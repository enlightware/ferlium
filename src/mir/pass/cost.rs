// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! What a body costs once lowered: the unit the inlining budgets are spent in.
//!
//! Counting operations overprices what inlining copies. Much of a small callee is frame
//! bookkeeping — its slots, the marks around its stack region, the field projections into them —
//! which the Wasm emitter turns into fixed frame offsets and folds into the accesses that use them,
//! emitting no instruction of its own. Everything else costs one unit. LLVM's `InlineCost` draws the
//! same line, treating static allocas, constant GEPs and lifetime markers as free.
//!
//! A failure path, which ends in a call that [diverges](Operation::diverges), runs at most once: a
//! callee is judged by its [`hot_cost`], but grows its caller by its whole [`cost`].

use crate::{
    graph,
    mir::{BlockId, Function, Operation, OperationKind, terminator::TerminatorKind},
    module::id::Id,
};

/// What one operation costs once lowered: nothing for frame bookkeeping, one unit otherwise.
pub(crate) fn operation_cost(operation: &Operation) -> usize {
    match operation.kind {
        // A statically sized slot is a frame offset; a witnessed one moves the stack frontier.
        OperationKind::Alloca { .. } => usize::from(!operation.operands.is_empty()),
        // A field at a static offset is folded into the address of the access using it; layout
        // evidence past the base and the index makes the offset dynamic.
        OperationKind::Subfield { .. } => usize::from(operation.operands.len() > 2),
        OperationKind::AllocaPlace { .. }
        | OperationKind::StackSave
        | OperationKind::StackRestore
        | OperationKind::Clear => 0,
        _ => 1,
    }
}

/// What a body costs once lowered, the sum of its operations' costs.
pub(crate) fn cost(func: &Function) -> usize {
    func.blocks().map(|block| block_cost(func, block)).sum()
}

/// Operations on the paths that can return, which is what inlining a body speeds up.
pub(crate) fn hot_cost(func: &Function) -> usize {
    let hot = hot_blocks(func);
    func.blocks()
        .filter(|block| hot[block.as_index()])
        .map(|block| block_cost(func, block))
        .sum()
}

/// A block's operations, including the call an `invoke` terminator makes.
fn block_cost(func: &Function, block: BlockId) -> usize {
    let block = func.block(block);
    let invoked = match &block.terminator().kind {
        TerminatorKind::Invoke { operation, .. } => Some(operation),
        _ => None,
    };
    block
        .operations()
        .iter()
        .chain(invoked)
        .map(operation_cost)
        .sum()
}

/// The blocks reachable from entry without passing through a cold one, by block index.
///
/// A block is cold when it contains a diverging call or all its successors are cold.
pub(crate) fn hot_blocks(func: &Function) -> Vec<bool> {
    let block_count = func.blocks().count();
    let successors: Vec<Vec<usize>> = func
        .blocks()
        .map(|block| {
            func.block(block)
                .terminator()
                .successors()
                .map(|target| target.as_index())
                .collect()
        })
        .collect();
    let diverges = |block: BlockId| {
        let block = func.block(block);
        block.operations().iter().any(Operation::diverges)
            || matches!(
                &block.terminator().kind,
                TerminatorKind::Invoke { operation, .. } if operation.diverges()
            )
    };
    // Successors first, so one sweep settles every block outside a loop.
    let mut cold: Vec<bool> = func.blocks().map(diverges).collect();
    let mut postorder = graph::reverse_postorder(&successors, func.entry().as_index());
    postorder.reverse();
    let mut changed = true;
    while changed {
        changed = false;
        for &block in &postorder {
            if !cold[block]
                && !successors[block].is_empty()
                && successors[block].iter().all(|&successor| cold[successor])
            {
                cold[block] = true;
                changed = true;
            }
        }
    }

    let mut hot = vec![false; block_count];
    let mut pending = vec![func.entry().as_index()];
    while let Some(block) = pending.pop() {
        if cold[block] || hot[block] {
            continue;
        }
        hot[block] = true;
        pending.extend(&successors[block]);
    }
    hot
}

#[cfg(test)]
mod tests {
    use super::cost;
    use crate::{
        CompilerSession, ExecutionTarget,
        compiler::MirOptimization,
        mir::pass::budget::INLINE_FUNCTION_GROWTH,
        module::{LocalFunctionId, ModuleId, Path, id::Id},
        std::STD_MODULE_ID,
    };

    const CORPUS: &[(&str, &str)] = include!("../../../tests/harness/mir_corpus.rs");

    /// Programs whose functions are larger and call more than the corpus's.
    const PROGRAMS: &[(&str, &str)] = &[
        (
            "many_accesses",
            "fn total(a: [int]) -> int { let mut t = 0; for i in 0..len(a) { t = t + a[i] + a[0] \
             + a[1] + a[2] + a[3] + a[4] + a[5] + a[6] + a[7] }; t }",
        ),
        (
            "bank_account",
            include_str!("../../../tests/modules/bank_account.fer"),
        ),
        ("csv", include_str!("../../../tests/modules/csv.fer")),
        (
            "data_text",
            include_str!("../../../tests/modules/data_text.fer"),
        ),
        (
            "image_adjust",
            include_str!("../../../tests/modules/image_adjust.fer"),
        ),
        (
            "iter_pipeline",
            include_str!("../../../tests/modules/iter_pipeline.fer"),
        ),
        ("linalg", include_str!("../../../tests/modules/linalg.fer")),
        (
            "quicksort",
            include_str!("../../../tests/modules/quicksort.fer"),
        ),
        ("sudoku", include_str!("../../../tests/modules/sudoku.fer")),
    ];

    /// Every function in `module` whose cost grew beyond `INLINE_FUNCTION_GROWTH`.
    fn overgrown(session: &CompilerSession, module: ModuleId) -> Vec<String> {
        let raw = session
            .mir_artifacts_for(module, MirOptimization::Disabled)
            .expect("raw artifacts were built");
        let optimized = session
            .mir_artifacts_for(module, MirOptimization::Enabled)
            .expect("optimized artifacts were built");
        raw.bodies()
            .iter()
            .enumerate()
            .filter_map(|(index, before)| {
                let after = optimized.get(LocalFunctionId::from_index(index))?;
                let (before, after_cost) = (cost(before.as_ref()?), cost(after));
                (after_cost > before + INLINE_FUNCTION_GROWTH)
                    .then(|| format!("`{}` grew from {before} to {after_cost}", after.name))
            })
            .collect()
    }

    /// Inlining and constructive folds may add operations, but no function's cost grows by more
    /// than `INLINE_FUNCTION_GROWTH` over the whole of optimization, standard library included.
    #[test]
    fn optimization_grows_no_function_beyond_its_budget() {
        for (index, (name, src)) in CORPUS.iter().chain(PROGRAMS).enumerate() {
            let mut session = CompilerSession::new();
            session.set_mir_optimization(MirOptimization::Enabled);
            // `image_adjust` uses named subscripts.
            session.set_allow_experimental(true);
            let module = session
                .compile_for(ExecutionTarget::Mir, src, name, Path::single_str(name))
                .unwrap_or_else(|_| panic!("`{name}` compiles"))
                .module_id;
            session.prepare_execution_target(ExecutionTarget::Mir, module);
            let mut grown = overgrown(&session, module);
            // Every session builds the same standard library, so one check covers it.
            if index == 0 {
                grown.extend(overgrown(&session, STD_MODULE_ID));
            }
            assert!(grown.is_empty(), "in `{name}`: {grown:?}");
        }
    }
}
