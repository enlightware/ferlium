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

use super::budget::{INLINE_FUNCTION_GROWTH, INLINE_LOOP_GROWTH};
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

/// Whether [`hot_cost`] exceeds `limit`, without finding the hot blocks when the whole body is
/// within it, which bounds its hot part.
pub(crate) fn hot_cost_exceeds(func: &Function, limit: usize) -> bool {
    cost(func) > limit && hot_cost(func) > limit
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

/// What a function cost before optimization started, which its growth budgets are measured from.
///
/// Measured once, before any round: against the current size, each round would grant the budgets
/// afresh, and they would only bound growth per round.
#[derive(Clone, Copy, Debug)]
pub(crate) struct GrowthBase {
    total: usize,
    outside_loops: usize,
}

impl GrowthBase {
    pub(crate) fn of(func: &Function) -> Self {
        let cyclic = cyclic_blocks(func);
        Self {
            total: cost(func),
            outside_loops: cost_outside_loops(func, &cyclic),
        }
    }
}

/// A function's cost as one pass plans rewrites, reserved against its growth budgets.
///
/// Two budgets, because a site in a loop runs once per iteration: the whole function may grow by
/// [`INLINE_LOOP_GROWTH`], and its code outside loops by [`INLINE_FUNCTION_GROWTH`]. They are
/// measured apart, so what loops take cannot starve the code around them: charging all growth to
/// one total would let a loop that inlines a large body in the first round refuse the sites before
/// it, while the same growth reached through smaller bodies over several rounds would not. A
/// function without loops grows by [`INLINE_FUNCTION_GROWTH`].
pub(crate) struct Growth {
    base: GrowthBase,
    cyclic: Vec<bool>,
    total: usize,
    outside_loops: usize,
}

impl Growth {
    pub(crate) fn new(base: GrowthBase, func: &Function) -> Self {
        let cyclic = cyclic_blocks(func);
        Self {
            base,
            total: cost(func),
            outside_loops: cost_outside_loops(func, &cyclic),
            cyclic,
        }
    }

    /// A function of `total` cost, `outside_loops` of it outside loops, that has not grown yet.
    #[cfg(test)]
    fn unchanged(total: usize, outside_loops: usize, cyclic: Vec<bool>) -> Self {
        Self {
            base: GrowthBase {
                total,
                outside_loops,
            },
            cyclic,
            total,
            outside_loops,
        }
    }

    /// Whether `block` lies in a loop.
    pub(crate) fn in_loop(&self, block: BlockId) -> bool {
        self.cyclic[block.as_index()]
    }

    /// Reserves replacing operations costing `removed` in `block` by ones costing `added`, unless
    /// that grows the function beyond a budget.
    ///
    /// A rewrite that does not grow the function is always accepted: the function is within its
    /// budgets already, and a rewrite exposed by growth elsewhere must not be refused for it.
    pub(crate) fn reserve(&mut self, block: BlockId, removed: usize, added: usize) -> bool {
        let in_loop = self.in_loop(block);
        let total = self.total.saturating_sub(removed).saturating_add(added);
        let outside_loops = if in_loop {
            self.outside_loops
        } else {
            self.outside_loops
                .saturating_sub(removed)
                .saturating_add(added)
        };
        if added > removed
            && (total > self.base.total + INLINE_LOOP_GROWTH
                || outside_loops > self.base.outside_loops + INLINE_FUNCTION_GROWTH)
        {
            return false;
        }
        self.total = total;
        self.outside_loops = outside_loops;
        true
    }
}

/// The cost of the blocks outside every loop.
fn cost_outside_loops(func: &Function, cyclic: &[bool]) -> usize {
    func.blocks()
        .filter(|block| !cyclic[block.as_index()])
        .map(|block| block_cost(func, block))
        .sum()
}

/// The blocks that lie on a cycle of the control-flow graph, by block index: a call there runs once
/// per iteration.
pub(crate) fn cyclic_blocks(func: &Function) -> Vec<bool> {
    struct Block(Vec<usize>);
    impl graph::Node for Block {
        type Index = usize;
        fn neighbors(&self) -> impl Iterator<Item = usize> {
            self.0.iter().copied()
        }
    }
    let blocks: Vec<Block> = func
        .blocks()
        .map(|block| {
            Block(
                func.block(block)
                    .terminator()
                    .successors()
                    .map(|target| target.as_index())
                    .collect(),
            )
        })
        .collect();
    let mut cyclic = vec![false; blocks.len()];
    for component in graph::find_strongly_connected_components(&blocks) {
        let [single] = component.as_slice() else {
            for &block in &component {
                cyclic[block] = true;
            }
            continue;
        };
        cyclic[*single] = blocks[*single].0.contains(single);
    }
    cyclic
}

#[cfg(test)]
mod tests {
    use super::{Growth, cost};
    use crate::{
        CompilerSession, ExecutionTarget,
        compiler::MirOptimization,
        mir::{
            BlockId,
            pass::budget::{INLINE_FUNCTION_GROWTH, INLINE_LOOP_GROWTH},
        },
        module::{LocalFunctionId, ModuleId, Path, id::Id},
        std::STD_MODULE_ID,
    };

    const OUTSIDE: BlockId = BlockId::new(0);
    const IN_LOOP: BlockId = BlockId::new(1);

    #[test]
    fn code_outside_loops_grows_by_the_function_growth_budget() {
        let mut growth = Growth::unchanged(10, 10, vec![false]);
        for _ in 0..64 {
            assert!(growth.reserve(OUTSIDE, 1, 3));
        }
        assert!(!growth.reserve(OUTSIDE, 1, 3));
    }

    /// What a loop takes cannot starve the code around it, whichever round inlines it.
    #[test]
    fn growth_in_loops_leaves_the_code_outside_them_its_budget() {
        let mut growth = Growth::unchanged(20, 10, vec![false, true]);
        assert!(growth.reserve(IN_LOOP, 1, INLINE_LOOP_GROWTH - INLINE_FUNCTION_GROWTH + 1));
        assert!(growth.reserve(OUTSIDE, 1, INLINE_FUNCTION_GROWTH + 1));
        assert!(!growth.reserve(OUTSIDE, 1, 2));
        // The whole function is at its budget now.
        assert!(!growth.reserve(IN_LOOP, 1, 2));
    }

    /// A rewrite exposed by growth elsewhere must go through when it does not grow the function.
    #[test]
    fn a_rewrite_that_does_not_grow_is_accepted_beyond_the_budgets() {
        let mut growth = Growth::unchanged(10, 10, vec![false, true]);
        assert!(growth.reserve(IN_LOOP, 1, INLINE_LOOP_GROWTH + 1));
        assert!(!growth.reserve(OUTSIDE, 1, 2));
        assert!(growth.reserve(OUTSIDE, 1, 1));
        assert!(growth.reserve(IN_LOOP, 2, 1));
    }

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

    /// Every function in `module` whose cost grew beyond `INLINE_LOOP_GROWTH`, the larger budget.
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
                (after_cost > before + INLINE_LOOP_GROWTH)
                    .then(|| format!("`{}` grew from {before} to {after_cost}", after.name))
            })
            .collect()
    }

    /// Inlining and constructive folds may add operations, but no function's cost grows by more
    /// than `INLINE_LOOP_GROWTH` over the whole of optimization, standard library included.
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
