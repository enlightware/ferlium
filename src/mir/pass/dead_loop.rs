// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Removal of loops that terminate and have no effect.
//!
//! Such a loop, once left, has only changed storage nothing reads any more, so its preheader may
//! jump directly to where it exits. What makes that sound is that it terminates: deleting a loop
//! that runs forever would make a non-terminating execution return, which optimization must never
//! do (see `runtime-sandboxing.md`).
//!
//! Termination comes from the sandbox contract rather than from a proof. Untrusted MIR crosses a
//! fuel check on every cycle, so a loop without one comes from trusted code, such as std's, which
//! must terminate. A loop with a fuel check is kept, even when it would also be trivially finite.
//!
//! A loop has no effect when every operation in it is one of:
//! - a computation without writes, such as a `load`, an address or a comparison;
//! - a call [known to return without effects](super::dce::is_proven_pure_call);
//! - a write to a *private* local: a `TrivialCopy` `alloca` that nothing outside the loop reads,
//!   through any place derived from it;
//! - a local allocation, or a stack marker.
//!
//! Its blocks must branch only among themselves and to a single exit, and none of its registers
//! may be used outside it. A `return`, a fallible operation or a `yield` inside it rejects it.

use rustc_hash::{FxHashMap, FxHashSet};

use super::{
    dataflow,
    dce::is_proven_pure_call,
    known_callee::KnownCallees,
    loops::{NaturalLoop, cfg, natural_loops},
};
use crate::{
    mir::{
        BlockId, Function, Operation, OperationKind, Value, ValueId,
        dominance::Dominance,
        edit::FunctionEdit,
        terminator::{Terminator, TerminatorKind},
    },
    module::{FunctionId, ModuleEnv, id::Id},
    types::type_properties::concrete_type_is_trivial_copy,
};

/// Removes loops without a fuel check whose execution has no effect once they are left.
pub(crate) fn remove_dead_loops(
    func: &Function,
    env: ModuleEnv<'_>,
    known: &KnownCallees,
    original_of: &dyn Fn(FunctionId) -> Option<FunctionId>,
    will_return: &dyn Fn(FunctionId) -> bool,
) -> Option<Function> {
    // A deleted loop may have been the last to read what an earlier loop computes, so scan again
    // until nothing goes.
    let mut current = None;
    while let Some(next) = remove_dead_loops_once(
        current.as_ref().unwrap_or(func),
        env,
        known,
        original_of,
        will_return,
    ) {
        current = Some(next);
    }
    current
}

fn remove_dead_loops_once(
    func: &Function,
    env: ModuleEnv<'_>,
    known: &KnownCallees,
    original_of: &dyn Fn(FunctionId) -> Option<FunctionId>,
    will_return: &dyn Fn(FunctionId) -> bool,
) -> Option<Function> {
    // Every directed cycle has an edge that does not increase block order, which rejects acyclic
    // bodies before building the CFG and dominance.
    let may_have_loop = func.blocks().any(|block| {
        func.block(block)
            .terminator()
            .successors()
            .any(|successor| successor.as_index() <= block.as_index())
    });
    if !may_have_loop {
        return None;
    }
    let (successors, predecessors) = cfg(func);
    let dominance = Dominance::of(&successors, func.entry().as_index());
    let mut loops = natural_loops(func, &successors, &predecessors, &dominance);
    if loops.is_empty() {
        return None;
    }
    // Outermost first: deleting a loop deletes the loops nested in it.
    loops.sort_by_key(|natural| std::cmp::Reverse(natural.blocks.len()));

    let census = Census::of(func, env);
    let mut trivial_copy = FxHashMap::default();
    let mut is_pure_call = |operation: &Operation| {
        is_proven_pure_call(
            operation,
            env,
            known,
            original_of,
            will_return,
            &mut trivial_copy,
        )
    };
    let mut deleted = FxHashSet::default();
    let mut exits = Vec::new();
    for natural in &loops {
        if deleted.contains(&natural.header) {
            continue;
        }
        let Some(exit) = dead_loop_exit(func, natural, &census, &mut is_pure_call) else {
            continue;
        };
        deleted.extend(natural.blocks.iter().copied());
        exits.push((natural.preheader, exit));
    }
    if exits.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for (preheader, exit) in exits {
        let terminator = &mut edit.block_mut(preheader).terminator;
        *terminator = Terminator::goto(terminator.span, exit);
    }
    edit.remove_unreachable_blocks();
    edit.merge_blocks_into_predecessors();
    edit.prune_constants();
    Some(edit.finish_unverified())
}

/// What the loop checks need to know about the whole function.
struct Census {
    /// The blocks using each register, as an operation or a terminator operand.
    uses: FxHashMap<ValueId, Vec<BlockId>>,
    /// For each place register derived from a `TrivialCopy` `alloca`, that `alloca`.
    roots: FxHashMap<ValueId, ValueId>,
    /// The blocks observing each such `alloca`: using it, or a place derived from it, other than
    /// by writing into it.
    observers: FxHashMap<ValueId, Vec<BlockId>>,
}

impl Census {
    fn of(func: &Function, env: ModuleEnv<'_>) -> Self {
        let mut census = Self {
            uses: FxHashMap::default(),
            roots: FxHashMap::default(),
            observers: FxHashMap::default(),
        };
        // A definition precedes its uses in block order, so one pass sees every base first.
        for block in func.blocks() {
            for operation in func.block(block).operations() {
                let Some(result) = operation.result_id() else {
                    continue;
                };
                match &operation.kind {
                    OperationKind::Alloca { ty } if concrete_type_is_trivial_copy(*ty, &env) => {
                        census.roots.insert(result, result);
                    }
                    OperationKind::Subfield { .. }
                    | OperationKind::AddressOffset { .. }
                    | OperationKind::AddressOffsetPlace { .. } => {
                        if let Some(Value::Register(base)) = operation.operands.first()
                            && let Some(&root) = census.roots.get(base)
                        {
                            census.roots.insert(result, root);
                        }
                    }
                    _ => {}
                }
            }
        }
        for block in func.blocks() {
            let basic = func.block(block);
            for operation in basic.operations() {
                let writes = written_operands(operation);
                for (position, operand) in operation.operands.iter().enumerate() {
                    let Value::Register(id) = operand else {
                        continue;
                    };
                    census.uses.entry(*id).or_default().push(block);
                    let Some(&root) = census.roots.get(id) else {
                        continue;
                    };
                    let derives = position == 0
                        && matches!(
                            operation.kind,
                            OperationKind::Subfield { .. }
                                | OperationKind::AddressOffset { .. }
                                | OperationKind::AddressOffsetPlace { .. }
                        );
                    // A move reads its source before leaving it absent.
                    let only_written = writes.contains(&position)
                        && !(position == 0
                            && matches!(
                                operation.kind,
                                OperationKind::Move | OperationKind::MoveBytes { .. }
                            ));
                    if !derives && !only_written {
                        census.observers.entry(root).or_default().push(block);
                    }
                }
            }
            for operand in basic.terminator().operands() {
                if let Value::Register(id) = operand {
                    census.uses.entry(*id).or_default().push(block);
                    if let Some(&root) = census.roots.get(id) {
                        census.observers.entry(root).or_default().push(block);
                    }
                }
            }
        }
        census
    }

    /// Whether `place` is local storage that nothing outside `blocks` observes.
    fn is_private(&self, place: &Value, blocks: &FxHashSet<BlockId>) -> bool {
        let Value::Register(id) = place else {
            return false;
        };
        let Some(root) = self.roots.get(id) else {
            return false;
        };
        self.observers
            .get(root)
            .is_none_or(|observers| observers.iter().all(|block| blocks.contains(block)))
    }
}

/// The operand positions an operation writes storage through.
fn written_operands(operation: &Operation) -> Vec<usize> {
    match &operation.kind {
        OperationKind::Store | OperationKind::Memcpy => vec![1],
        OperationKind::Move | OperationKind::MoveBytes { .. } => vec![0, 1],
        OperationKind::Clear => vec![0],
        OperationKind::Call { .. } => dataflow::call_result_operand_index(operation)
            .into_iter()
            .collect(),
        _ => Vec::new(),
    }
}

/// The block `natural` exits to, if it may be deleted.
fn dead_loop_exit(
    func: &Function,
    natural: &NaturalLoop,
    census: &Census,
    is_pure_call: &mut dyn FnMut(&Operation) -> bool,
) -> Option<BlockId> {
    let blocks = &natural.blocks;
    let mut exit = None;
    for &block in blocks {
        let basic = func.block(block);
        if !matches!(
            basic.terminator().kind,
            TerminatorKind::Goto { .. }
                | TerminatorKind::CondBr { .. }
                | TerminatorKind::SwitchVariant { .. }
        ) {
            return None;
        }
        for successor in basic.terminator().successors() {
            if blocks.contains(&successor) {
                continue;
            }
            if exit.is_some_and(|exit| exit != successor) {
                return None;
            }
            exit = Some(successor);
        }
        for operation in basic.operations() {
            if !has_no_effect(operation, blocks, census, is_pure_call) {
                return None;
            }
            if let Some(result) = operation.result_id()
                && census
                    .uses
                    .get(&result)
                    .is_some_and(|uses| uses.iter().any(|block| !blocks.contains(block)))
            {
                return None;
            }
        }
    }
    // Jumping from the preheader to itself would loop where the loop exited.
    exit.filter(|&exit| exit != natural.preheader)
}

/// Whether skipping `operation`, in a loop made of `blocks`, changes nothing once the loop is left.
fn has_no_effect(
    operation: &Operation,
    blocks: &FxHashSet<BlockId>,
    census: &Census,
    is_pure_call: &mut dyn FnMut(&Operation) -> bool,
) -> bool {
    let writes_private = || {
        written_operands(operation)
            .into_iter()
            .all(|position| census.is_private(&operation.operands[position], blocks))
    };
    match &operation.kind {
        OperationKind::Alloca { .. }
        | OperationKind::AllocaPlace { .. }
        | OperationKind::Load
        | OperationKind::CompareEqual
        | OperationKind::Subfield { .. }
        | OperationKind::AddressOffset { .. }
        | OperationKind::AddressOffsetPlace { .. }
        | OperationKind::ExtractTag
        | OperationKind::ExtractPayloadIndirection
        | OperationKind::IsInitialized
        | OperationKind::StackSave
        // A restore only frees storage, which nothing may use after the loop since the loop may
        // have freed it. Skipping it keeps that storage until a later restore or the return.
        | OperationKind::StackRestore => true,
        OperationKind::Store
        | OperationKind::Memcpy
        | OperationKind::Move
        | OperationKind::MoveBytes { .. }
        | OperationKind::Clear => writes_private(),
        OperationKind::Call { .. } => is_pure_call(operation) && writes_private(),
        // A fuel check marks a loop that may not terminate. Anything else may have an effect.
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::remove_dead_loops;
    use crate::{
        CompilerSession, MirOptimization,
        mir::Function,
        module::{LocalFunctionId, ModuleEnv, Path, id::Id},
    };

    /// Two trusted loops, the second counting up to what the first computes.
    const DEPENDENT_LOOPS: &str = "#[no_fuel_check]
        pub fn f(n: int) {
            let mut i = 0;
            loop {
                if i >= n {
                    break;
                };
                i += 1;
            };
            let mut j = 0;
            loop {
                if j >= i {
                    break;
                };
                j += 1;
            };
        }";

    fn has_loop(body: &Function) -> bool {
        body.blocks().any(|block| {
            body.block(block)
                .terminator()
                .successors()
                .any(|successor| successor.as_index() <= block.as_index())
        })
    }

    /// Whether an optimized physical body of the module `source` defines still loops.
    fn loops_after_optimization(source: &str) -> bool {
        let mut session = CompilerSession::new();
        session.set_allow_unsafe(true);
        session.set_mir_optimization(MirOptimization::Enabled);
        session.set_physical_mir_optimization(MirOptimization::Enabled);
        let module = session
            .compile(source, "dead_loop", Path::single_str("dead_loop"))
            .unwrap()
            .module_id;
        let program = session.prepare_physical_program(module).unwrap();
        let artifacts = program.module(module).unwrap();
        (0..artifacts.entry_count())
            .filter_map(|index| artifacts.get(LocalFunctionId::from_index(index)))
            .any(has_loop)
    }

    #[test]
    fn a_trusted_loop_only_counting_is_removed() {
        assert!(!loops_after_optimization(
            "#[no_fuel_check]
             pub fn f(n: int) {
                 let mut i = 0;
                 loop {
                     if i >= n {
                         return ();
                     };
                     i += 1;
                 }
             }",
        ));
    }

    /// The second loop reads what the first computes, so the first goes only once the second has.
    /// The pass must find both alone: the driver reruns it only when another pass changes the body.
    #[test]
    fn one_run_removes_a_loop_read_only_by_a_dead_loop() {
        let mut session = CompilerSession::new();
        session.set_allow_unsafe(true);
        session.set_mir_optimization(MirOptimization::Enabled);
        session.set_physical_mir_optimization(MirOptimization::Disabled);
        let module = session
            .compile(DEPENDENT_LOOPS, "dead_loop", Path::single_str("dead_loop"))
            .unwrap()
            .module_id;
        let program = session.prepare_physical_program(module).unwrap();
        let artifacts = program.module(module).unwrap();
        let env = ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules());
        let looping: Vec<_> = (0..artifacts.entry_count())
            .filter_map(|index| artifacts.get(LocalFunctionId::from_index(index)))
            .filter(|body| has_loop(body))
            .collect();
        assert_eq!(looping.len(), 1);
        let removed =
            remove_dead_loops(looping[0], env, session.known_callees(), &Some, &|_| false).unwrap();
        assert!(
            !has_loop(&removed),
            "{}",
            removed.render_with_source_map(&env).text
        );
    }

    /// Without the trusted contract, the loop may run forever, which must stay so.
    #[test]
    fn a_loop_with_a_fuel_check_is_kept() {
        assert!(loops_after_optimization(
            "pub fn f(n: int) {
                 let mut i = 0;
                 loop {
                     if i >= n {
                         return ();
                     };
                     i += 1;
                 }
             }",
        ));
    }

    #[test]
    fn a_loop_computing_what_follows_it_is_kept() {
        assert!(loops_after_optimization(
            "#[no_fuel_check]
             pub fn f(n: int) -> int {
                 let mut i = 0;
                 let mut sum = 0;
                 loop {
                     if i >= n {
                         return sum;
                     };
                     sum += i;
                     i += 1;
                 }
             }",
        ));
    }

    #[test]
    fn a_loop_writing_through_a_reference_is_kept() {
        assert!(loops_after_optimization(
            "#[no_fuel_check]
             pub fn f(n: &mut int) {
                 loop {
                     if n <= 0 {
                         return ();
                     };
                     n -= 1;
                 }
             }",
        ));
    }
}
