// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Stack-region facts and removal of markers that record a frontier already recorded.
//!
//! A stack marker is the interpreter's `environment.len()` at the point it was taken, and
//! `stack_restore` pops back down to it. Only an `alloca` pushes. Two facts follow, and they need
//! no ownership reasoning at all:
//!
//! - a `stack_save` taken where the frontier is *already* held by a live marker records the same
//!   integer, so the two markers are interchangeable and the second save is redundant;
//! - a `stack_restore` to a frontier the interpreter is already at pops nothing.
//!
//! Nesting is what produces them: inlining brackets every spliced body, and a body spliced
//! immediately inside another's bracket takes its mark at the same frontier.
//!
//! **This removes no lifetime information.** A bracket that reclaims real storage is the MIR
//! spelling of a live range ending, and a backend's stack-slot allocator needs it to prove two
//! slots may share a frame offset — [`dce::remove_empty_local_stack_regions`] is careful for the
//! same reason, and `dce`'s own tests pin it. What goes here is only the *duplicate* of a mark that
//! another marker already holds, and the no-op restore of a frontier already current. Neither tells
//! a backend anything the surviving marker does not. Peak cell use is unchanged, instruction for
//! instruction, which is what separates this from deleting a bracket that does work.
//!
//! The analysis is a forward fixpoint whose state is the set of markers known equal to the current
//! frontier, intersected at joins. Its caller supplies what changes that frontier: the MIR cleanup
//! pass uses [`dce`]'s storage predicate, while a backend may model its own storage representation.
//! A separate allocation-preservation query tracks which markers retain one local allocation,
//! allowing ownership rewrites to cross inner restores without deleting lifetime boundaries.

use std::{cmp::Ordering, collections::VecDeque};

use rustc_hash::{FxHashMap, FxHashSet};

use super::{
    dce::may_leave_frame_storage,
    site::{OperationIndex, OperationSite},
};
use crate::{
    mir::{
        self, BlockId, Function, Operation, OperationKind, edit::FunctionEdit, role::ValueRoles,
        terminator::TerminatorKind, value::ValueId,
    },
    module::id::Id,
};

/// The markers known to equal the current allocation frontier, ordered by index.
///
/// Empty means "unknown", the bottom of the lattice, so intersection at a join is the meet and the
/// fixpoint descends to it. More than one marker because a restore re-establishes every marker its
/// own save was taken alongside.
///
/// A sorted `Vec` rather than a set: these hold one to a handful of markers, and the fixpoint
/// clones a state per block per sweep, where a hash set's allocation dominates the work it saves.
type Frontier = Vec<ValueId>;

fn holds(frontier: &Frontier, marker: ValueId) -> bool {
    frontier
        .binary_search_by_key(&marker.as_index(), |held| held.as_index())
        .is_ok()
}

fn record(frontier: &mut Frontier, marker: ValueId) {
    if let Err(position) = frontier.binary_search_by_key(&marker.as_index(), |held| held.as_index())
    {
        frontier.insert(position, marker);
    }
}

/// The meet: markers both paths agree are at the frontier. Linear, both sides being sorted.
fn intersect(left: &Frontier, right: &Frontier) -> Frontier {
    let mut result = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < left.len() && j < right.len() {
        let (a, b) = (left[i].as_index(), right[j].as_index());
        match a.cmp(&b) {
            Ordering::Equal => {
                result.push(left[i]);
                i += 1;
                j += 1;
            }
            Ordering::Less => i += 1,
            Ordering::Greater => j += 1,
        }
    }
    result
}

/// Canonicalizes redundant stack markers and drops restores that reclaim nothing, returning a
/// rewritten function if anything changed.
pub(crate) fn remove_redundant_stack_markers(func: &Function) -> Option<Function> {
    // A lone save-and-restore pair has nothing to be redundant against: the frontier is unknown at
    // the save, and the restore is the first to reach its own mark. Most bodies stop here without
    // the fixpoint running at all.
    let (saves, restores) = func
        .blocks()
        .flat_map(|block| func.block(block).operations())
        .fold(
            (0usize, 0usize),
            |(saves, restores), operation| match operation.kind {
                OperationKind::StackSave => (saves + 1, restores),
                OperationKind::StackRestore => (saves, restores + 1),
                _ => (saves, restores),
            },
        );
    if saves < 2 && restores < 2 {
        return None;
    }

    let roles = ValueRoles::derive(func);
    let invalidates = |operation: &Operation| may_leave_frame_storage(operation, func, &roles);
    // In the physical interpreter, yielding transfers control without changing the frame-storage
    // frontier, but a backend retaining suspension frames resumes on a frontier of its own, and
    // cannot restore a mark taken before the suspension. MIR serves both, so no marker is known
    // equal across a yield.
    let entry_states = analyze(func, &invalidates, &|kind| {
        matches!(kind, TerminatorKind::Yield { .. })
    });

    // A redundant save's marker is replaced by one already holding the same frontier. The
    // substitution is justified where it is *decided* — the two markers are equal integers there —
    // and both are immutable afterwards, so it holds at every use. Dominance holds too: a marker in
    // the state arrived on every path to this point, so its definition dominates this one's.
    let mut substitution: FxHashMap<ValueId, ValueId> = FxHashMap::default();
    let mut dead = FxHashMap::<BlockId, FxHashSet<OperationIndex>>::default();
    for block in func.blocks() {
        let Some(state) = entry_states[block.as_index()].as_ref() else {
            continue;
        };
        let mut state = state.clone();
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            let index = OperationIndex::from_index(index);
            match &operation.kind {
                OperationKind::StackSave => {
                    if let (Some(marker), Some(held)) =
                        (operation.result_id(), representative(&state))
                    {
                        substitution.insert(marker, resolve(&substitution, held));
                        dead.entry(block).or_default().insert(index);
                    }
                }
                OperationKind::StackRestore => {
                    // Substituted markers are equal integers, so a marker this sweep merged into
                    // another's is held whenever that one is.
                    if let Some(mir::Value::Register(marker)) = operation.operands.first()
                        && (holds(&state, *marker)
                            || state.iter().any(|held| {
                                resolve(&substitution, *held) == resolve(&substitution, *marker)
                            }))
                    {
                        dead.entry(block).or_default().insert(index);
                    }
                }
                _ => {}
            }
            step(operation, &invalidates, &mut state);
        }
    }
    if dead.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    if !substitution.is_empty() {
        edit.visit_operands_mut(|operand| {
            if let mir::Value::Register(id) = operand
                && let Some(replacement) = substitution.get(id)
            {
                *id = *replacement;
            }
        });
    }
    for (block, indices) in &dead {
        let mut index = 0;
        edit.block_mut(*block).operations.retain(|_| {
            let keep = !indices.contains(&OperationIndex::from_index(index));
            index += 1;
            keep
        });
    }
    Some(edit.finish_unverified())
}

/// Finds stack markers whose restores never change the allocation frontier under a target's
/// storage model.
///
/// `changes_frontier` identifies operations which may change the target's current frontier.
/// `terminator_changes_frontier` does the same for transfers, such as suspension into another
/// caller.
/// A marker is returned only when it is known to remain at the current frontier on every reachable
/// restore, so a backend may omit both the save and all restores naming it.
// Used by backends whose storage frontier differs from physical MIR's.
#[cfg_attr(all(not(target_arch = "wasm32"), not(test)), allow(dead_code))]
pub(crate) fn no_op_stack_markers(
    func: &Function,
    changes_frontier: impl Fn(&Operation) -> bool,
    terminator_changes_frontier: impl Fn(&TerminatorKind) -> bool,
) -> FxHashSet<ValueId> {
    let mut no_op = func
        .blocks()
        .flat_map(|block| func.block(block).operations())
        .filter_map(|operation| {
            matches!(operation.kind, OperationKind::StackSave)
                .then(|| operation.result_id())
                .flatten()
        })
        .collect::<FxHashSet<_>>();
    if no_op.is_empty() {
        return no_op;
    }

    let entry_states = analyze(func, &changes_frontier, &terminator_changes_frontier);
    for block in func.blocks() {
        let Some(mut state) = entry_states[block.as_index()].clone() else {
            continue;
        };
        let basic_block = func.block(block);
        for operation in basic_block.operations() {
            reject_changing_restore(operation, &state, &mut no_op);
            step(operation, &changes_frontier, &mut state);
        }
    }
    no_op
}

fn reject_changing_restore(
    operation: &Operation,
    state: &Frontier,
    no_op: &mut FxHashSet<ValueId>,
) {
    if matches!(operation.kind, OperationKind::StackRestore)
        && let Some(mir::Value::Register(marker)) = operation.operands.first()
        && !holds(state, *marker)
    {
        no_op.remove(marker);
    }
}

/// The marker a redundant save defers to: the lowest live one, which the ordering makes the first.
fn representative(state: &Frontier) -> Option<ValueId> {
    state.first().copied()
}

/// Follows a substitution to its final target. Chains form when three saves nest.
fn resolve(substitution: &FxHashMap<ValueId, ValueId>, marker: ValueId) -> ValueId {
    let mut current = marker;
    while let Some(next) = substitution.get(&current) {
        if *next == current {
            break;
        }
        current = *next;
    }
    current
}

/// The frontier state on entry to each reachable block.
fn analyze(
    func: &Function,
    changes_frontier: &impl Fn(&Operation) -> bool,
    terminator_changes_frontier: &impl Fn(&TerminatorKind) -> bool,
) -> Vec<Option<Frontier>> {
    let mut entry_states = vec![None; func.blocks().count()];
    entry_states[func.entry().as_index()] = Some(Frontier::default());
    let mut pending = VecDeque::from([func.entry()]);
    let mut queued = vec![false; entry_states.len()];
    queued[func.entry().as_index()] = true;

    // A state is initialized by its first reached predecessor and can only shrink afterwards.
    // Revisit just the successors of a changed block rather than sweeping the whole function.
    while let Some(block) = pending.pop_front() {
        queued[block.as_index()] = false;
        let mut state = entry_states[block.as_index()]
            .clone()
            .expect("only reached blocks enter the frontier worklist");
        let basic_block = func.block(block);
        for operation in basic_block.operations() {
            step(operation, changes_frontier, &mut state);
        }
        if let TerminatorKind::Invoke { operation, .. } = &basic_block.terminator().kind {
            step(operation, changes_frontier, &mut state);
        }
        if terminator_changes_frontier(&basic_block.terminator().kind) {
            state.clear();
        }
        for successor in basic_block.terminator().successors() {
            let slot = &mut entry_states[successor.as_index()];
            let updated = slot
                .as_ref()
                .map_or_else(|| state.clone(), |existing| intersect(existing, &state));
            if slot.as_ref() != Some(&updated) {
                *slot = Some(updated);
                if !queued[successor.as_index()] {
                    queued[successor.as_index()] = true;
                    pending.push_back(successor);
                }
            }
        }
    }
    entry_states
}

/// Advances the frontier state across one operation.
fn step(
    operation: &Operation,
    changes_frontier: &impl Fn(&Operation) -> bool,
    state: &mut Frontier,
) {
    match &operation.kind {
        OperationKind::StackSave => {
            if let Some(marker) = operation.result_id() {
                record(state, marker);
            }
        }
        OperationKind::StackRestore => {
            // Restoring to a frontier already current changes nothing, so the whole set survives.
            // Otherwise the frontier becomes this marker's, and only it is known to hold it.
            if let Some(mir::Value::Register(marker)) = operation.operands.first()
                && !holds(state, *marker)
            {
                state.clear();
                state.push(*marker);
            }
        }
        _ => {
            if changes_frontier(operation) {
                state.clear();
            }
        }
    }
}

/// Whether one local allocation is live, and which markers saved while it was protect it.
#[derive(Clone, Default, PartialEq, Eq)]
struct AllocationState {
    live: bool,
    markers: Frontier,
}

fn step_allocation(operation: &Operation, allocation: ValueId, state: &mut AllocationState) {
    match operation.kind {
        OperationKind::Alloca { .. } if operation.result_id() == Some(allocation) => {
            state.live = true;
            state.markers.clear();
        }
        OperationKind::StackSave => {
            let marker = operation.result_id().unwrap();
            if state.live {
                record(&mut state.markers, marker);
            } else {
                state.markers.retain(|&saved| saved != marker);
            }
        }
        OperationKind::StackRestore => {
            state.live &= matches!(operation.operands.first(), Some(mir::Value::Register(marker))
                if holds(&state.markers, *marker));
            if !state.live {
                state.markers.clear();
            }
        }
        _ => {}
    }
}

/// The allocation's state on entry to every block, as a must-analysis: live only if live on every
/// path. `None` for a block no path reaches.
fn allocation_states(func: &Function, allocation: ValueId) -> Vec<Option<AllocationState>> {
    let mut inputs = vec![None; func.blocks().count()];
    inputs[func.entry().as_index()] = Some(AllocationState::default());
    let mut pending = VecDeque::from([func.entry()]);
    let mut queued = vec![false; inputs.len()];
    queued[func.entry().as_index()] = true;
    while let Some(block) = pending.pop_front() {
        queued[block.as_index()] = false;
        let mut state = inputs[block.as_index()].clone().unwrap();
        let basic = func.block(block);
        for operation in basic.operations() {
            step_allocation(operation, allocation, &mut state);
        }
        if let TerminatorKind::Invoke { operation, .. } = &basic.terminator().kind {
            step_allocation(operation, allocation, &mut state);
        }
        if matches!(basic.terminator().kind, TerminatorKind::Yield { .. }) {
            state = AllocationState::default();
        }
        for successor in basic.terminator().successors() {
            let slot = &mut inputs[successor.as_index()];
            let updated = slot.as_ref().map_or_else(
                || state.clone(),
                |existing| AllocationState {
                    live: existing.live && state.live,
                    markers: intersect(&existing.markers, &state.markers),
                },
            );
            if slot.as_ref() != Some(&updated) {
                *slot = Some(updated);
                if !queued[successor.as_index()] {
                    queued[successor.as_index()] = true;
                    pending.push_back(successor);
                }
            }
        }
    }
    inputs
}

/// Restores proved to preserve the current incarnation of one local allocation on every path.
///
/// A marker protects the allocation only if saved while it is live. Reexecuting the allocation
/// invalidates all older snapshots: static allocation identities alone cannot distinguish loop
/// iterations. Intersecting facts at joins keeps this a small must-analysis, without the
/// verifier's relational allocation-frontier alternatives. Unknown histories lose the proof.
pub(crate) fn restores_preserving_alloca(
    func: &Function,
    allocation: ValueId,
) -> FxHashSet<OperationSite> {
    let inputs = allocation_states(func, allocation);
    let mut preserving = FxHashSet::default();
    for block in func.blocks() {
        let Some(mut state) = inputs[block.as_index()].clone() else {
            continue;
        };
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            if state.live
                && matches!(operation.kind, OperationKind::StackRestore)
                && matches!(operation.operands.first(), Some(mir::Value::Register(marker))
                    if holds(&state.markers, *marker))
            {
                preserving.insert(OperationSite {
                    block,
                    index: OperationIndex::from_index(index),
                });
            }
            step_allocation(operation, allocation, &mut state);
        }
    }
    preserving
}

/// Whether a local allocation is live after the operations of `block`, on every path reaching it:
/// allocated, and not popped since by a restore to a marker saved before it.
pub(crate) fn alloca_live_after(func: &Function, allocation: ValueId, block: BlockId) -> bool {
    let Some(mut state) = allocation_states(func, allocation)[block.as_index()].clone() else {
        return false;
    };
    for operation in func.block(block).operations() {
        step_allocation(operation, allocation, &mut state);
    }
    state.live
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::{ParameterKind, Value, builder::FunctionBuilder, terminator::Terminator};
    use crate::{
        CompilerSession, Location, MirOptimization,
        hir::function::ArgConvention,
        std::{logic::bool_type, math::int_type},
    };

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("stack", src)
    }

    #[test]
    fn allocation_preservation_distinguishes_inner_and_outer_restores_across_a_loop() {
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("allocation_lifetime".into(), Default::default());
        let entry = builder.add_block();
        let body = builder.add_block();
        let outer = builder
            .append_operation(entry, Operation::stack_save(span))
            .unwrap();
        let allocation = builder
            .append_operation(entry, Operation::alloca(span, int_type()))
            .unwrap();
        let inner = builder
            .append_operation(entry, Operation::stack_save(span))
            .unwrap();
        builder.set_terminator(entry, Terminator::goto(span, body));
        builder.append_operation(body, Operation::alloca(span, int_type()));
        builder.append_operation(body, Operation::stack_restore(span, inner));
        builder.append_operation(body, Operation::stack_restore(span, outer));
        builder.set_terminator(body, Terminator::goto(span, body));
        let function = builder.finish_unverified();
        let Value::Register(allocation) = allocation else {
            unreachable!()
        };
        // The backedge follows reclamation of the source. Even the inner marker cannot prove
        // preservation on *every* visit; a snapshot does not resurrect an ended allocation.
        assert!(restores_preserving_alloca(&function, allocation).is_empty());

        let mut edit = FunctionEdit::new(function);
        edit.block_mut(body).operations.pop();
        let function = edit.finish_unverified();
        assert_eq!(
            restores_preserving_alloca(&function, allocation),
            FxHashSet::from_iter([OperationSite {
                block: body,
                index: OperationIndex::from_index(1)
            }])
        );
    }

    #[test]
    fn allocation_preservation_intersects_histories_at_joins() {
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("allocation_join".into(), Default::default());
        let entry = builder.add_block();
        let keep = builder.add_block();
        let reclaim = builder.add_block();
        let join = builder.add_block();
        let outer = builder
            .append_operation(entry, Operation::stack_save(span))
            .unwrap();
        let allocation = builder
            .append_operation(entry, Operation::alloca(span, int_type()))
            .unwrap();
        let inner = builder
            .append_operation(entry, Operation::stack_save(span))
            .unwrap();
        // Neither history at the join may be ignored.
        let condition =
            builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let));
        let condition = builder
            .append_operation(entry, Operation::load(span, Value::Parameter(condition)))
            .unwrap();
        builder.set_terminator(entry, Terminator::cond_br(span, condition, keep, reclaim));
        builder.append_operation(keep, Operation::stack_restore(span, inner.clone()));
        builder.set_terminator(keep, Terminator::goto(span, join));
        builder.append_operation(reclaim, Operation::stack_restore(span, outer));
        builder.set_terminator(reclaim, Terminator::goto(span, join));
        builder.append_operation(join, Operation::stack_restore(span, inner));
        builder.set_terminator(join, Terminator::ret(span));
        let function = builder.finish_unverified();
        let Value::Register(allocation) = allocation else {
            unreachable!()
        };
        assert_eq!(
            restores_preserving_alloca(&function, allocation),
            FxHashSet::from_iter([OperationSite {
                block: keep,
                index: OperationIndex::from_index(0)
            }])
        );
    }

    #[test]
    fn target_storage_model_decides_whether_cross_block_markers_are_no_ops() {
        let session = CompilerSession::new();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("target_stack".into(), Default::default());
        let entry = builder.add_block();
        let body = builder.add_block();
        let marker = builder
            .append_operation(entry, Operation::stack_save(span))
            .unwrap();
        builder.set_terminator(entry, Terminator::goto(span, body));
        builder.append_operation(body, Operation::check_fuel(span));
        builder.append_operation(body, Operation::stack_restore(span, marker.clone()));
        builder.set_terminator(body, Terminator::ret(span));
        let function = builder.finish(session.module_env());
        let Value::Register(marker) = marker else {
            unreachable!()
        };

        assert!(no_op_stack_markers(&function, |_| false, |_| false).contains(&marker));
        assert!(
            !no_op_stack_markers(
                &function,
                |operation| matches!(operation.kind, OperationKind::CheckFuel),
                |_| false,
            )
            .contains(&marker)
        );
    }

    /// A backend retaining suspension frames resumes on a frontier of its own, so a mark taken after
    /// a `yield` must not defer to one taken before it, even with no allocation in between.
    #[test]
    fn a_mark_after_a_yield_is_not_merged_into_one_before_it() {
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("suspended".into(), Default::default());
        let entry = builder.add_block();
        let resume = builder.add_block();
        let place = builder
            .append_operation(entry, Operation::alloca(span, crate::std::math::int_type()))
            .unwrap();
        let before = builder
            .append_operation(entry, Operation::stack_save(span))
            .unwrap();
        builder.set_terminator(entry, Terminator::r#yield(span, place, resume));
        let after = builder
            .append_operation(resume, Operation::stack_save(span))
            .unwrap();
        builder.append_operation(resume, Operation::stack_restore(span, before));
        builder.append_operation(resume, Operation::stack_restore(span, after));
        builder.set_terminator(resume, Terminator::ret(span));
        let function = builder.finish_unverified();

        let simplified = remove_redundant_stack_markers(&function).unwrap_or(function);
        assert!(
            simplified
                .block(resume)
                .operations()
                .iter()
                .any(|operation| matches!(operation.kind, OperationKind::StackSave)),
            "the resumed region must keep its own mark"
        );
    }

    /// Two `stack_save`s with nothing between them take the same mark, so one must go. This is the
    /// shape nested inlining produces and the cheapest observable case of the rule.
    ///
    /// Asserted as an invariant over the whole module rather than a count, which would pin the
    /// inliner's decisions rather than this pass's.
    #[test]
    fn no_two_stack_saves_are_adjacent() {
        let module = optimized("fn main() { [1, 2] |> concat([3, 4]) |> map(|x| x * x); }");
        let lines: Vec<&str> = module.lines().map(str::trim).collect();
        let adjacent: Vec<&str> = lines
            .windows(2)
            .filter(|pair| pair[0].contains("stack_save") && pair[1].contains("stack_save"))
            .map(|pair| pair[1])
            .collect();
        assert!(
            adjacent.is_empty(),
            "a save taken at an already-recorded frontier must be removed, found {} :\n{}",
            adjacent.len(),
            adjacent.join("\n")
        );
        assert!(
            lines.iter().any(|line| line.contains("stack_save")),
            "the pipeline must still bracket the regions that reclaim storage:\n{module}"
        );
    }
}
