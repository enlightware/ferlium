// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Removal of dead proven-total calls and the storage scaffolding that folding leaves behind.
//!
//! Folding replaces `call f(a, b, ret)` with `store @cN to ret` or a constructive operation such as
//! `build_array`. That can leave the arguments' own construction and cleanup in place: correct,
//! since nothing reads them, but they still cost storage and writes at run time and bury the result
//! in noise when the MIR is read.
//!
//! This is **not** general dead-code elimination. Before storage cleanup, a backward use-count
//! worklist removes unused chains of concrete numeric calls explicitly classified as total and
//! speculatable, plus direct script calls whose raw-MIR summary proves they return. An empty effect
//! row is not sufficient: an arbitrary pure function may diverge.
//! The ordinary storage rule removes an `alloca` only when every use of it is as the destination of
//! a constant `store`. The cleanup entered after tail merging additionally admits a non-owning
//! operation result. Two properties make those stores safe without a whole ownership analysis:
//!
//! - a constant is trivially copyable, so storing one creates no drop obligation;
//! - an admitted register's defining operation explicitly says its result requires no consuming
//!   use, excluding variants and owning closure construction. Deleting the store therefore cannot
//!   orphan a resource — which the verifier would reject, and which is the trap any wider rule
//!   falls into first.
//!
//! Unread `dict_entry` and `subfield` place derivations are also removed. They neither own a value
//! nor have side effects, and a linear use-count worklist handles nested `subfield` chains.
//! A compiler-known `build_array`, bare function store, or semantic `clone` used only by its
//! matching drops is removed as one lifetime: deleting construction and cleanup together neither
//! leaks nor drops uninitialized storage. An exact same-block clone/drop pair is also removed when
//! the allocation has no observing or alias-producing use, even if later lifetimes reuse its cell.
//! This deliberately does not generalize to arbitrary resource producers.
//! Constants left unreferenced by removed stores are dropped from the pool with them.
//!
//! Any surviving use of an allocation — a `load`, a `subfield`, a call argument, or an unadmitted
//! register store — disqualifies that allocation. A drop is admitted only as part of one of the
//! complete lifetimes above. Widening the storage rule means proving the drop obligation is
//! discharged, and should happen only against the whole corpus.

#![allow(dead_code)]

use rustc_hash::{FxHashMap, FxHashSet};

use crate::mir::{
    self, BlockId, Function, OperationKind, edit::FunctionEdit, terminator::TerminatorKind,
    value::ValueId,
};
use crate::{
    hir::function::ArgConvention,
    module::{FunctionId, ModuleEnv, id::Id},
    types::{
        r#type::{CallResultConvention, Type},
        type_properties::concrete_type_is_trivial_copy,
    },
};

use super::{dataflow, known_callee::KnownCallees, site::OperationIndex};

#[derive(Clone, Copy)]
struct DeadResultCandidate {
    block: BlockId,
    operation: OperationIndex,
}

/// Removes candidate operations once their result has only `dead_at` remaining uses.
///
/// A direct result-producing operation is dead at zero uses. A value-returning call writes through
/// an alloca operand, so its one self-use is the dead state. In either case, removing one candidate
/// decrements its operands and can expose another candidate in the same backwards walk.
fn remove_dead_results(
    func: &Function,
    candidates: FxHashMap<ValueId, DeadResultCandidate>,
    dead_at: usize,
) -> Option<Function> {
    if candidates.is_empty() {
        return None;
    }

    let mut uses = FxHashMap::<ValueId, usize>::default();
    let mut count_operands = |operands: &[mir::Value]| {
        for operand in operands {
            if let mir::Value::Register(id) = operand {
                *uses.entry(*id).or_default() += 1;
            }
        }
    };
    for block in func.blocks() {
        let basic_block = func.block(block);
        for operation in basic_block.operations() {
            count_operands(&operation.operands);
        }
        count_operands(basic_block.terminator().operands());
    }

    let remaining_uses =
        |uses: &FxHashMap<ValueId, usize>, result: &ValueId| uses.get(result).copied().unwrap_or(0);
    let mut pending: Vec<_> = candidates
        .keys()
        .copied()
        .filter(|result| remaining_uses(&uses, result) == dead_at)
        .collect();
    let mut removed_results = FxHashSet::default();
    let mut removed = FxHashMap::<BlockId, FxHashSet<OperationIndex>>::default();
    while let Some(result) = pending.pop() {
        if !removed_results.insert(result) || remaining_uses(&uses, &result) != dead_at {
            continue;
        }
        let candidate = candidates[&result];
        removed
            .entry(candidate.block)
            .or_default()
            .insert(candidate.operation);
        for operand in
            &func.block(candidate.block).operations()[candidate.operation.as_index()].operands
        {
            let mir::Value::Register(operand) = operand else {
                continue;
            };
            let count = uses
                .get_mut(operand)
                .expect("every register operand was counted");
            *count -= 1;
            if *count == 0 {
                uses.remove(operand);
            }
            if remaining_uses(&uses, operand) == dead_at && candidates.contains_key(operand) {
                pending.push(*operand);
            }
        }
    }
    if removed.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for (block, indices) in removed {
        let mut index = 0usize;
        edit.block_mut(block).operations.retain(|_| {
            let keep = !indices.contains(&OperationIndex::from_index(index));
            index += 1;
            keep
        });
    }
    Some(edit.finish_unverified())
}

/// Removes unread results of representation-only operations.
///
/// This is the narrow non-call half needed after tail merging makes a predicate dead. Calls require
/// the stronger total/speculatable contract below; stores and allocations are handled as complete
/// local-storage lifetimes by [`remove_dead_storage`]. A backwards use-count worklist removes a
/// chain in one scan without pretending that arbitrary effect-free operations are speculatable.
pub(crate) fn remove_dead_trivial_results(func: &Function) -> Option<Function> {
    let mut candidates = FxHashMap::<ValueId, DeadResultCandidate>::default();
    for block in func.blocks() {
        let basic_block = func.block(block);
        for (index, operation) in basic_block.operations().iter().enumerate() {
            if matches!(
                operation.kind,
                OperationKind::CompareEqual | OperationKind::Load | OperationKind::ExtractTag
            ) && let Some(result) = operation.result_id()
            {
                debug_assert!(!operation.result_requires_consuming_use());
                candidates.insert(
                    result,
                    DeadResultCandidate {
                        block,
                        operation: OperationIndex::from_index(index),
                    },
                );
            }
        }
    }
    remove_dead_results(func, candidates, 0)
}

/// Removes unused calls known to return without source-visible effects.
///
/// An empty effect row is intentionally insufficient: a pure script call may diverge, and deleting
/// it would change behaviour. A concrete native numeric operation uses [`KnownCallees`]' explicit
/// total/speculatable contract. Any other direct callee must be a module-table script body with a
/// raw-MIR `will_return` proof. Its authoritative parameter conventions must all be passive `Let`,
/// it may have no hidden evidence inputs, and its concrete result must be `TrivialCopy`; together
/// these conditions exclude mutation through an argument and a managed result's ownership
/// lifetime. Its result must be a local whole-place `alloca` with no surviving read. A backwards
/// use-count worklist removes chains in one pass: deleting a dead consumer can make the total call
/// that produced one of its arguments dead in turn.
pub(crate) fn remove_dead_proven_calls(
    func: &Function,
    env: ModuleEnv<'_>,
    known: &KnownCallees,
    original_of: &dyn Fn(FunctionId) -> Option<FunctionId>,
    will_return: &dyn Fn(FunctionId) -> bool,
) -> Option<Function> {
    let mut allocas = FxHashSet::default();
    let mut candidates = FxHashMap::<ValueId, DeadResultCandidate>::default();
    let mut trivial_copy = FxHashMap::default();
    for block in func.blocks() {
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            if matches!(operation.kind, OperationKind::Alloca { .. })
                && let Some(result) = operation.result_id()
            {
                allocas.insert(result);
            }
            let OperationKind::Call { ty, metadata } = &operation.kind else {
                continue;
            };
            if !ty.effects().is_empty() || ty.result_convention != CallResultConvention::Value {
                continue;
            }
            let Some(mut call) = dataflow::call_operands(&operation.operands, ty) else {
                continue;
            };
            let mir::Value::Function(callee) = *call.callee else {
                continue;
            };
            let known_total = known
                .resolve(callee, original_of)
                .is_some_and(|callee| callee.is_total_and_speculatable());
            if !known_total {
                let Some(function) = env
                    .module_by_id(callee.module)
                    .and_then(|module| module.get_function_by_id(callee.function))
                else {
                    continue;
                };
                if function.code.as_script().is_none()
                    || function.parameter_passing.len() != call.arguments.len()
                {
                    continue;
                }
                call.arguments = call
                    .arguments
                    .into_iter()
                    .zip(&function.parameter_passing)
                    .map(|((argument, _), convention)| (argument, *convention))
                    .collect();
            }
            let eligible = known_total
                || (!metadata
                    .as_deref()
                    // Vacuous in today's pipeline because whole-module owned-argument forwarding
                    // runs after per-function DCE. Retain the guard so a future reordering cannot
                    // delete an ownership transfer and its callee-side cleanup.
                    .is_some_and(|metadata| !metadata.owned_arguments.is_empty())
                    // Hidden evidence can carry semantic callbacks (for example `Value::drop`),
                    // whose effects are not represented in the direct call type.
                    && call.extras.is_empty()
                    && call
                        .arguments
                        .iter()
                        .all(|(_, convention)| *convention == ArgConvention::Let)
                    && *trivial_copy
                        .entry(ty.ret())
                        .or_insert_with(|| concrete_type_is_trivial_copy(ty.ret(), &env))
                    && will_return(callee));
            if !eligible {
                continue;
            }
            let mir::Value::Register(result) = call.result else {
                continue;
            };
            candidates.insert(
                *result,
                DeadResultCandidate {
                    block,
                    operation: OperationIndex::from_index(index),
                },
            );
        }
    }
    candidates.retain(|result, _| allocas.contains(result));
    // The shared use census is the more expensive part and starts only after the semantic scan
    // above found an eligible call whose result is local storage.
    remove_dead_results(func, candidates, 1)
}

/// Removes dead storage scaffolding, returning a rewritten function if anything was removed.
pub(crate) fn remove_dead_storage(func: &Function) -> Option<Function> {
    remove_dead_storage_impl(func, false)
}

/// The storage cleanup used only after tail merging made a representation chain dead.
///
/// Unlike ordinary DCE, this admits stores of results whose defining operation declares that the
/// result needs no consuming use. Keeping the extra producer census behind this entry point means
/// every unchanged function retains the cheaper constant-only scan.
pub(crate) fn remove_dead_storage_after_tail_merge(func: &Function) -> Option<Function> {
    remove_dead_storage_impl(func, true)
}

fn remove_dead_storage_impl(
    func: &Function,
    admit_non_consuming_register_stores: bool,
) -> Option<Function> {
    let mut census = DceCensus::of(func, admit_non_consuming_register_stores);
    let constructed = census.dead_constructed_values();
    let clone_pairs = census.dead_same_block_clone_drop_pairs();
    let mut dead = census.dead_allocas();
    for (block, operations) in constructed.into_iter().chain(clone_pairs) {
        dead.operations.entry(block).or_default().extend(operations);
    }
    let dead_places = census.unread_derived_places(func, &dead.operations);
    for (block, index) in dead_places {
        dead.operations.entry(block).or_default().insert(index);
    }
    remove_empty_local_stack_regions(func, &census.restore_uses, &mut dead.operations);
    if dead.operations.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for block in func.blocks() {
        let removed: &FxHashSet<OperationIndex> = match dead.operations.get(&block) {
            Some(indices) => indices,
            None => continue,
        };
        let mut index = 0;
        edit.block_mut(block).operations.retain(|_| {
            let keep = !removed.contains(&OperationIndex::from_index(index));
            index += 1;
            keep
        });
    }
    // The constants those stores named are usually the last reference to them; dropping the entries
    // keeps the pool an inventory of what the function actually uses.
    edit.prune_constants();
    Some(edit.finish_unverified())
}

/// Adds same-block stack regions that provably reclaim no storage to `removed`.
///
/// Inlining emits a `stack_save` before a copied body and a `stack_restore` at each exit. The
/// straight-line case has one restore in the same block after block merging. Once DCE has removed
/// every frame-growing operation between the two, both markers are no-ops.
///
/// This deliberately handles only properly nested, single-use regions within one basic block. A
/// marker restored on several exits or across blocks needs CFG reasoning; leaving it alone is safe.
/// The scan is linear in the function and handles nesting without revisiting an operation.
fn remove_empty_local_stack_regions(
    func: &Function,
    restore_uses: &FxHashMap<ValueId, usize>,
    removed: &mut FxHashMap<BlockId, FxHashSet<OperationIndex>>,
) {
    struct Region {
        marker: ValueId,
        save_index: OperationIndex,
        grows_frame: bool,
    }

    for block in func.blocks() {
        let already_removed = removed.get(&block).cloned().unwrap_or_default();
        let mut regions: Vec<Region> = Vec::new();
        let mut newly_removed = Vec::new();

        for (index, operation) in func.block(block).operations().iter().enumerate() {
            let index = OperationIndex::from_index(index);
            if already_removed.contains(&index) {
                continue;
            }
            match &operation.kind {
                OperationKind::StackSave => {
                    let Some(marker) = operation.result_id() else {
                        continue;
                    };
                    if restore_uses.get(&marker) == Some(&1) {
                        regions.push(Region {
                            marker,
                            save_index: index,
                            grows_frame: false,
                        });
                    }
                }
                OperationKind::StackRestore => {
                    let Some(mir::Value::Register(marker)) = operation.operands.first() else {
                        continue;
                    };
                    if let Some(region) = regions.pop_if(|region| region.marker == *marker) {
                        if !region.grows_frame {
                            newly_removed.push(region.save_index);
                            newly_removed.push(index);
                        }
                    }
                }
                _ if may_leave_frame_storage(operation) => {
                    if let Some(region) = regions.last_mut() {
                        region.grows_frame = true;
                    }
                }
                _ => {}
            }
        }

        if !newly_removed.is_empty() {
            removed.entry(block).or_default().extend(newly_removed);
        }
    }
}

/// Whether executing an operation may leave a cell allocated in the current MIR frame.
///
/// This is intentionally conservative. Several interpreter operations materialize temporary places
/// even though they are not spelled `alloca`; dictionary/subscript projection, semantic drop and a
/// call carrying symbolic subscript evidence can do so. False positives merely retain a bracket.
pub(super) fn may_leave_frame_storage(operation: &mir::Operation) -> bool {
    match &operation.kind {
        OperationKind::Alloca { .. }
        | OperationKind::AllocaPlace { .. }
        | OperationKind::Project { .. }
        | OperationKind::EndProject
        | OperationKind::DictEntry { .. }
        | OperationKind::SubscriptMember { .. }
        | OperationKind::Drop { .. } => true,
        // A call reclaims its own script frame, and closure calls bracket their materialized
        // evidence and environment internally. The one caller-frame temporary is a symbolic
        // subscript passed as script evidence; retaining every such call is conservative because a
        // native call can marshal the same operand without allocating a cell.
        OperationKind::Call { .. } => operation
            .operands
            .iter()
            .any(|operand| matches!(operand, mir::Value::Subscript(_))),
        OperationKind::CompareEqual
        | OperationKind::Load
        | OperationKind::Subfield { .. }
        | OperationKind::BuildSubscript { .. }
        | OperationKind::Variant { .. }
        | OperationKind::BuildArray { .. }
        | OperationKind::ExtractTag
        | OperationKind::Store
        | OperationKind::Clear
        | OperationKind::Memcpy
        | OperationKind::Move
        | OperationKind::StackSave
        | OperationKind::StackRestore
        | OperationKind::CheckCallDepth
        | OperationKind::CheckFuel
        | OperationKind::Clone { .. }
        | OperationKind::BuildClosure { .. }
        | OperationKind::CloneClosureEnv { .. }
        | OperationKind::DropClosureEnv => false,
    }
}

/// Information shared by DCE's independent lifetime rules.
///
/// Definitions are collected first so the second pass can classify every use even when canonical
/// block order does not happen to visit a definition before its users. That one use pass replaces
/// the formerly separate censuses for constructed values, constant-only allocations, derived
/// places and stack-marker restores.
struct DceCensus {
    allocations: FxHashMap<ValueId, AllocationUses>,
    derived_definitions: FxHashMap<ValueId, (BlockId, OperationIndex)>,
    derived_uses: FxHashMap<ValueId, usize>,
    restore_uses: FxHashMap<ValueId, usize>,
    non_consuming_results: FxHashSet<ValueId>,
    same_block_clone_drop_pairs: Vec<CloneDropPair>,
}

/// The operations selected for removal, grouped by block.
struct Dead {
    operations: FxHashMap<BlockId, FxHashSet<OperationIndex>>,
}

#[derive(Default)]
struct AllocationUses {
    definition: (BlockId, OperationIndex),
    removable_stores: Vec<(BlockId, OperationIndex)>,
    storage_only_invalid: bool,
    /// The constructor/drop uses are allowed only if the complete lifetime is removable.
    has_deferred_construction_use: bool,
    constructor: Option<(BlockId, OperationIndex)>,
    drops: Vec<(BlockId, OperationIndex)>,
    invalid_construction: bool,
    /// Whether some use prevents exact same-block clone/drop lifetime cancellation.
    invalid_clone_pair_use: bool,
}

#[derive(Clone, Copy)]
struct CloneDropPair {
    allocation: ValueId,
    block: BlockId,
    clone: OperationIndex,
    drop: OperationIndex,
}

impl AllocationUses {
    fn has_removable_construction(&self) -> bool {
        !self.invalid_construction && !self.drops.is_empty() && self.constructor.is_some()
    }
}

impl DceCensus {
    fn of(func: &Function, census_non_consuming_results: bool) -> DceCensus {
        let mut census = DceCensus {
            allocations: FxHashMap::default(),
            derived_definitions: FxHashMap::default(),
            derived_uses: FxHashMap::default(),
            restore_uses: FxHashMap::default(),
            non_consuming_results: FxHashSet::default(),
            same_block_clone_drop_pairs: Vec::new(),
        };
        let mut has_clone = false;

        for block in func.blocks() {
            for (index, operation) in func.block(block).operations().iter().enumerate() {
                let index = OperationIndex::from_index(index);
                has_clone |= matches!(operation.kind, OperationKind::Clone { .. });
                let Some(result) = operation.result_id() else {
                    continue;
                };
                if census_non_consuming_results && !operation.result_requires_consuming_use() {
                    census.non_consuming_results.insert(result);
                }
                if matches!(operation.kind, OperationKind::Alloca { .. }) {
                    census.allocations.insert(
                        result,
                        AllocationUses {
                            definition: (block, index),
                            ..AllocationUses::default()
                        },
                    );
                } else if matches!(
                    operation.kind,
                    OperationKind::DictEntry { .. } | OperationKind::Subfield { .. }
                ) {
                    census.derived_definitions.insert(result, (block, index));
                }
            }
        }

        for block in func.blocks() {
            let basic_block = func.block(block);
            let mut pending_clones = FxHashMap::<ValueId, (OperationIndex, Type)>::default();
            for (index, operation) in basic_block.operations().iter().enumerate() {
                let index = OperationIndex::from_index(index);
                if has_clone {
                    census.note_same_block_clone_drop_pair(
                        block,
                        index,
                        operation,
                        &mut pending_clones,
                    );
                }
                if matches!(operation.kind, OperationKind::StackRestore)
                    && let Some(mir::Value::Register(marker)) = operation.operands.first()
                {
                    *census.restore_uses.entry(*marker).or_default() += 1;
                }
                for (position, operand) in operation.operands.iter().enumerate() {
                    census
                        .note_operation_use(block, index, operation, position, operand, has_clone);
                }
            }
            census.note_terminator_uses(&basic_block.terminator().kind);
        }

        census
    }

    /// Records an exact local clone lifetime which starts and ends in this block without any
    /// intervening use of its destination.
    ///
    /// Candidates are filtered after the complete use census: an allocation which is ever read,
    /// projected or passed to a call may have an alias not named by the root at the candidate site.
    /// Whole-place initialization and cleanup roles are safe because they cannot expose such an
    /// alias. Keeping the ordered part block-local avoids a CFG fixed point; the complete-lifetime
    /// rule below independently handles clone/drop cleanup split across successor blocks.
    fn note_same_block_clone_drop_pair(
        &mut self,
        block: BlockId,
        index: OperationIndex,
        operation: &mir::Operation,
        pending: &mut FxHashMap<ValueId, (OperationIndex, Type)>,
    ) {
        let remove_pending_operands = |pending: &mut FxHashMap<ValueId, _>| {
            if pending.is_empty() {
                return;
            }
            for operand in &operation.operands {
                if let mir::Value::Register(id) = operand {
                    pending.remove(id);
                }
            }
        };

        match &operation.kind {
            OperationKind::Clone { ty }
                if let Some(mir::Value::Register(destination)) = operation.operands.get(1)
                    && self.allocations.contains_key(destination)
                    && operation
                        .operands
                        .iter()
                        .enumerate()
                        .all(|(position, operand)| {
                            position == 1
                                || !matches!(operand, mir::Value::Register(id) if id == destination)
                        }) =>
            {
                remove_pending_operands(pending);
                pending.insert(*destination, (index, *ty));
            }
            OperationKind::Drop { ty }
                if let Some(mir::Value::Register(target)) = operation.operands.first()
                    && operation
                        .operands
                        .iter()
                        .enumerate()
                        .all(|(position, operand)| {
                            position == 0
                                || !matches!(operand, mir::Value::Register(id) if id == target)
                        }) =>
            {
                let matched = pending
                    .get(target)
                    .copied()
                    .filter(|(_, clone_ty)| clone_ty == ty);
                remove_pending_operands(pending);
                if let Some((clone, _)) = matched {
                    self.same_block_clone_drop_pairs.push(CloneDropPair {
                        allocation: *target,
                        block,
                        clone,
                        drop: index,
                    });
                }
            }
            _ => {
                remove_pending_operands(pending);
            }
        }
    }

    fn note_operation_use(
        &mut self,
        block: BlockId,
        index: OperationIndex,
        operation: &mir::Operation,
        position: usize,
        operand: &mir::Value,
        track_clone_pairs: bool,
    ) {
        let mir::Value::Register(id) = operand else {
            return;
        };
        if self.derived_definitions.contains_key(id) {
            *self.derived_uses.entry(*id).or_default() += 1;
        }
        let removable_store = matches!(operation.kind, OperationKind::Store)
            && position == 1
            && match operation.operands[0] {
                mir::Value::Constant(_) => true,
                mir::Value::Register(result) => self.non_consuming_results.contains(&result),
                _ => false,
            };
        let Some(allocation) = self.allocations.get_mut(id) else {
            return;
        };
        if removable_store {
            allocation.removable_stores.push((block, index));
        }

        let is_array_constructor = matches!(operation.kind, OperationKind::BuildArray { .. })
            && position + 1 == operation.operands.len();
        let is_bare_function_constructor = matches!(operation.kind, OperationKind::Store)
            && position == 1
            && matches!(operation.operands[0], mir::Value::Function(_));
        let is_clone_constructor =
            matches!(operation.kind, OperationKind::Clone { .. }) && position == 1;
        let is_drop = matches!(operation.kind, OperationKind::Drop { .. }) && position == 0;
        let is_construction_use =
            is_array_constructor || is_bare_function_constructor || is_clone_constructor || is_drop;
        if !removable_store {
            if is_construction_use {
                allocation.has_deferred_construction_use = true;
            } else {
                allocation.storage_only_invalid = true;
            }
        }

        if is_array_constructor || is_bare_function_constructor || is_clone_constructor {
            if allocation.constructor.replace((block, index)).is_some() {
                allocation.invalid_construction = true;
            }
        } else if is_drop {
            allocation.drops.push((block, index));
        } else {
            allocation.invalid_construction = true;
        }

        if track_clone_pairs && !is_exact_clone_lifetime_role(operation, position) {
            allocation.invalid_clone_pair_use = true;
        }
    }

    fn note_terminator_uses(&mut self, terminator: &TerminatorKind) {
        let mut note = |operand: &mir::Value| {
            let mir::Value::Register(id) = operand else {
                return;
            };
            if self.derived_definitions.contains_key(id) {
                *self.derived_uses.entry(*id).or_default() += 1;
            }
            if let Some(allocation) = self.allocations.get_mut(id) {
                allocation.storage_only_invalid = true;
                allocation.invalid_construction = true;
                allocation.invalid_clone_pair_use = true;
            }
        };
        match terminator {
            TerminatorKind::Invoke { operation, .. } => {
                operation.operands.iter().for_each(&mut note);
            }
            TerminatorKind::CondBr { condition, .. } => note(condition),
            TerminatorKind::Yield { place, .. } => note(place),
            TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::PropagateError
            | TerminatorKind::FailureDuringCleanup => {}
        }
    }

    fn dead_constructed_values(&self) -> FxHashMap<BlockId, FxHashSet<OperationIndex>> {
        let mut removed = FxHashMap::<BlockId, FxHashSet<OperationIndex>>::default();
        for candidate in self.allocations.values() {
            if !candidate.has_removable_construction() {
                continue;
            }
            let Some((block, constructor)) = candidate.constructor else {
                continue;
            };
            removed.entry(block).or_default().insert(constructor);
            for (block, drop) in &candidate.drops {
                removed.entry(*block).or_default().insert(*drop);
            }
        }
        removed
    }

    fn dead_same_block_clone_drop_pairs(&self) -> FxHashMap<BlockId, FxHashSet<OperationIndex>> {
        let mut removed = FxHashMap::<BlockId, FxHashSet<OperationIndex>>::default();
        for pair in &self.same_block_clone_drop_pairs {
            if self.allocations[&pair.allocation].invalid_clone_pair_use {
                continue;
            }
            removed.entry(pair.block).or_default().insert(pair.clone);
            removed.entry(pair.block).or_default().insert(pair.drop);
        }
        removed
    }

    fn dead_allocas(&self) -> Dead {
        let mut operations = FxHashMap::<BlockId, FxHashSet<OperationIndex>>::default();
        for candidate in self.allocations.values() {
            // Constructor/drop uses cease to disqualify the alloca only when that complete resource
            // lifetime is itself selected for removal.
            if candidate.storage_only_invalid
                || (candidate.has_deferred_construction_use
                    && !candidate.has_removable_construction())
            {
                continue;
            }
            let (block, index) = candidate.definition;
            operations.entry(block).or_default().insert(index);
            for (block, index) in &candidate.removable_stores {
                operations.entry(*block).or_default().insert(*index);
            }
        }
        Dead { operations }
    }

    /// The pure place derivations nothing reads any more.
    ///
    /// **Devirtualization is what makes these dead.** It rewrites a call through a resolved
    /// dictionary entry to name the callee directly, which removes the only use the entry usually
    /// had — so a successful devirtualization leaves an operation computing a place no one reads.
    /// Over `sudoku.fer` that is 86 of the 88 entries taken from a constant dictionary.
    ///
    /// Removing one is safe without any of the analysis the `alloca` rule needs: `dict_entry` reads
    /// evidence and `subfield` only extends a place path. Neither has a side effect or yields an
    /// owned value, so an unread result discharges no drop obligation and consumes nothing.
    ///
    /// `subfield`s can form chains, so use counts are retired through a worklist: deleting an
    /// unread leaf may make its base derivation unread too.
    fn unread_derived_places(
        &mut self,
        func: &Function,
        removed_operations: &FxHashMap<BlockId, FxHashSet<OperationIndex>>,
    ) -> Vec<(BlockId, OperationIndex)> {
        if self.derived_definitions.is_empty() {
            return Vec::new();
        }

        let mut uses = std::mem::take(&mut self.derived_uses);
        // A removed clone/drop lifetime can strand its dictionary-derived dispatch places. Retire
        // those uses before starting the existing derived-place worklist, avoiding a second DCE
        // traversal merely to collect the callees the lifetime removal made unread.
        for (block, indices) in removed_operations {
            for index in indices {
                for operand in &func.block(*block).operations()[index.as_index()].operands {
                    let mir::Value::Register(id) = operand else {
                        continue;
                    };
                    if self.derived_definitions.contains_key(id)
                        && let Some(count) = uses.get_mut(id)
                    {
                        *count -= 1;
                        if *count == 0 {
                            uses.remove(id);
                        }
                    }
                }
            }
        }
        let mut pending: Vec<ValueId> = self
            .derived_definitions
            .keys()
            .copied()
            .filter(|result| !uses.contains_key(result))
            .collect();
        let mut dead_results: FxHashSet<ValueId> = FxHashSet::default();
        while let Some(result) = pending.pop() {
            if !dead_results.insert(result) {
                continue;
            }
            let (block, index) = self.derived_definitions[&result];
            for operand in &func.block(block).operations()[index.as_index()].operands {
                let mir::Value::Register(operand) = operand else {
                    continue;
                };
                if let Some(count) = uses.get_mut(operand) {
                    *count -= 1;
                    if *count == 0 {
                        pending.push(*operand);
                    }
                }
            }
        }

        dead_results
            .into_iter()
            .map(|result| self.derived_definitions[&result])
            .collect()
    }
}

/// Whether this operand role can neither observe an initialized lifetime nor retain an alias to it.
///
/// The same-block rule removes only a clone and the drop ending that particular lifetime. Other
/// whole-place writes and drops may belong to later lifetimes in the same allocation and therefore
/// remain. Any read, projection, call argument, or unmodelled role rejects every pair for the root.
fn is_exact_clone_lifetime_role(operation: &mir::Operation, position: usize) -> bool {
    match &operation.kind {
        OperationKind::Clone { .. } => position == 1,
        OperationKind::Drop { .. } | OperationKind::Clear => position == 0,
        OperationKind::Store | OperationKind::Memcpy | OperationKind::Move => position == 1,
        OperationKind::BuildArray { .. } => position + 1 == operation.operands.len(),
        OperationKind::Call { ty, .. } => {
            dataflow::call_result_operand_index(&operation.operands, ty) == Some(position)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization};

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("dce", src)
    }

    fn raw(src: &str) -> String {
        CompilerSession::new().emit_mir("dce", src)
    }

    fn body_of<'a>(module: &'a str, name: &str) -> &'a str {
        module
            .split(&format!("fn {name}"))
            .nth(1)
            .unwrap_or_else(|| panic!("module has no `{name}`:\n{module}"))
            .split("\nfn ")
            .next()
            .unwrap()
    }

    /// The gate example, all the way down: after folding and cleanup, nothing is left but the store
    /// of the result into the return place.
    #[test]
    fn folded_arithmetic_leaves_only_its_result() {
        let module = optimized("fn main() -> int { let x = 2 + 3; x * 7 }");
        let main = body_of(&module, "main");

        assert!(
            !main.contains("alloca"),
            "every argument place is dead after folding:\n{main}"
        );
        let stores = main.lines().filter(|line| line.contains("store ")).count();
        assert_eq!(stores, 1, "only the result store must remain:\n{main}");
        assert!(main.contains("to %p0"), "{main}");
    }

    /// Devirtualization takes a dictionary entry's only reader, leaving an operation that computes
    /// a place nothing looks at. Over `sudoku.fer` that was 86 of the 88 entries read from a
    /// constant dictionary, which is what motivated the rule.
    #[test]
    fn a_dictionary_entry_nothing_reads_is_removed() {
        let module = optimized(
            "fn twice_it(x) { x + x }\n\
             fn use_it(n: int) -> int { twice_it(n) }",
        );
        let caller = body_of(&module, "use_it");

        assert!(
            caller.contains("call std::Num<std::int>::add"),
            "the call must have been devirtualized, or there is no dead entry to remove:\n{caller}"
        );
        assert!(
            !caller.contains("dict_entry"),
            "the entry it no longer reads must be gone:\n{caller}"
        );
    }

    /// Lowering a variant pattern projects both layers of its payload, even when the source-level
    /// binding is unused. The inner unread `subfield` must make the outer one dead through the
    /// worklist.
    #[test]
    fn an_unread_chain_of_subfields_is_removed() {
        let source = "fn has_value(x: None | Some(int)) -> bool { match x { Some(_n) => true, None => false } }";
        let raw_module = raw(source);
        let raw_body = body_of(&raw_module, "has_value");
        let raw_subfields = raw_body
            .lines()
            .filter(|line| line.contains("subfield"))
            .count();
        assert_eq!(
            raw_subfields, 2,
            "the test needs the nested lowering artifact it exercises:\n{raw_body}"
        );

        let module = optimized(source);
        let body = body_of(&module, "has_value");
        let optimized_subfields = body
            .lines()
            .filter(|line| line.contains("subfield"))
            .count();
        assert_eq!(
            optimized_subfields, 0,
            "both unread payload projections must be gone:\n{body}"
        );
    }

    #[test]
    fn an_unused_managed_clone_lifetime_is_removed() {
        let source = "fn discard(x: [int]) { let mut copy = x; () }";
        let raw_module = raw(source);
        let raw_body = body_of(&raw_module, "discard");
        assert!(
            raw_body.contains("clone [int]") && raw_body.contains("drop [int]"),
            "the test needs the managed clone lifetime emitted by lowering:\n{raw_body}"
        );

        let module = optimized(source);
        let body = body_of(&module, "discard");
        assert!(
            !body.contains("clone ") && !body.contains("drop ") && !body.contains("alloca"),
            "the unused clone, its drop and its storage must be removed together:\n{body}"
        );
    }

    #[test]
    fn a_dead_managed_clone_before_an_overwrite_is_removed() {
        let source = "fn overwrite(x: [int]) { let mut copy = x; copy = []; () }";
        let raw_module = raw(source);
        let raw_body = body_of(&raw_module, "overwrite");
        assert!(
            raw_body.contains("clone [int]") && raw_body.matches("drop [int]").count() == 2,
            "the test needs one cloned and one replacement lifetime:\n{raw_body}"
        );

        let module = optimized(source);
        let body = body_of(&module, "overwrite");
        assert!(
            !body.contains("clone [int]") && body.matches("drop [int]").count() == 1,
            "only the replacement lifetime and its drop must remain:\n{body}"
        );
    }

    #[test]
    fn a_read_managed_clone_lifetime_is_retained() {
        let source = "fn first(x: [int]) -> int { let mut copy = x; copy[0] }";
        let module = optimized(source);
        let body = body_of(&module, "first");
        assert!(
            body.contains("clone [int]") && body.contains("drop [int]"),
            "an observed clone is not a dead ownership lifetime:\n{body}"
        );
    }

    #[test]
    fn a_dead_generic_clone_drops_its_dispatch_places() {
        let source = "fn discard<T>(x: T) where T: Value { let mut copy = x; () }";
        let raw_module = raw(source);
        let raw_body = body_of(&raw_module, "discard");
        assert!(
            raw_body.contains("clone ")
                && raw_body.contains("drop ")
                && raw_body.contains("dict_entry"),
            "the test needs dictionary-dispatched ownership operations:\n{raw_body}"
        );

        let module = optimized(source);
        let body = body_of(&module, "discard");
        assert!(
            !body.contains("clone ")
                && !body.contains("drop ")
                && !body.contains("dict_entry")
                && !body.contains("alloca"),
            "removing the lifetime must also collect its dispatch places:\n{body}"
        );
    }

    /// A straight-line inline of an allocation-free body receives a stack bracket from the
    /// inliner, but final cleanup can see that the bracket has nothing to reclaim.
    #[test]
    fn an_empty_inline_stack_region_is_removed() {
        let module = optimized(
            "fn identity(x: int) -> int { x }\n\
             fn use_it(n: int) -> int { identity(n) }",
        );
        let caller = body_of(&module, "use_it");

        assert!(
            !caller.contains("call dce::identity"),
            "identity must be inlined for the test to exercise its stack region:\n{caller}"
        );
        assert!(
            !caller.contains("stack_save") && !caller.contains("stack_restore"),
            "an allocation-free inline region needs no stack bracket:\n{caller}"
        );
    }

    /// A normal call owns and reclaims its own frame. It does not make an otherwise empty inline
    /// region necessary merely because the copied body delegates its result to a native callee.
    #[test]
    fn a_call_inside_an_otherwise_empty_inline_region_needs_no_bracket() {
        let module = optimized(
            "fn twice(x: int) -> int { x + x }\n\
             fn use_it(n: int) -> int { twice(n) }",
        );
        let caller = body_of(&module, "use_it");

        assert!(
            !caller.contains("call dce::twice") && caller.contains("call std::"),
            "the wrapper must be inlined while its delegated call survives:\n{caller}"
        );
        assert!(
            !caller.contains("stack_save") && !caller.contains("stack_restore"),
            "a self-reclaiming call does not make the inline region nonempty:\n{caller}"
        );
    }

    /// A local place in an inlined body belongs to the former callee frame. Its bracket must stay
    /// so repeated execution reclaims that place at the point where the call used to return.
    #[test]
    fn a_nonempty_inline_stack_region_is_retained() {
        let module = optimized(
            "fn through_local(x: int) -> int { let mut y = x; y = y + 1; y }\n\
             fn use_it(n: int) -> int { through_local(n) }",
        );
        let caller = body_of(&module, "use_it");

        assert!(
            !caller.contains("call dce::through_local"),
            "through_local must be inlined for the test to exercise its stack region:\n{caller}"
        );
        assert!(
            caller.contains("alloca")
                && caller.contains("stack_save")
                && caller.contains("stack_restore"),
            "a live local allocation must retain its stack bracket:\n{caller}"
        );
    }

    #[test]
    fn unused_total_integer_and_float_call_chains_are_removed() {
        let module = optimized(
            "fn discard_int(x: int) -> int {\n\
                 let first = x + 1; let second = first * 2; x\n\
             }\n\
             fn discard_float(x: float) -> float {\n\
                 let first = x + 1.5; let second = first * 2.5; x\n\
             }",
        );
        for name in ["discard_int", "discard_float"] {
            let body = body_of(&module, name);
            assert!(
                !body.contains("call "),
                "the dead total call chain and its scaffolding must disappear from {name}:\n{body}"
            );
            assert!(
                !body.contains("alloca"),
                "ordinary DCE must collect the dead calls' cells in {name}:\n{body}"
            );
        }
    }

    #[test]
    fn an_unused_proven_returning_script_call_is_removed() {
        let module = optimized(
            "#[inline(never)]\n\
             fn increment(x: int) -> int { x + 1 }\n\
             fn discard(x: int) -> int { let unused = increment(x); x }",
        );
        let caller = body_of(&module, "discard");
        assert!(
            !caller.contains("call dce::increment"),
            "the unused terminating script call must disappear:\n{caller}"
        );
    }

    /// An empty effect row says nothing about termination. The recursive call is pure, but removing
    /// it would turn a diverging function into one that returns, so only the explicitly classified
    /// native numeric calls above may use the dead-call rule.
    #[test]
    fn an_unused_arbitrary_pure_call_is_retained() {
        let module = optimized(
            "fn diverges(x: int) -> int { diverges(x) }\n\
             fn retain(x: int) -> int { let unused = diverges(x); x }",
        );
        let body = body_of(&module, "retain");
        assert!(
            body.contains("call dce::diverges"),
            "purity alone must not delete a possibly diverging call:\n{body}"
        );
    }

    #[test]
    fn an_unused_mutating_script_call_is_retained() {
        let module = optimized(
            "#[inline(never)]\n\
             fn overwrite(x: &mut int) -> int { x = 1; 0 }\n\
             fn retain() -> int { let mut x = 0; let unused = overwrite(x); x }",
        );
        let caller = body_of(&module, "retain");
        assert!(
            caller.contains("call dce::overwrite"),
            "a call with a mutable argument must retain its effect:\n{caller}"
        );
    }

    #[test]
    fn an_unused_managed_script_result_is_retained() {
        let module = optimized(
            "#[inline(never)]\n\
             fn preserve(x: string) -> string { x }\n\
             fn retain(x: string) -> string { let unused = preserve(x); x }",
        );
        let caller = body_of(&module, "retain");
        assert!(
            caller.contains("call dce::preserve"),
            "a managed result must retain its ownership lifetime:\n{caller}"
        );
    }
}
