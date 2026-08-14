// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Removal of the storage scaffolding that folding leaves behind.
//!
//! Folding replaces `call f(a, b, ret)` with `store @cN to ret` or a constructive operation such as
//! `build_array`. That can leave the arguments' own construction and cleanup in place: correct,
//! since nothing reads them, but they still cost storage and writes at run time and bury the result
//! in noise when the MIR is read.
//!
//! This is **not** general dead-code elimination. Its storage rule removes an `alloca` only when
//! *every* use of it is as the destination of a `store` whose value is a pool constant, and then
//! removes those stores with it. Two properties make that safe without any ownership analysis:
//!
//! - a constant is trivially copyable, so storing one creates no drop obligation and deleting the
//!   store discards nothing that must be dropped;
//! - the value operand is not a register, so no owned register loses its single consuming use —
//!   which the verifier would reject, and which is the trap any wider rule falls into first.
//!
//! Unread `dict_entry` and `subfield` place derivations are also removed. They neither own a value
//! nor have side effects, and a linear use-count worklist handles nested `subfield` chains.
//! A compiler-known `build_array` (or bare function store) used only by its matching drops is
//! removed as one lifetime: deleting construction and cleanup together neither leaks nor drops
//! uninitialized storage. This deliberately does not generalize to arbitrary resource producers.
//! Constants left unreferenced by removed stores are dropped from the pool with them.
//!
//! Any surviving use of an allocation — a `load`, a `subfield`, a `drop`, a call argument, or a
//! store of a register — disqualifies that allocation. Widening the storage rule means proving the
//! drop obligation is discharged, and should happen only against the whole corpus.

#![allow(dead_code)]

use rustc_hash::{FxHashMap, FxHashSet};

use crate::mir::{
    self, BlockId, Function, OperationKind, edit::FunctionEdit, terminator::TerminatorKind,
    value::ValueId,
};

/// Removes dead storage scaffolding, returning a rewritten function if anything was removed.
pub(crate) fn remove_dead_storage(func: &Function) -> Option<Function> {
    let mut census = DceCensus::of(func);
    let constructed = census.dead_constructed_values();
    let mut dead = census.dead_allocas();
    for (block, operations) in constructed {
        dead.operations.entry(block).or_default().extend(operations);
    }
    let dead_places = census.unread_derived_places(func);
    for (block, index) in dead_places {
        dead.operations.entry(block).or_default().insert(index);
    }
    remove_empty_local_stack_regions(func, &census.restore_uses, &mut dead.operations);
    if dead.operations.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for block in func.blocks() {
        let removed: &FxHashSet<usize> = match dead.operations.get(&block) {
            Some(indices) => indices,
            None => continue,
        };
        let mut index = 0;
        edit.block_mut(block).operations.retain(|_| {
            let keep = !removed.contains(&index);
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
    removed: &mut FxHashMap<BlockId, FxHashSet<usize>>,
) {
    struct Region {
        marker: ValueId,
        save_index: usize,
        grows_frame: bool,
    }

    for block in func.blocks() {
        let already_removed = removed.get(&block).cloned().unwrap_or_default();
        let mut regions: Vec<Region> = Vec::new();
        let mut newly_removed = Vec::new();

        for (index, operation) in func.block(block).operations().iter().enumerate() {
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
    derived_definitions: FxHashMap<ValueId, (BlockId, usize)>,
    derived_uses: FxHashMap<ValueId, usize>,
    restore_uses: FxHashMap<ValueId, usize>,
}

/// The operations selected for removal, grouped by block.
struct Dead {
    operations: FxHashMap<BlockId, FxHashSet<usize>>,
}

#[derive(Default)]
struct AllocationUses {
    definition: (BlockId, usize),
    constant_stores: Vec<(BlockId, usize)>,
    constant_only_invalid: bool,
    /// The constructor/drop uses are allowed only if the complete lifetime is removable.
    has_deferred_construction_use: bool,
    constructor: Option<(BlockId, usize)>,
    drops: Vec<(BlockId, usize)>,
    invalid_construction: bool,
}

impl AllocationUses {
    fn has_removable_construction(&self) -> bool {
        !self.invalid_construction && !self.drops.is_empty() && self.constructor.is_some()
    }
}

impl DceCensus {
    fn of(func: &Function) -> DceCensus {
        let mut census = DceCensus {
            allocations: FxHashMap::default(),
            derived_definitions: FxHashMap::default(),
            derived_uses: FxHashMap::default(),
            restore_uses: FxHashMap::default(),
        };

        for block in func.blocks() {
            for (index, operation) in func.block(block).operations().iter().enumerate() {
                let Some(result) = operation.result_id() else {
                    continue;
                };
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
            for (index, operation) in basic_block.operations().iter().enumerate() {
                if matches!(operation.kind, OperationKind::StackRestore)
                    && let Some(mir::Value::Register(marker)) = operation.operands.first()
                {
                    *census.restore_uses.entry(*marker).or_default() += 1;
                }
                for (position, operand) in operation.operands.iter().enumerate() {
                    census.note_operation_use(block, index, operation, position, operand);
                }
            }
            census.note_terminator_uses(&basic_block.terminator().kind);
        }

        census
    }

    fn note_operation_use(
        &mut self,
        block: BlockId,
        index: usize,
        operation: &mir::Operation,
        position: usize,
        operand: &mir::Value,
    ) {
        let mir::Value::Register(id) = operand else {
            return;
        };
        if self.derived_definitions.contains_key(id) {
            *self.derived_uses.entry(*id).or_default() += 1;
        }
        let Some(allocation) = self.allocations.get_mut(id) else {
            return;
        };

        let removable_constant_store = matches!(operation.kind, OperationKind::Store)
            && position == 1
            && matches!(operation.operands[0], mir::Value::Constant(_));
        if removable_constant_store {
            allocation.constant_stores.push((block, index));
        }

        let is_array_constructor = matches!(operation.kind, OperationKind::BuildArray { .. })
            && position + 1 == operation.operands.len();
        let is_bare_function_constructor = matches!(operation.kind, OperationKind::Store)
            && position == 1
            && matches!(operation.operands[0], mir::Value::Function(_));
        let is_drop = matches!(operation.kind, OperationKind::Drop { .. }) && position == 0;
        let is_construction_use = is_array_constructor || is_bare_function_constructor || is_drop;
        if !removable_constant_store {
            if is_construction_use {
                allocation.has_deferred_construction_use = true;
            } else {
                allocation.constant_only_invalid = true;
            }
        }

        if is_array_constructor || is_bare_function_constructor {
            if allocation.constructor.replace((block, index)).is_some() {
                allocation.invalid_construction = true;
            }
        } else if is_drop {
            allocation.drops.push((block, index));
        } else {
            allocation.invalid_construction = true;
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
                allocation.constant_only_invalid = true;
                allocation.invalid_construction = true;
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

    fn dead_constructed_values(&self) -> FxHashMap<BlockId, FxHashSet<usize>> {
        let mut removed: FxHashMap<BlockId, FxHashSet<usize>> = FxHashMap::default();
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

    fn dead_allocas(&self) -> Dead {
        let mut operations: FxHashMap<BlockId, FxHashSet<usize>> = FxHashMap::default();
        for candidate in self.allocations.values() {
            // Constructor/drop uses cease to disqualify the alloca only when that complete resource
            // lifetime is itself selected for removal.
            if candidate.constant_only_invalid
                || (candidate.has_deferred_construction_use
                    && !candidate.has_removable_construction())
            {
                continue;
            }
            let (block, index) = candidate.definition;
            operations.entry(block).or_default().insert(index);
            for (block, index) in &candidate.constant_stores {
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
    fn unread_derived_places(&mut self, func: &Function) -> Vec<(BlockId, usize)> {
        if self.derived_definitions.is_empty() {
            return Vec::new();
        }

        let mut uses = std::mem::take(&mut self.derived_uses);
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
            for operand in &func.block(block).operations()[index].operands {
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
}
