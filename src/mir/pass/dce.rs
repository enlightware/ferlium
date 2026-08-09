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
//! Folding replaces `call f(a, b, ret)` with `store @cN to ret`, which leaves the arguments' own
//! `alloca`s and stores in place: correct, since nothing reads them, but they still cost a cell and
//! a write at run time and they bury the result in noise when the MIR is read.
//!
//! This is **not** general dead-code elimination. It removes an `alloca` only when *every* use of it
//! is as the destination of a `store` whose value is a pool constant, and then removes those stores
//! with it. Two properties make that safe without any ownership analysis:
//!
//! - a constant is trivially copyable, so storing one creates no drop obligation and deleting the
//!   store discards nothing that must be dropped;
//! - the value operand is not a register, so no owned register loses its single consuming use —
//!   which the verifier would reject, and which is the trap any wider rule falls into first.
//!
//! Constants left unreferenced by the removed stores are dropped from the pool with them.
//!
//! Anything else about the place — a `load`, a `subfield`, a `drop`, a call argument, a store of a
//! register — disqualifies it. Widening the rule means proving the drop obligation is discharged,
//! and should happen only against the whole corpus.

#![allow(dead_code)]

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    mir::{
        self, BlockId, Function, OperationKind, edit::FunctionEdit, terminator::TerminatorKind,
        value::ValueId,
    },
    module::ModuleEnv,
};

/// Removes dead storage scaffolding, returning a rewritten function if anything was removed.
pub(crate) fn remove_dead_storage(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    let mut dead = dead_allocas(func);
    let dead_entries = unread_dict_entries(func);
    for (block, index) in dead_entries {
        dead.operations.entry(block).or_default().insert(index);
    }
    remove_empty_local_stack_regions(func, &mut dead.operations);
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
    Some(edit.finish(env))
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
    removed: &mut FxHashMap<BlockId, FxHashSet<usize>>,
) {
    let mut restore_uses: FxHashMap<ValueId, usize> = FxHashMap::default();
    for block in func.blocks() {
        for operation in func.block(block).operations() {
            if matches!(operation.kind, OperationKind::StackRestore)
                && let Some(mir::Value::Register(marker)) = operation.operands.first()
            {
                *restore_uses.entry(*marker).or_default() += 1;
            }
        }
    }

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
fn may_leave_frame_storage(operation: &mir::Operation) -> bool {
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

/// The `dict_entry` operations nothing reads any more.
///
/// **Devirtualization is what makes these dead.** It rewrites a call through a resolved dictionary
/// entry to name the callee directly, which removes the only use the entry usually had — so a
/// successful devirtualization leaves an operation computing a place no one reads. Over
/// `sudoku.fer` that is 86 of the 88 entries taken from a constant dictionary.
///
/// Removing one is safe without any of the analysis the `alloca` rule needs: `dict_entry` reads
/// evidence rather than storage, has no side effect, and yields a *place* rather than an owned
/// value — so an unread one discharges no drop obligation and consumes nothing. One pass suffices
/// because its operand is a dictionary or a parameter, never another entry's result, so removing one
/// can never make another dead.
fn unread_dict_entries(func: &Function) -> Vec<(BlockId, usize)> {
    let mut used: FxHashSet<ValueId> = FxHashSet::default();
    let mut note = |operand: &mir::Value| {
        if let mir::Value::Register(id) = operand {
            used.insert(*id);
        }
    };
    for block in func.blocks() {
        let basic_block = func.block(block);
        for operation in basic_block.operations() {
            if matches!(operation.kind, OperationKind::DictEntry { .. }) {
                // Its own operand, not its result: an entry never reads another entry.
                continue;
            }
            operation.operands.iter().for_each(&mut note);
        }
        match &basic_block.terminator().kind {
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

    let mut dead = Vec::new();
    for block in func.blocks() {
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            if matches!(operation.kind, OperationKind::DictEntry { .. })
                && let Some(result) = operation.result_id()
                && !used.contains(&result)
            {
                dead.push((block, index));
            }
        }
    }
    dead
}

/// The `alloca`s that can go, and the operations to remove with them.
struct Dead {
    /// Operation indices to remove, per block.
    operations: FxHashMap<BlockId, FxHashSet<usize>>,
}

fn dead_allocas(func: &Function) -> Dead {
    // Every `alloca` starts as a candidate; a use the rule does not allow removes it.
    let mut candidates: FxHashSet<ValueId> = FxHashSet::default();
    for block in func.blocks() {
        for operation in func.block(block).operations() {
            if matches!(operation.kind, OperationKind::Alloca { .. })
                && let Some(result) = operation.result_id()
            {
                candidates.insert(result);
            }
        }
    }

    // Stores that would go with their destination, and the uses that disqualify one.
    let mut stores: FxHashMap<ValueId, Vec<(BlockId, usize)>> = FxHashMap::default();
    let disqualify = |operand: &mir::Value, candidates: &mut FxHashSet<ValueId>| {
        if let mir::Value::Register(id) = operand {
            candidates.remove(id);
        }
    };

    for block in func.blocks() {
        let basic_block = func.block(block);
        for (index, operation) in basic_block.operations().iter().enumerate() {
            let removable_store = matches!(operation.kind, OperationKind::Store)
                && matches!(operation.operands[0], mir::Value::Constant(_));
            for (position, operand) in operation.operands.iter().enumerate() {
                // The destination of a constant store is the one use that keeps a candidate alive.
                if removable_store && position == 1 {
                    if let mir::Value::Register(id) = operand {
                        stores.entry(*id).or_default().push((block, index));
                    }
                    continue;
                }
                disqualify(operand, &mut candidates);
            }
        }
        match &basic_block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => {
                for operand in operation.operands.iter() {
                    disqualify(operand, &mut candidates);
                }
            }
            TerminatorKind::CondBr { condition, .. } => disqualify(condition, &mut candidates),
            TerminatorKind::Yield { place, .. } => disqualify(place, &mut candidates),
            TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::PropagateError
            | TerminatorKind::FailureDuringCleanup => {}
        }
    }

    // What survives is dead: its storage is written with constants and never read.
    let mut operations: FxHashMap<BlockId, FxHashSet<usize>> = FxHashMap::default();
    for block in func.blocks() {
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            if matches!(operation.kind, OperationKind::Alloca { .. })
                && let Some(result) = operation.result_id()
                && candidates.contains(&result)
            {
                operations.entry(block).or_default().insert(index);
            }
        }
    }
    for alloca in &candidates {
        for (block, index) in stores.get(alloca).into_iter().flatten() {
            operations.entry(*block).or_default().insert(*index);
        }
    }

    Dead { operations }
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization};

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("dce", src)
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
            "fn through_local(x: int) -> int { let y = x; y }\n\
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
