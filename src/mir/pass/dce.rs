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
    if dead.allocas.is_empty() && dead_entries.is_empty() {
        return None;
    }
    for (block, index) in dead_entries {
        dead.operations.entry(block).or_default().insert(index);
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
    allocas: FxHashSet<ValueId>,
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

    Dead {
        allocas: candidates,
        operations,
    }
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization};

    /// The gate example, all the way down: after folding and cleanup, nothing is left but the store
    /// of the result into the return place.
    #[test]
    fn folded_arithmetic_leaves_only_its_result() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let optimized = session.emit_mir("dce", "fn main() -> int { let x = 2 + 3; x * 7 }");
        let main = optimized
            .split("fn main")
            .nth(1)
            .expect("the module defines main");

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
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let optimized = session.emit_mir(
            "dce",
            "fn twice_it(x) { x + x }\n\
             fn use_it(n: int) -> int { twice_it(n) }",
        );
        let caller = optimized
            .split("fn use_it")
            .nth(1)
            .expect("the module defines use_it")
            .split("\nfn ")
            .next()
            .expect("use_it has a body");

        assert!(
            caller.contains("call std::Num<std::int>::add"),
            "the call must have been devirtualized, or there is no dead entry to remove:\n{caller}"
        );
        assert!(
            !caller.contains("dict_entry"),
            "the entry it no longer reads must be gone:\n{caller}"
        );
    }
}
