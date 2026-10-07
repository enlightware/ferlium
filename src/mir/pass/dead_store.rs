// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Elimination of overwritten whole-place stores to local `TrivialCopy` storage.
//!
//! This is deliberately narrower than general dead-store elimination. A candidate is a direct
//! `alloca` of a concrete `TrivialCopy` type. Its permitted exact-root roles are whole-place
//! `store`/`memcpy` and infallible call-result writes, plus `load`/`memcpy`/`move` reads. A
//! projection, an escaping call argument, or a non-copy ownership operation rejects the allocation.
//! Backward liveness then determines whether old contents can be read before a later whole-place
//! write on any path. A store whose written value is not live is dead.

use rustc_hash::{FxHashMap, FxHashSet};

use super::{
    local_cells::{Access, Allocation, LocalCells, Read, Write, access},
    site::OperationIndex,
};
use crate::{
    mir::{self, BlockId, Function, Operation, OperationKind, ValueId, edit::FunctionEdit},
    module::{ModuleEnv, id::Id},
    types::type_properties::concrete_type_is_trivial_copy,
};

/// Removes stores to a local whole place that every following path overwrites before reading.
pub(crate) fn remove_overwritten_trivial_copy_stores(
    func: &Function,
    env: ModuleEnv<'_>,
) -> Option<Function> {
    // We intentionally do not reason through aliases. The access whitelist is fail-safe: an
    // operand in a new or unmodelled operation kind rejects the root rather than broadening this
    // proof. Unlike dataflow's escape census, call arguments are not admitted by convention: this
    // pass admits only the exact direct roles listed above. A source-fallible call is an `Invoke`
    // terminator. Its result place is deliberately not a DS write: the error edge needs a separate
    // control-flow/cleanup proof.
    let cells = LocalCells::of_matching(func, |_, allocation| {
        let &Allocation::Value { ty, .. } = allocation else {
            return false;
        };
        concrete_type_is_trivial_copy(ty, &env)
    });
    let candidates: FxHashSet<ValueId> = cells
        .iter()
        .filter(|cell| {
            cells.uses(cell).iter().all(|cell_use| {
                !cell_use.in_terminator(func)
                    && (is_whole_place_write(cell_use.access)
                        || is_exact_place_read(cell_use.access))
            })
        })
        .map(|cell| cell.id)
        .collect();
    if candidates.is_empty() {
        return None;
    }

    let consuming_results = func
        .blocks()
        .flat_map(|block| func.block(block).operations())
        .filter(|operation| operation.result_requires_consuming_use())
        .filter_map(Operation::result_id)
        .collect::<FxHashSet<_>>();

    let block_count = func.blocks().count();
    let mut predecessors = vec![Vec::new(); block_count];
    for block in func.blocks() {
        for successor in func.block(block).terminator().successors() {
            predecessors[successor.as_index()].push(block);
        }
    }

    // `live_in[b]` is the set of candidate roots whose incoming contents may be read before an
    // overwrite on a path starting at b.  A worklist makes loops linear in the number of newly-live
    // root/block pairs rather than repeatedly sweeping the complete CFG.
    let mut live_in = vec![FxHashSet::default(); block_count];
    let mut pending: Vec<BlockId> = func.blocks().collect();
    while let Some(block) = pending.pop() {
        let mut live = FxHashSet::default();
        for successor in func.block(block).terminator().successors() {
            live.extend(live_in[successor.as_index()].iter().copied());
        }
        transfer_block(
            func,
            block,
            &candidates,
            &consuming_results,
            &mut live,
            None,
        );
        if live == live_in[block.as_index()] {
            continue;
        }
        live_in[block.as_index()] = live;
        pending.extend(predecessors[block.as_index()].iter().copied());
    }

    let mut removed = FxHashMap::<BlockId, FxHashSet<OperationIndex>>::default();
    for block in func.blocks() {
        let mut live = FxHashSet::default();
        for successor in func.block(block).terminator().successors() {
            live.extend(live_in[successor.as_index()].iter().copied());
        }
        transfer_block(
            func,
            block,
            &candidates,
            &consuming_results,
            &mut live,
            Some(&mut removed),
        );
    }
    if removed.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for (block, indices) in removed {
        let mut index = 0;
        edit.block_mut(block).operations.retain(|_| {
            let keep = !indices.contains(&OperationIndex::from_index(index));
            index += 1;
            keep
        });
    }
    edit.prune_constants();
    Some(edit.finish_unverified())
}

/// Transfers liveness through one block, optionally recording stores dead at their program point.
fn transfer_block(
    func: &Function,
    block: BlockId,
    candidates: &FxHashSet<ValueId>,
    consuming_results: &FxHashSet<ValueId>,
    live: &mut FxHashSet<ValueId>,
    mut removed: Option<&mut FxHashMap<BlockId, FxHashSet<OperationIndex>>>,
) {
    for (index, operation) in func.block(block).operations().iter().enumerate().rev() {
        let candidate = |operand: &mir::Value| match operand {
            mir::Value::Register(root) if candidates.contains(root) => Some(*root),
            _ => None,
        };
        for (position, operand) in operation.operands.iter().enumerate() {
            if let Some(root) = candidate(operand)
                && is_whole_place_write(access(operation, position))
            {
                if matches!(operation.kind, OperationKind::Store)
                    && !store_source_requires_consuming_use(operation, consuming_results)
                    && !live.contains(&root)
                    && let Some(removed) = &mut removed
                {
                    removed
                        .entry(block)
                        .or_default()
                        .insert(OperationIndex::from_index(index));
                }
                live.remove(&root);
            }
        }
        for (position, operand) in operation.operands.iter().enumerate() {
            if let Some(root) = candidate(operand)
                && is_exact_place_read(access(operation, position))
            {
                live.insert(root);
            }
        }
    }
}

/// Whether removing this store would orphan an owned value register.
fn store_source_requires_consuming_use(
    operation: &Operation,
    consuming_results: &FxHashSet<ValueId>,
) -> bool {
    matches!(
        operation.operands.first(),
        Some(mir::Value::Register(value)) if consuming_results.contains(value)
    )
}

/// Whether `access` is a whole-place result write that replaces the old contents.
///
/// `memcpy` is a representation copy, not an ownership action.
fn is_whole_place_write(access: Access) -> bool {
    matches!(
        access,
        Access::Write(Write::Store | Write::Copy | Write::CallResult)
    )
}

/// Whether `access` reads a candidate's complete `TrivialCopy` representation.
///
/// A representation copy and a move out to the caller both observe the stored value. They do not
/// leave an ownership obligation for a `TrivialCopy` root, unlike an arbitrary move. We do not
/// model a move-out's later absence: retaining a store longer is conservative, and recognizing the
/// read is necessary for the ordinary final `move local to return` shape.
fn is_exact_place_read(access: Access) -> bool {
    matches!(
        access,
        Access::Read(Read::Load | Read::Copy) | Access::MoveOut(_)
    )
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    use crate::{CompilerSession, MirOptimization};

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("dead_store", src)
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

    #[test]
    fn removes_an_initial_store_overwritten_on_every_branch() {
        let module = optimized(
            "fn select(b: bool, x: int) -> int { let mut y = 0; if b { y = x } else { y = x + 1 }; y }",
        );
        let body = body_of(&module, "select");
        assert!(
            !body.contains("int = 0"),
            "the initial zero must become unreferenced and leave the constant pool:\n{body}"
        );
    }

    #[test]
    fn retains_an_initial_store_read_through_an_exact_copy() {
        let module = optimized(indoc! {"
            fn select(b: bool) -> int {
                let mut y = 7;
                if b { y = 1 };
                let z = y;
                if z == 0 { y = 2 };
                y
            }
        "});
        let body = body_of(&module, "select");
        assert!(
            body.contains("int = 7"),
            "an exact copy reading the old value must retain its initialization:\n{body}"
        );
    }

    #[test]
    fn retains_a_store_read_on_a_loop_back_edge() {
        let module = optimized(indoc! {"
            fn loop_read(mut n: int) -> int {
                let mut y = 7;
                loop {
                    if n <= 0 { break };
                    let z = y;
                    if z < 0 { y = 12 };
                    y = 11;
                    n = n - 1;
                };
                0
            }
        "});
        let body = body_of(&module, "loop_read");
        assert!(
            body.contains("int = 11"),
            "a store read on a later loop iteration must remain live across the back edge:\n{body}"
        );
    }

    #[test]
    fn retains_an_overwritten_store_that_consumes_a_variant() {
        // A `Variant` may have a `TrivialCopy` representation while its freshly constructed result
        // is still an owned register. Removing its consuming store would violate MIR ownership.
        optimized(
            "fn overwrite(b: bool) { let mut x = Some(1); if b { x = None } else { x = None } }",
        );
    }

    #[test]
    fn refuses_a_projected_place() {
        let module = optimized(
            "fn first(b: bool) -> int { let mut pair = (0, 1); if b { pair = (2, 3) }; pair.0 }",
        );
        let body = body_of(&module, "first");
        assert!(
            body.contains("store @c0"),
            "projected storage is outside the exact-place proof:\n{body}"
        );
    }
}
