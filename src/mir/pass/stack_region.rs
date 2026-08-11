// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Removal of stack markers that record a frontier already recorded.
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
//! frontier, intersected at joins. Anything that may leave frame storage clears it; that predicate
//! is [`dce`]'s, so the two passes cannot drift on what grows a frame.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    mir::{
        self, BlockId, Function, OperationKind, edit::FunctionEdit, edit::successors,
        terminator::TerminatorKind, value::ValueId,
    },
    module::{ModuleEnv, id::Id},
};

use super::dce::may_leave_frame_storage;

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
            std::cmp::Ordering::Equal => {
                result.push(left[i]);
                i += 1;
                j += 1;
            }
            std::cmp::Ordering::Less => i += 1,
            std::cmp::Ordering::Greater => j += 1,
        }
    }
    result
}

/// Canonicalizes redundant stack markers and drops restores that reclaim nothing, returning a
/// rewritten function if anything changed.
pub(crate) fn remove_redundant_stack_markers(
    func: &Function,
    env: ModuleEnv<'_>,
) -> Option<Function> {
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

    let entry_states = analyze(func);

    // A redundant save's marker is replaced by one already holding the same frontier. The
    // substitution is justified where it is *decided* — the two markers are equal integers there —
    // and both are immutable afterwards, so it holds at every use. Dominance holds too: a marker in
    // the state arrived on every path to this point, so its definition dominates this one's.
    let mut substitution: FxHashMap<ValueId, ValueId> = FxHashMap::default();
    let mut dead: FxHashMap<BlockId, FxHashSet<usize>> = FxHashMap::default();
    for block in func.blocks() {
        let Some(state) = entry_states.get(&block) else {
            continue;
        };
        let mut state = state.clone();
        for (index, operation) in func.block(block).operations().iter().enumerate() {
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
                    if let Some(mir::Value::Register(marker)) = operation.operands.first()
                        && holds(&state, *marker)
                    {
                        dead.entry(block).or_default().insert(index);
                    }
                }
                _ => {}
            }
            step(operation, &mut state);
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
            let keep = !indices.contains(&index);
            index += 1;
            keep
        });
    }
    Some(edit.finish(env))
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
fn analyze(func: &Function) -> FxHashMap<BlockId, Frontier> {
    let mut entry_states: FxHashMap<BlockId, Frontier> = FxHashMap::default();
    entry_states.insert(func.entry(), Frontier::default());

    // Blocks are visited in index order until nothing changes, as `dataflow` does: bodies are
    // small, and the state can only shrink, so this settles in a couple of sweeps.
    let mut changed = true;
    while changed {
        changed = false;
        for block in func.blocks() {
            let Some(entry) = entry_states.get(&block).cloned() else {
                continue;
            };
            let mut state = entry;
            let basic_block = func.block(block);
            for operation in basic_block.operations() {
                step(operation, &mut state);
            }
            if let TerminatorKind::Invoke { operation, .. } = &basic_block.terminator().kind {
                step(operation, &mut state);
            }
            for successor in successors(basic_block.terminator()) {
                let updated = match entry_states.get(&successor) {
                    Some(existing) => intersect(existing, &state),
                    None => state.clone(),
                };
                if entry_states.get(&successor) != Some(&updated) {
                    entry_states.insert(successor, updated);
                    changed = true;
                }
            }
        }
    }
    entry_states
}

/// Advances the frontier state across one operation.
fn step(operation: &mir::Operation, state: &mut Frontier) {
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
            if may_leave_frame_storage(operation) {
                state.clear();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization};

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("stack", src)
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
