// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Merging of alpha-equivalent basic-block tails.
//!
//! Lowering keeps the source's control-flow shape. Consequently two arms which compute the same
//! thing still become two blocks, and ordinary CSE cannot see across their mutually exclusive
//! paths. This pass hash-conses complete blocks while treating results defined inside each block by
//! their definition order rather than their function-wide [`ValueId`](mir::ValueId). It redirects
//! edges to one representative; it never moves or duplicates an operation.
//!
//! Source spans are intentionally absent from the key. They describe where either equivalent copy
//! came from, not what it does, and retaining the representative's span is the same diagnostic
//! compromise made whenever optimization removes one of two redundant computations.
//!
//! Source-fallible `invoke` tails are excluded for now. An invoked operation may define a value
//! whose valid scope begins only on its normal edge, so merging it needs a subgraph-level renaming
//! proof rather than this block-local one.

use std::hash::{Hash, Hasher};

use rustc_hash::{FxHashMap, FxHasher};

use crate::{
    containers::DenseBitSet,
    mir::{self, BlockId, Function, edit::FunctionEdit, terminator::TerminatorKind},
    module::id::Id,
};

fn hash_value(
    value: &mir::Value,
    local_results: &FxHashMap<mir::ValueId, usize>,
    state: &mut impl Hasher,
) {
    match value {
        mir::Value::Register(id) if local_results.contains_key(id) => {
            0u8.hash(state);
            local_results[id].hash(state);
        }
        value => {
            1u8.hash(state);
            value.hash(state);
        }
    }
}

fn values_alpha_equivalent(
    left: &mir::Value,
    right: &mir::Value,
    left_results: &FxHashMap<mir::ValueId, usize>,
    right_results: &FxHashMap<mir::ValueId, usize>,
) -> bool {
    match (left, right) {
        (mir::Value::Register(left), mir::Value::Register(right)) => {
            match (left_results.get(left), right_results.get(right)) {
                (Some(left), Some(right)) => left == right,
                (None, None) => left == right,
                _ => false,
            }
        }
        _ => left == right,
    }
}

fn canonical_target(target: BlockId, replacement: &FxHashMap<BlockId, BlockId>) -> BlockId {
    replacement.get(&target).copied().unwrap_or(target)
}

fn block_fingerprint(
    function: &Function,
    block: BlockId,
    replacement: &FxHashMap<BlockId, BlockId>,
    local_results: &mut FxHashMap<mir::ValueId, usize>,
) -> Option<u64> {
    let block = function.block(block);
    let mut state = FxHasher::default();
    block.operations().len().hash(&mut state);
    local_results.clear();
    for operation in block.operations() {
        let (kind, operands) = operation.kind_and_operands();
        kind.hash(&mut state);
        operands.len().hash(&mut state);
        for operand in operands {
            hash_value(operand, local_results, &mut state);
        }
        if let Some(result) = operation.result_id() {
            local_results.insert(result, local_results.len());
        }
    }

    match &block.terminator().kind {
        TerminatorKind::Goto { target } => {
            0u8.hash(&mut state);
            canonical_target(*target, replacement).hash(&mut state);
        }
        TerminatorKind::CondBr {
            condition,
            then_target,
            else_target,
        } => {
            1u8.hash(&mut state);
            hash_value(condition, local_results, &mut state);
            canonical_target(*then_target, replacement).hash(&mut state);
            canonical_target(*else_target, replacement).hash(&mut state);
        }
        TerminatorKind::Invoke { .. } => return None,
        TerminatorKind::Yield { place, resume } => {
            2u8.hash(&mut state);
            hash_value(place, local_results, &mut state);
            canonical_target(*resume, replacement).hash(&mut state);
        }
        TerminatorKind::Return => 3u8.hash(&mut state),
        TerminatorKind::PropagateError => 4u8.hash(&mut state),
        TerminatorKind::FailureDuringCleanup => 5u8.hash(&mut state),
    }
    Some(state.finish())
}

enum Representatives {
    One(BlockId),
    Many(Vec<BlockId>),
}

impl Representatives {
    fn find(&self, mut equivalent: impl FnMut(BlockId) -> bool) -> Option<BlockId> {
        match self {
            Self::One(block) => equivalent(*block).then_some(*block),
            Self::Many(blocks) => blocks.iter().copied().find(|block| equivalent(*block)),
        }
    }

    fn push(&mut self, block: BlockId) {
        match self {
            Self::One(first) => *self = Self::Many(vec![*first, block]),
            Self::Many(blocks) => blocks.push(block),
        }
    }
}

fn blocks_alpha_equivalent(
    function: &Function,
    left: BlockId,
    right: BlockId,
    replacement: &FxHashMap<BlockId, BlockId>,
) -> bool {
    let left = function.block(left);
    let right = function.block(right);
    if left.operations().len() != right.operations().len() {
        return false;
    }
    let mut left_results = FxHashMap::default();
    let mut right_results = FxHashMap::default();
    for (left, right) in left.operations().iter().zip(right.operations()) {
        let (left_kind, left_operands) = left.kind_and_operands();
        let (right_kind, right_operands) = right.kind_and_operands();
        if left_kind != right_kind
            || left_operands.len() != right_operands.len()
            || !left_operands
                .iter()
                .zip(right_operands.iter())
                .all(|(left, right)| {
                    values_alpha_equivalent(left, right, &left_results, &right_results)
                })
        {
            return false;
        }
        match (left.result_id(), right.result_id()) {
            (Some(left), Some(right)) => {
                let ordinal = left_results.len();
                left_results.insert(left, ordinal);
                right_results.insert(right, ordinal);
            }
            (None, None) => {}
            _ => return false,
        }
    }

    match (&left.terminator().kind, &right.terminator().kind) {
        (TerminatorKind::Goto { target: left }, TerminatorKind::Goto { target: right }) => {
            canonical_target(*left, replacement) == canonical_target(*right, replacement)
        }
        (
            TerminatorKind::CondBr {
                condition: left_condition,
                then_target: left_then,
                else_target: left_else,
            },
            TerminatorKind::CondBr {
                condition: right_condition,
                then_target: right_then,
                else_target: right_else,
            },
        ) => {
            values_alpha_equivalent(
                left_condition,
                right_condition,
                &left_results,
                &right_results,
            ) && canonical_target(*left_then, replacement)
                == canonical_target(*right_then, replacement)
                && canonical_target(*left_else, replacement)
                    == canonical_target(*right_else, replacement)
        }
        (TerminatorKind::Invoke { .. }, _) | (_, TerminatorKind::Invoke { .. }) => false,
        (
            TerminatorKind::Yield {
                place: left_place,
                resume: left_resume,
            },
            TerminatorKind::Yield {
                place: right_place,
                resume: right_resume,
            },
        ) => {
            values_alpha_equivalent(left_place, right_place, &left_results, &right_results)
                && canonical_target(*left_resume, replacement)
                    == canonical_target(*right_resume, replacement)
        }
        (TerminatorKind::Return, TerminatorKind::Return)
        | (TerminatorKind::PropagateError, TerminatorKind::PropagateError)
        | (TerminatorKind::FailureDuringCleanup, TerminatorKind::FailureDuringCleanup) => true,
        _ => false,
    }
}

fn reachable_blocks(function: &Function) -> DenseBitSet {
    let mut reachable = DenseBitSet::with_capacity(function.blocks().count());
    let mut pending = vec![
        function
            .blocks()
            .next()
            .expect("a canonical MIR function has an entry block"),
    ];
    while let Some(block) = pending.pop() {
        if reachable.contains(block.as_index()) {
            continue;
        }
        reachable.insert(block.as_index());
        pending.extend(function.block(block).terminator().successors());
    }
    reachable
}

/// Merges complete alpha-equivalent blocks and simplifies branches whose two edges then coincide.
pub(crate) fn merge_equivalent_tails(function: &Function) -> Option<Function> {
    if function.blocks().count() < 2 {
        return None;
    }

    let mut representatives = FxHashMap::<u64, Representatives>::default();
    let mut replacement = FxHashMap::<BlockId, BlockId>::default();
    let mut local_results = FxHashMap::default();
    // An unreachable block cannot safely represent a reachable one: a shared successor may use a
    // result defined by the reachable candidate, which only dominates that successor while the
    // other predecessor remains unreachable.
    let reachable = reachable_blocks(function);
    // Ordinary forward branch tails occur later in canonical block order. Walking backwards means
    // their representatives are already known, so two multi-block acyclic tails compare equal as
    // soon as their final blocks do. Backedges stay conservative: this is not graph isomorphism.
    let mut blocks: Vec<_> = function
        .blocks()
        .skip(1)
        .filter(|block| reachable.contains(block.as_index()))
        .collect();
    blocks.reverse();
    for block in blocks {
        let Some(fingerprint) =
            block_fingerprint(function, block, &replacement, &mut local_results)
        else {
            continue;
        };
        let representative = representatives.get(&fingerprint).and_then(|candidates| {
            candidates
                .find(|candidate| blocks_alpha_equivalent(function, block, candidate, &replacement))
        });
        if let Some(representative) = representative {
            replacement.insert(block, representative);
        } else if let Some(candidates) = representatives.get_mut(&fingerprint) {
            candidates.push(block);
        } else {
            representatives.insert(fingerprint, Representatives::One(block));
        }
    }

    let has_equal_target_branch = function
        .blocks()
        .filter(|block| reachable.contains(block.as_index()))
        .any(|block| {
            matches!(
                function.block(block).terminator().kind,
                TerminatorKind::CondBr {
                    then_target,
                    else_target,
                    ..
                } if then_target == else_target
            )
        });
    if replacement.is_empty() && !has_equal_target_branch {
        return None;
    }

    let mut edit = FunctionEdit::new(function.clone());
    let blocks: Vec<_> = edit.blocks().collect();
    for block in blocks {
        let terminator = &mut edit.block_mut(block).terminator;
        match &mut terminator.kind {
            TerminatorKind::Goto { target } => {
                *target = replacement.get(target).copied().unwrap_or(*target);
            }
            TerminatorKind::CondBr {
                then_target,
                else_target,
                ..
            } => {
                *then_target = replacement
                    .get(then_target)
                    .copied()
                    .unwrap_or(*then_target);
                *else_target = replacement
                    .get(else_target)
                    .copied()
                    .unwrap_or(*else_target);
            }
            TerminatorKind::Invoke { normal, error, .. } => {
                *normal = replacement.get(normal).copied().unwrap_or(*normal);
                *error = replacement.get(error).copied().unwrap_or(*error);
            }
            TerminatorKind::Yield { resume, .. } => {
                *resume = replacement.get(resume).copied().unwrap_or(*resume);
            }
            TerminatorKind::Return
            | TerminatorKind::PropagateError
            | TerminatorKind::FailureDuringCleanup => {}
        }
        if let TerminatorKind::CondBr {
            then_target,
            else_target,
            ..
        } = terminator.kind
            && then_target == else_target
        {
            terminator.kind = TerminatorKind::Goto {
                target: then_target,
            };
        }
    }

    edit.remove_unreachable_blocks();
    edit.merge_blocks_into_predecessors();
    edit.prune_constants();
    Some(edit.finish_unverified())
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, Location, MirOptimization,
        hir::value::LiteralValue,
        mir::{Operation, ParameterKind, builder::FunctionBuilder, terminator::Terminator},
        std::{logic::bool_type, math::int_type},
    };

    use super::merge_equivalent_tails;

    fn optimized_body(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("tail_merge", src)
    }

    #[test]
    fn alpha_equivalent_branch_arms_are_merged() {
        let body = optimized_body("fn f(x: int) -> int { if x > 0 { x + 1 } else { x + 1 } }");
        assert!(
            !body.contains("condbr"),
            "the equivalent arms make the predicate dead:\n{body}"
        );
        assert_eq!(
            body.matches("Num<std::int>::add#impl").count(),
            1,
            "the common tail must be retained once:\n{body}"
        );
        assert!(
            !body.contains("Ord<std::int>::cmp#impl"),
            "proven-call DCE must collect the dead predicate:\n{body}"
        );
    }

    #[test]
    fn different_branch_arms_are_not_merged() {
        let body = optimized_body("fn f(x: int) -> int { if x > 0 { x + 1 } else { x + 2 } }");
        assert!(
            body.contains("condbr"),
            "different computations must retain their branch:\n{body}"
        );
        assert_eq!(
            body.matches("Num<std::int>::add#impl").count(),
            2,
            "both distinct arms must survive:\n{body}"
        );
    }

    #[test]
    fn equivalent_multi_block_acyclic_tails_are_merged_inside_out() {
        let body = optimized_body(
            "fn f(x: int, c: bool, d: bool) -> int {\n\
                 if c { if d { x + 1 } else { x + 2 } }\n\
                 else { if d { x + 1 } else { x + 2 } }\n\
             }",
        );
        assert_eq!(
            body.matches("condbr").count(),
            1,
            "the duplicated inner diamond must survive only once:\n{body}"
        );
        assert_eq!(
            body.matches("Num<std::int>::add#impl").count(),
            2,
            "each distinct inner result is computed once:\n{body}"
        );
    }

    /// Equal arms make the branch result irrelevant, but purity alone does not make its predicate
    /// speculatable: deleting this recursive call would turn divergence into a return.
    #[test]
    fn a_dead_arbitrary_pure_predicate_is_retained() {
        let body = optimized_body(
            "fn diverges(c: bool) -> bool { diverges(c) }\n\
             fn f(x: int, c: bool) -> int {\n\
                 if diverges(c) { x + 1 } else { x + 1 }\n\
             }",
        );
        assert!(
            !body.contains("condbr"),
            "the equivalent arms do not need a branch:\n{body}"
        );
        assert!(
            body.contains("call tail_merge::diverges"),
            "the possibly divergent predicate must still execute:\n{body}"
        );
    }

    #[test]
    fn an_unreachable_block_cannot_represent_a_reachable_one() {
        let span = Location::new_synthesized();
        let mut builder =
            FunctionBuilder::new("unreachable_representative".into(), Default::default());
        let ret = builder.add_parameter(int_type(), ParameterKind::Return);
        let entry = builder.add_block();
        let reachable = builder.add_block();
        let successor = builder.add_block();
        // Put the unreachable candidate last: the backwards scan would prefer it without the
        // reachability guard.
        let unreachable = builder.add_block();

        let slot = builder
            .append_operation(entry, Operation::alloca(span, int_type()))
            .unwrap();
        builder.set_terminator(entry, Terminator::goto(span, reachable));
        let reachable_result = builder
            .append_operation(reachable, Operation::load(span, slot.clone()))
            .unwrap();
        builder.set_terminator(reachable, Terminator::goto(span, successor));
        builder.append_operation(
            successor,
            Operation::store(span, reachable_result, crate::mir::Value::Parameter(ret)),
        );
        builder.set_terminator(successor, Terminator::ret(span));
        builder.append_operation(unreachable, Operation::load(span, slot));
        builder.set_terminator(unreachable, Terminator::goto(span, successor));

        let session = CompilerSession::new();
        let function = builder.finish(session.module_env());
        assert!(
            merge_equivalent_tails(&function).is_none(),
            "the only equivalent candidate is unreachable"
        );
    }

    #[test]
    fn simplifying_a_branch_prunes_its_dead_condition_constant() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut builder = FunctionBuilder::new("prune_condition".into(), Default::default());
        let condition = builder.add_constant(bool_type(), LiteralValue::new_native(true), &env);
        let entry = builder.add_block();
        let exit = builder.add_block();
        builder.set_terminator(
            entry,
            Terminator::cond_br(span, crate::mir::Value::Constant(condition), exit, exit),
        );
        builder.set_terminator(exit, Terminator::ret(span));

        let function = builder.finish(env);
        let merged = merge_equivalent_tails(&function).expect("the equal branch targets simplify");
        assert!(merged.constants().is_empty());
    }
}
