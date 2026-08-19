// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Simplification of shared basic-block tails.
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
//!
//! An empty block is the limiting case in the other direction: it holds nothing to execute, so its
//! terminator can be folded into its predecessors without duplicating an operation. How far that
//! goes depends on the terminator. A `goto` is folded into *every* predecessor edge, whatever its
//! kind, because an edge can name any block. An operand-free terminal — `return`, error propagation
//! or cleanup failure — can only replace a predecessor's own `goto`: a conditional or invoke edge
//! must name a block, and has nowhere to put a terminal instead.

use std::hash::{Hash, Hasher};

use rustc_hash::{FxHashMap, FxHasher};

use crate::{
    containers::{DenseBitSet, SVec2},
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

/// The result of simplifying tails, including whether the rewrite can have made values dead.
pub(crate) struct SimplifiedTails {
    pub(crate) body: Function,
    pub(crate) exposed_dead_code: bool,
}

fn is_operand_free_terminal(kind: &TerminatorKind) -> bool {
    matches!(
        kind,
        TerminatorKind::Return
            | TerminatorKind::PropagateError
            | TerminatorKind::FailureDuringCleanup
    )
}

fn is_empty_terminal_block(function: &Function, block: BlockId) -> bool {
    let block = function.block(block);
    block.operations().is_empty() && is_operand_free_terminal(&block.terminator().kind)
}

fn is_empty_forwarding_block(function: &Function, block: BlockId) -> bool {
    let candidate = function.block(block);
    candidate.operations().is_empty()
        && matches!(candidate.terminator().kind, TerminatorKind::Goto { target } if target != block)
}

/// Where an edge to `target` actually arrives: an empty block whose terminator is a jump executes
/// nothing, so the edge carries straight on through it.
///
/// `limit` is the function's block count, which bounds any acyclic chain and so doubles as the
/// cycle guard. A cycle of empty jumps is unreachable code shaped like an infinite loop; exhausting
/// the bound leaves the edge exactly where it was rather than picking an arbitrary block in it.
fn forwarded_target(edit: &FunctionEdit, target: BlockId, limit: usize) -> BlockId {
    let mut current = target;
    for _ in 0..limit {
        let block = edit.block(current);
        if !block.operations.is_empty() {
            return current;
        }
        match block.terminator.kind {
            TerminatorKind::Goto { target } if target != current => current = target,
            _ => return current,
        }
    }
    target
}

/// Folds the jump of every empty forwarding block into the edges reaching it, and collapses a
/// conditional whose two edges land on the same block. Answers whether a conditional collapsed,
/// which is what can leave its condition unread.
///
/// This applies to every predecessor edge kind, unlike the terminal folding below: an edge names a
/// block, and forwarding only changes *which* block it names.
fn fold_empty_forwarding_blocks(edit: &mut FunctionEdit) -> bool {
    let blocks: Vec<_> = edit.blocks().collect();
    let limit = blocks.len();
    let mut collapsed = false;
    for block in blocks {
        // Resolving both edges before taking the mutable borrow keeps the walk reading a body no
        // rewrite has touched. Chains resolve completely, so the order blocks are visited in
        // cannot change the outcome.
        let successors: SVec2<_> = edit.block(block).terminator.successors().collect();
        let forwarded: SVec2<_> = successors
            .iter()
            .map(|&target| forwarded_target(edit, target, limit))
            .collect();
        if forwarded == successors {
            continue;
        }
        let mut forwarded = forwarded.into_iter();
        let mut next = || forwarded.next().expect("one target per successor");
        let terminator = &mut edit.block_mut(block).terminator.kind;
        match terminator {
            TerminatorKind::Goto { target } => *target = next(),
            TerminatorKind::CondBr {
                then_target,
                else_target,
                ..
            } => {
                *then_target = next();
                *else_target = next();
            }
            TerminatorKind::Invoke { normal, error, .. } => {
                *normal = next();
                *error = next();
            }
            TerminatorKind::Yield { resume, .. } => *resume = next(),
            TerminatorKind::Return
            | TerminatorKind::PropagateError
            | TerminatorKind::FailureDuringCleanup => {}
        }
        if let TerminatorKind::CondBr {
            then_target,
            else_target,
            ..
        } = *terminator
            && then_target == else_target
        {
            *terminator = TerminatorKind::Goto {
                target: then_target,
            };
            collapsed = true;
        }
    }
    collapsed
}

fn fold_empty_terminal_successors(edit: &mut FunctionEdit) {
    // Ordinary acyclic successors follow their predecessors in canonical block order. Visiting
    // backwards propagates a terminal through an empty jump chain in this one scan.
    let mut blocks: Vec<_> = edit.blocks().collect();
    blocks.reverse();
    for block in blocks {
        let target = match edit.block(block).terminator.kind {
            TerminatorKind::Goto { target } => target,
            _ => continue,
        };
        let terminal = {
            let target = edit.block(target);
            if target.operations.is_empty() && is_operand_free_terminal(&target.terminator.kind) {
                target.terminator.clone()
            } else {
                continue;
            }
        };
        edit.block_mut(block).terminator = terminal;
    }
}

/// Merges complete alpha-equivalent blocks, collapses equal-target branches and folds shared empty
/// exit blocks into their predecessors.
pub(crate) fn simplify_tails(function: &Function) -> Option<SimplifiedTails> {
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
    let mut has_empty_terminal_successor = match function.block(function.entry()).terminator().kind
    {
        TerminatorKind::Goto { target } => is_empty_terminal_block(function, target),
        _ => false,
    };
    for block in blocks {
        if let TerminatorKind::Goto { target } = function.block(block).terminator().kind {
            has_empty_terminal_successor |= is_empty_terminal_block(function, target);
        }
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
    let has_empty_forwarding_block = function
        .blocks()
        .skip(1)
        .filter(|block| reachable.contains(block.as_index()))
        .any(|block| is_empty_forwarding_block(function, block));
    let mut exposed_dead_code = !replacement.is_empty() || has_equal_target_branch;
    if !exposed_dead_code && !has_empty_terminal_successor && !has_empty_forwarding_block {
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

    // Before the terminal folding, which reads a `goto` chain one link at a time: bypassing the
    // empty links first hands it the block that actually terminates.
    exposed_dead_code |= fold_empty_forwarding_blocks(&mut edit);
    fold_empty_terminal_successors(&mut edit);
    edit.remove_unreachable_blocks();
    edit.merge_blocks_into_predecessors();
    edit.prune_constants();
    Some(SimplifiedTails {
        body: edit.finish_unverified(),
        exposed_dead_code,
    })
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, Location, MirOptimization,
        hir::value::LiteralValue,
        mir::{
            Operation, ParameterKind,
            builder::FunctionBuilder,
            terminator::{Terminator, TerminatorKind},
        },
        std::{logic::bool_type, math::int_type},
    };

    use super::simplify_tails;

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
            simplify_tails(&function).is_none(),
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
        let merged = simplify_tails(&function).expect("the equal branch targets simplify");
        assert!(merged.body.constants().is_empty());
    }

    /// A conditional edge cannot carry a terminal, but it can carry a jump: an empty block which
    /// only jumps onwards is bypassed by every predecessor edge, whatever its kind.
    #[test]
    fn an_empty_forwarding_block_is_bypassed_by_a_conditional_edge() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut builder = FunctionBuilder::new("empty_forwarding".into(), Default::default());
        let condition = builder.add_constant(bool_type(), LiteralValue::new_native(true), &env);
        let entry = builder.add_block();
        let arm = builder.add_block();
        let forwarding = builder.add_block();
        let join = builder.add_block();

        builder.set_terminator(
            entry,
            Terminator::cond_br(
                span,
                crate::mir::Value::Constant(condition),
                arm,
                forwarding,
            ),
        );
        // An operation in each of the two surviving blocks keeps them out of the reach of every
        // other rewrite here: they are neither equivalent to one another nor empty.
        builder
            .append_operation(arm, Operation::alloca(span, int_type()))
            .unwrap();
        builder.set_terminator(arm, Terminator::goto(span, join));
        builder.set_terminator(forwarding, Terminator::goto(span, join));
        builder
            .append_operation(join, Operation::alloca(span, int_type()))
            .unwrap();
        builder.set_terminator(join, Terminator::ret(span));

        let function = builder.finish(env);
        let simplified = simplify_tails(&function).expect("the empty block can be bypassed");
        let body = simplified.body;
        assert_eq!(
            body.blocks().count(),
            3,
            "the block holding nothing but a jump must be gone"
        );
        assert!(
            body.blocks().all(|block| {
                let block = body.block(block);
                !block.operations().is_empty()
                    || !matches!(block.terminator().kind, TerminatorKind::Goto { .. })
            }),
            "no empty forwarding block may remain"
        );
    }

    #[test]
    fn a_shared_empty_return_is_folded_into_its_predecessors() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut builder = FunctionBuilder::new("fold_return".into(), Default::default());
        let ret = builder.add_parameter(int_type(), ParameterKind::Return);
        let condition = builder.add_constant(bool_type(), LiteralValue::new_native(true), &env);
        let one = builder.add_constant(int_type(), LiteralValue::new_native(1_isize), &env);
        let two = builder.add_constant(int_type(), LiteralValue::new_native(2_isize), &env);
        let entry = builder.add_block();
        let left = builder.add_block();
        let right = builder.add_block();
        let shared = builder.add_block();
        let exit = builder.add_block();
        builder.set_terminator(
            entry,
            Terminator::cond_br(span, crate::mir::Value::Constant(condition), left, right),
        );
        builder.append_operation(
            left,
            Operation::store(
                span,
                crate::mir::Value::Constant(one),
                crate::mir::Value::Parameter(ret),
            ),
        );
        builder.set_terminator(left, Terminator::goto(span, shared));
        builder.append_operation(
            right,
            Operation::store(
                span,
                crate::mir::Value::Constant(two),
                crate::mir::Value::Parameter(ret),
            ),
        );
        builder.set_terminator(right, Terminator::goto(span, shared));
        builder.set_terminator(shared, Terminator::goto(span, exit));
        builder.set_terminator(exit, Terminator::ret(span));

        let function = builder.finish(env);
        let simplified = simplify_tails(&function).expect("the shared return must fold");
        assert!(!simplified.exposed_dead_code);
        assert_eq!(simplified.body.blocks().count(), 3);
        assert!(matches!(
            simplified.body.block(left).terminator().kind,
            TerminatorKind::Return
        ));
        assert!(matches!(
            simplified.body.block(right).terminator().kind,
            TerminatorKind::Return
        ));
    }

    #[test]
    fn an_entry_jump_to_an_empty_return_is_folded() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut builder = FunctionBuilder::new("fold_entry_return".into(), Default::default());
        let entry = builder.add_block();
        let exit = builder.add_block();
        builder.set_terminator(entry, Terminator::goto(span, exit));
        builder.set_terminator(exit, Terminator::ret(span));

        let function = builder.finish(env);
        let simplified = simplify_tails(&function).expect("the entry return must fold");
        assert!(!simplified.exposed_dead_code);
        assert_eq!(simplified.body.blocks().count(), 1);
        assert!(matches!(
            simplified.body.block(entry).terminator().kind,
            TerminatorKind::Return
        ));
    }
}
