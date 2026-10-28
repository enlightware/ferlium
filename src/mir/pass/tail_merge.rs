// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Simplification of shared basic-block tails.
//!
//! Lowering keeps the source's control-flow shape. Consequently two arms which compute the same
//! thing still become two blocks, and ordinary CSE cannot see across their mutually exclusive
//! paths. This pass merges equivalent *regions*: a block with the blocks it dominates, compared
//! along their edges, with the results defined inside each region compared by definition order
//! rather than by their function-wide [`ValueId`](mir::ValueId). A result defined in one block of a
//! region and used in another, as CSE leaves it, is thus no obstacle, and neither is an invoke,
//! whose result reaches only its normal edge. A block hash-conses alone, the successors it
//! dominates counted by presence only, which preselects the candidates. The pass redirects edges
//! to one representative; it never moves or duplicates an operation.
//!
//! Source spans are intentionally absent from the key. They describe where either equivalent copy
//! came from, not what it does, and retaining the representative's span is the same diagnostic
//! compromise made whenever optimization removes one of two redundant computations.
//!
//! An empty block is the limiting case in the other direction: it holds nothing to execute, so its
//! terminator can be folded into its predecessors without duplicating an operation. How far that
//! goes depends on the terminator. A `goto` is folded into *every* predecessor edge, whatever its
//! kind, because an edge can name any block. A terminal — `return`, error propagation or cleanup
//! failure — can only replace a predecessor's own `goto`: a conditional or invoke edge must name a
//! block, and has nowhere to put a terminal instead. A returned value defined before the empty
//! block dominates each of its predecessors too.

use std::hash::{Hash, Hasher};

use rustc_hash::{FxHashMap, FxHashSet, FxHasher};

use crate::{
    containers::SVec2,
    mir::{
        self, BlockId, Function, Operation, ValueId,
        dominance::Dominance,
        edit::FunctionEdit,
        terminator::{TerminatorKind, TerminatorKindDiscriminant},
    },
    module::id::Id,
};

fn hash_value(
    value: &mir::Value,
    local_results: &FxHashMap<ValueId, usize>,
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
    left_results: &FxHashMap<ValueId, usize>,
    right_results: &FxHashMap<ValueId, usize>,
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

fn hash_target(
    block: BlockId,
    target: BlockId,
    replacement: &FxHashMap<BlockId, BlockId>,
    dominance: &Dominance,
    state: &mut impl Hasher,
) {
    // A successor in the block's region is compared as part of it, not by identity.
    if !replacement.contains_key(&target)
        && dominance.dominates(block.as_index(), target.as_index())
    {
        u32::MAX.hash(state);
    } else {
        canonical_target(target, replacement).hash(state);
    }
}

fn hash_operation(
    operation: &Operation,
    local_results: &mut FxHashMap<ValueId, usize>,
    state: &mut impl Hasher,
) {
    let (kind, operands) = operation.kind_and_operands();
    kind.hash(state);
    operands.len().hash(state);
    for operand in operands {
        hash_value(operand, local_results, state);
    }
    if let Some(result) = operation.result_id() {
        local_results.insert(result, local_results.len());
    }
}

/// A hash of `block` alone that equivalent regions share: results it defines by definition order,
/// successors in its region by their presence.
fn block_fingerprint(
    function: &Function,
    id: BlockId,
    replacement: &FxHashMap<BlockId, BlockId>,
    dominance: &Dominance,
    local_results: &mut FxHashMap<ValueId, usize>,
) -> u64 {
    let block = function.block(id);
    let mut state = FxHasher::default();
    block.operations().len().hash(&mut state);
    local_results.clear();
    for operation in block.operations() {
        hash_operation(operation, local_results, &mut state);
    }
    let kind = &block.terminator().kind;
    TerminatorKindDiscriminant::from(kind).hash(&mut state);
    match kind {
        TerminatorKind::CondBr { condition, .. } => {
            hash_value(condition, local_results, &mut state)
        }
        TerminatorKind::SwitchVariant { tag, cases, .. } => {
            hash_value(tag, local_results, &mut state);
            for (case, _) in cases {
                case.hash(&mut state);
            }
        }
        TerminatorKind::Invoke { operation, .. } => {
            hash_operation(operation, local_results, &mut state)
        }
        TerminatorKind::Yield { place, .. } => hash_value(place, local_results, &mut state),
        TerminatorKind::Return { value } => {
            if let Some(value) = value {
                hash_value(value, local_results, &mut state);
            }
        }
        TerminatorKind::InvariantFailure { message } => message.hash(&mut state),
        TerminatorKind::Goto { .. }
        | TerminatorKind::PropagateError
        | TerminatorKind::FailureDuringCleanup
        | TerminatorKind::EffectViolation => {}
    }
    for target in kind.successors() {
        hash_target(id, target, replacement, dominance, &mut state);
    }
    state.finish()
}

enum Representatives {
    One(BlockId),
    Many(Vec<BlockId>),
}

impl Representatives {
    fn find(
        &self,
        mut equivalent: impl FnMut(BlockId) -> Option<Vec<BlockId>>,
    ) -> Option<(BlockId, Vec<BlockId>)> {
        match self {
            Self::One(block) => equivalent(*block).map(|region| (*block, region)),
            Self::Many(blocks) => blocks
                .iter()
                .find_map(|block| equivalent(*block).map(|region| (*block, region))),
        }
    }

    fn push(&mut self, block: BlockId) {
        match self {
            Self::One(first) => *self = Self::Many(vec![*first, block]),
            Self::Many(blocks) => blocks.push(block),
        }
    }
}

/// Whether two operations compute the same thing, pairing their results by position.
fn operations_alpha_equivalent(
    left: &Operation,
    right: &Operation,
    left_results: &mut FxHashMap<ValueId, usize>,
    right_results: &mut FxHashMap<ValueId, usize>,
) -> bool {
    let (left_kind, left_operands) = left.kind_and_operands();
    let (right_kind, right_operands) = right.kind_and_operands();
    if left_kind != right_kind
        || left_operands.len() != right_operands.len()
        || !left_operands
            .iter()
            .zip(right_operands)
            .all(|(left, right)| values_alpha_equivalent(left, right, left_results, right_results))
    {
        return false;
    }
    match (left.result_id(), right.result_id()) {
        (Some(left), Some(right)) => {
            let ordinal = left_results.len();
            left_results.insert(left, ordinal);
            right_results.insert(right, ordinal);
            true
        }
        (None, None) => true,
        _ => false,
    }
}

/// Pairs the targets of two terminators that agree in everything else, recording the result of
/// an invoked operation; `None` if they differ.
fn paired_targets(
    left: &TerminatorKind,
    right: &TerminatorKind,
    left_results: &mut FxHashMap<ValueId, usize>,
    right_results: &mut FxHashMap<ValueId, usize>,
) -> Option<SVec2<(BlockId, BlockId)>> {
    let agree = match (left, right) {
        (TerminatorKind::Goto { .. }, TerminatorKind::Goto { .. })
        | (TerminatorKind::PropagateError, TerminatorKind::PropagateError)
        | (TerminatorKind::EffectViolation, TerminatorKind::EffectViolation)
        | (TerminatorKind::FailureDuringCleanup, TerminatorKind::FailureDuringCleanup) => true,
        (
            TerminatorKind::CondBr {
                condition: left, ..
            },
            TerminatorKind::CondBr {
                condition: right, ..
            },
        )
        | (TerminatorKind::Yield { place: left, .. }, TerminatorKind::Yield { place: right, .. }) => {
            values_alpha_equivalent(left, right, left_results, right_results)
        }
        (
            TerminatorKind::SwitchVariant {
                tag: left_tag,
                cases: left_cases,
                ..
            },
            TerminatorKind::SwitchVariant {
                tag: right_tag,
                cases: right_cases,
                ..
            },
        ) => {
            values_alpha_equivalent(left_tag, right_tag, left_results, right_results)
                && left_cases.len() == right_cases.len()
                && left_cases
                    .iter()
                    .zip(right_cases)
                    .all(|((left, _), (right, _))| left == right)
        }
        // The invoked result is defined on the normal edge, which the region pairs like any other.
        (
            TerminatorKind::Invoke {
                operation: left, ..
            },
            TerminatorKind::Invoke {
                operation: right, ..
            },
        ) => operations_alpha_equivalent(left, right, left_results, right_results),
        (TerminatorKind::Return { value: left }, TerminatorKind::Return { value: right }) => {
            match (left, right) {
                (None, None) => true,
                (Some(left), Some(right)) => {
                    values_alpha_equivalent(left, right, left_results, right_results)
                }
                _ => false,
            }
        }
        (
            TerminatorKind::InvariantFailure { message: left },
            TerminatorKind::InvariantFailure { message: right },
        ) => left == right,
        _ => false,
    };
    agree.then(|| left.successors().zip(right.successors()).collect())
}

/// Whether the region of `right` is alpha-equivalent to the region of `left`, answering the blocks
/// of `right`'s region, which redirecting `right`'s edges to `left` leaves unreachable.
///
/// A block's region is the blocks it dominates. Every use of a result defined in a region is
/// dominated by its definition, hence in the region too, so two regions compare by pairing their
/// blocks along their edges and their results by definition order across all those blocks; a
/// depth-first walk from the roots reaches every block's dominators first. An edge leaving the
/// regions must reach the same block on both sides. A result may thus cross blocks, as CSE leaves
/// it, and an invoke's result reaches its normal edge. Redirecting the edges entering `right` to
/// `left` only adds paths through `left`, which leaves every use in `left`'s region dominated.
fn equivalent_region(
    function: &Function,
    left: BlockId,
    right: BlockId,
    replacement: &FxHashMap<BlockId, BlockId>,
    representatives: &FxHashSet<BlockId>,
    dominance: &Dominance,
) -> Option<Vec<BlockId>> {
    let (left_root, right_root) = (left.as_index(), right.as_index());
    if dominance.dominates(left_root, right_root) || dominance.dominates(right_root, left_root) {
        return None;
    }
    // Dominance is that of the body before this simplification: a block already merged, or
    // standing for others, has other edges now.
    let in_region = |root: usize, block: BlockId| {
        dominance.dominates(root, block.as_index())
            && !replacement.contains_key(&block)
            && !representatives.contains(&block)
    };
    let mut left_results = FxHashMap::default();
    let mut right_results = FxHashMap::default();
    let mut pairs = FxHashMap::from_iter([(right, left)]);
    let mut paired_lefts = FxHashSet::from_iter([left]);
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        let left = function.block(left);
        let right = function.block(right);
        if left.operations().len() != right.operations().len()
            || !left
                .operations()
                .iter()
                .zip(right.operations())
                .all(|(left, right)| {
                    operations_alpha_equivalent(left, right, &mut left_results, &mut right_results)
                })
        {
            return None;
        }
        for (left, right) in paired_targets(
            &left.terminator().kind,
            &right.terminator().kind,
            &mut left_results,
            &mut right_results,
        )? {
            let shared = canonical_target(left, replacement);
            if shared == canonical_target(right, replacement)
                && !dominance.dominates(right_root, shared.as_index())
            {
                continue;
            }
            if !in_region(left_root, left) || !in_region(right_root, right) {
                return None;
            }
            match pairs.get(&right) {
                Some(paired) if *paired == left => {}
                Some(_) => return None,
                None if paired_lefts.insert(left) => {
                    pairs.insert(right, left);
                    pending.push((left, right));
                }
                None => return None,
            }
        }
    }
    Some(pairs.into_keys().collect())
}

/// How many source failures are in flight in each block, by block index. Normal and error flow
/// never join, so every reachable block has exactly one depth: an `invoke`'s error edge adds one.
fn failure_depths(function: &Function) -> Vec<usize> {
    let mut depths = vec![None; function.blocks().count()];
    depths[function.entry().as_index()] = Some(0);
    let mut pending = vec![function.entry()];
    while let Some(block) = pending.pop() {
        let depth = depths[block.as_index()].expect("a pending block has its depth");
        let terminator = &function.block(block).terminator().kind;
        let error = match terminator {
            TerminatorKind::Invoke { error, .. } => Some(*error),
            _ => None,
        };
        for successor in terminator.successors() {
            let successor_depth = depth + usize::from(Some(successor) == error);
            if depths[successor.as_index()].is_none() {
                depths[successor.as_index()] = Some(successor_depth);
                pending.push(successor);
            }
        }
    }
    depths.into_iter().map(Option::unwrap_or_default).collect()
}

/// The result of simplifying tails, including whether the rewrite can have made values dead.
pub(crate) struct SimplifiedTails {
    pub(crate) body: Function,
    pub(crate) exposed_dead_code: bool,
}

fn is_terminal(kind: &TerminatorKind) -> bool {
    matches!(
        kind,
        TerminatorKind::Return { .. }
            | TerminatorKind::PropagateError
            | TerminatorKind::EffectViolation
            | TerminatorKind::FailureDuringCleanup
            | TerminatorKind::InvariantFailure { .. }
    )
}

fn is_empty_terminal_block(function: &Function, block: BlockId) -> bool {
    let block = function.block(block);
    block.operations().is_empty() && is_terminal(&block.terminator().kind)
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
            TerminatorKind::SwitchVariant { cases, default, .. } => {
                for (_, target) in cases {
                    *target = next();
                }
                *default = next();
            }
            TerminatorKind::Invoke { normal, error, .. } => {
                *normal = next();
                *error = next();
            }
            TerminatorKind::Yield { resume, .. } => *resume = next(),
            TerminatorKind::Return { .. }
            | TerminatorKind::PropagateError
            | TerminatorKind::EffectViolation
            | TerminatorKind::FailureDuringCleanup
            | TerminatorKind::InvariantFailure { .. } => {}
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
        if let TerminatorKind::SwitchVariant { cases, default, .. } = terminator
            && cases.iter().all(|(_, target)| target == default)
        {
            *terminator = TerminatorKind::Goto { target: *default };
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
            if target.operations.is_empty() && is_terminal(&target.terminator.kind) {
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

    // Keyed by failure depth too: regions alike but for the failures in flight are not
    // interchangeable, and one that never reaches a terminal, such as a loop, would not say so.
    let mut representatives = FxHashMap::<(usize, u64), Representatives>::default();
    let mut replacement = FxHashMap::<BlockId, BlockId>::default();
    // The blocks others were redirected to, and those a merged region left unreachable.
    let mut standing_for_others = FxHashSet::default();
    let mut discarded = FxHashSet::default();
    let mut local_results = FxHashMap::default();
    // An unreachable block cannot safely represent a reachable one: a shared successor may use a
    // result defined by the reachable candidate, which only dominates that successor while the
    // other predecessor remains unreachable.
    let successors: Vec<Vec<usize>> = function
        .blocks()
        .map(|block| {
            function
                .block(block)
                .terminator()
                .successors()
                .map(|target| target.as_index())
                .collect()
        })
        .collect();
    let dominance = Dominance::of(&successors, function.entry().as_index());
    let failures = failure_depths(function);
    // Ordinary forward branch tails occur later in canonical block order. Walking backwards means
    // their representatives are already known, so the tails two blocks share are found first and
    // compared by identity; what is left of the two regions is paired.
    let mut blocks: Vec<_> = function
        .blocks()
        .skip(1)
        .filter(|block| dominance.is_reachable(block.as_index()))
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
        if discarded.contains(&block) {
            continue;
        }
        let fingerprint = (
            failures[block.as_index()],
            block_fingerprint(
                function,
                block,
                &replacement,
                &dominance,
                &mut local_results,
            ),
        );
        let representative = representatives.get(&fingerprint).and_then(|candidates| {
            candidates.find(|candidate| {
                if discarded.contains(&candidate) {
                    return None;
                }
                equivalent_region(
                    function,
                    candidate,
                    block,
                    &replacement,
                    &standing_for_others,
                    &dominance,
                )
            })
        });
        if let Some((representative, region)) = representative {
            replacement.insert(block, representative);
            standing_for_others.insert(representative);
            discarded.extend(region);
        } else if let Some(candidates) = representatives.get_mut(&fingerprint) {
            candidates.push(block);
        } else {
            representatives.insert(fingerprint, Representatives::One(block));
        }
    }

    let has_equal_target_branch = function
        .blocks()
        .filter(|block| dominance.is_reachable(block.as_index()))
        .any(|block| match &function.block(block).terminator().kind {
            TerminatorKind::CondBr {
                then_target,
                else_target,
                ..
            } => then_target == else_target,
            TerminatorKind::SwitchVariant { cases, default, .. } => {
                cases.iter().all(|(_, target)| target == default)
            }
            _ => false,
        });
    let has_empty_forwarding_block = function
        .blocks()
        .skip(1)
        .filter(|block| dominance.is_reachable(block.as_index()))
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
            TerminatorKind::SwitchVariant { cases, default, .. } => {
                for (_, target) in cases {
                    *target = replacement.get(target).copied().unwrap_or(*target);
                }
                *default = replacement.get(default).copied().unwrap_or(*default);
            }
            TerminatorKind::Invoke { normal, error, .. } => {
                *normal = replacement.get(normal).copied().unwrap_or(*normal);
                *error = replacement.get(error).copied().unwrap_or(*error);
            }
            TerminatorKind::Yield { resume, .. } => {
                *resume = replacement.get(resume).copied().unwrap_or(*resume);
            }
            TerminatorKind::Return { .. }
            | TerminatorKind::PropagateError
            | TerminatorKind::EffectViolation
            | TerminatorKind::FailureDuringCleanup
            | TerminatorKind::InvariantFailure { .. } => {}
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
        if let TerminatorKind::SwitchVariant { cases, default, .. } = &terminator.kind
            && cases.iter().all(|(_, target)| target == default)
        {
            terminator.kind = TerminatorKind::Goto { target: *default };
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
    use ustr::ustr;

    use super::simplify_tails;
    use crate::{
        CompilerSession, Location, MirOptimization,
        hir::value::LiteralValue,
        mir::{
            Operation, OperationKind, ParameterKind, Value,
            builder::FunctionBuilder,
            terminator::{Terminator, TerminatorKind},
            verify::verify_function,
        },
        module::{FunctionId, LocalFunctionId, ModuleId},
        std::{logic::bool_type, math::int_type},
        types::{
            effects::{PrimitiveEffect, effect},
            r#type::{CallImplType, FnType},
        },
    };

    fn optimized_body(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("tail_merge", src)
    }

    #[test]
    fn alpha_equivalent_branch_arms_are_merged() {
        let body = optimized_body("fn f(x: int) -> int { if x > 0 { x + 1 } else { x + 1 } }");
        assert!(
            !body.contains("condbr") && !body.contains("switch_variant"),
            "the equivalent arms make the predicate dead:\n{body}"
        );
        assert_eq!(
            body.matches("Num<std::int>::add#impl").count(),
            1,
            "the common tail must be retained once:\n{body}"
        );
        assert!(
            !body.contains("compare_int")
                && !body.contains("gt_int")
                && !body.contains("Ord<std::int>::gt"),
            "proven-call DCE must collect the dead predicate:\n{body}"
        );
    }

    /// CSE leaves a result defined in one block and used in a later one. Each copy is then
    /// equivalent only as a whole region, never block by block: alone, the later block would lose
    /// the definition its own copy provides.
    #[test]
    fn regions_whose_results_cross_blocks_are_merged_whole() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        for same in [true, false] {
            let mut builder = FunctionBuilder::new("region_tails".into(), Default::default());
            let x = builder.add_parameter(int_type(), ParameterKind::Value);
            let c = builder.add_parameter(bool_type(), ParameterKind::Value);
            let ret = builder.add_parameter(int_type(), ParameterKind::Return);
            let entry = builder.add_block();
            let copies = [
                (builder.add_block(), builder.add_block()),
                (builder.add_block(), builder.add_block()),
            ];
            let exit = builder.add_block();
            let join = builder.add_block();
            let slot = builder
                .append_operation(entry, Operation::alloca(span, int_type()))
                .unwrap();
            builder.append_operation(
                entry,
                Operation::store(span, Value::Parameter(x), slot.clone()),
            );
            builder.set_terminator(
                entry,
                Terminator::cond_br(span, Value::Parameter(c), copies[0].0, copies[1].0),
            );
            for (index, (test, update)) in copies.into_iter().enumerate() {
                let loaded = builder
                    .append_operation(test, Operation::load(span, slot.clone()))
                    .unwrap();
                builder.set_terminator(
                    test,
                    Terminator::cond_br(span, Value::Parameter(c), update, exit),
                );
                let stored = if same || index == 0 {
                    loaded
                } else {
                    Value::Parameter(x)
                };
                builder.append_operation(
                    update,
                    Operation::store(span, stored, Value::Parameter(ret)),
                );
                builder.set_terminator(update, Terminator::goto(span, join));
            }
            builder.append_operation(
                exit,
                Operation::store(span, Value::Parameter(x), Value::Parameter(ret)),
            );
            builder.set_terminator(exit, Terminator::ret(span));
            builder.set_terminator(join, Terminator::ret(span));
            let body = builder.finish(env);
            let body = simplify_tails(&body).map_or(body, |result| result.body);
            verify_function(&body, env);
            let loads = body
                .blocks()
                .flat_map(|block| body.block(block).operations())
                .filter(|operation| matches!(operation.kind, OperationKind::Load))
                .count();
            assert_eq!(loads, if same { 1 } else { 2 }, "same: {same}");
        }
    }

    /// An indexed read lowers to a bounds-check diamond and an invoke whose result its normal edge
    /// reads: equivalent arms are a region with a join and an invoke, merged as a whole.
    #[test]
    fn arms_reading_through_a_checked_index_are_merged() {
        let body = optimized_body(
            "fn f(a: [int], i: int, c: bool) -> int { if c { a[i] * 3 + i } else { a[i] * 3 + i } }",
        );
        assert_eq!(
            body.matches("array_offset_in_bounds").count(),
            1,
            "the two arms must become one:\n{body}"
        );
    }

    #[test]
    fn invariant_failure_tails_merge_only_with_the_same_diagnostic() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        for same in [true, false] {
            let mut builder = FunctionBuilder::new("fatal_tails".into(), Default::default());
            let condition = builder.add_constant(bool_type(), LiteralValue::new_native(true), &env);
            let entry = builder.add_block();
            let yes = builder.add_block();
            let no = builder.add_block();
            builder.set_terminator(
                entry,
                Terminator::cond_br(span, Value::Constant(condition), yes, no),
            );
            builder.set_terminator(yes, Terminator::invariant_failure(span, "first".into()));
            builder.set_terminator(
                no,
                Terminator::invariant_failure(span, if same { "first" } else { "second" }.into()),
            );
            let body = builder.finish(env);
            let body = simplify_tails(&body).map_or(body, |result| result.body);
            verify_function(&body, env);
            assert_eq!(body.blocks().count(), if same { 1 } else { 3 });
            let messages: Vec<_> = body
                .blocks()
                .filter_map(|block| match body.block(block).terminator().kind {
                    TerminatorKind::InvariantFailure { message } => Some(message),
                    _ => None,
                })
                .collect();
            assert!(messages.contains(&ustr("first")));
            assert_eq!(messages.contains(&ustr("second")), !same);
        }
    }

    /// A loop never reaches a terminal, which would otherwise tell normal flow from a failure in
    /// flight. Merging the copy on an error edge with the one on the normal edge would join them.
    #[test]
    fn equal_regions_merge_only_with_the_same_failures_in_flight() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("failure_tails".into(), Default::default());
        let entry = builder.add_block();
        let loops = [builder.add_block(), builder.add_block()];
        let result = builder
            .append_operation(entry, Operation::alloca(span, int_type()))
            .unwrap();
        let call = Operation::call(
            span,
            Value::Function(FunctionId::new(
                ModuleId::default(),
                LocalFunctionId::default(),
            )),
            [result],
            CallImplType::value(FnType::new_by_val(
                [],
                int_type(),
                effect(PrimitiveEffect::Fallible),
            )),
        );
        builder.set_terminator(entry, Terminator::invoke(span, call, loops[0], loops[1]));
        for block in loops {
            builder.append_operation(block, Operation::check_fuel(span));
            builder.set_terminator(block, Terminator::goto(span, block));
        }
        let body = builder.finish(env);
        let body = simplify_tails(&body).map_or(body, |result| result.body);
        verify_function(&body, env);
        assert_eq!(body.blocks().count(), 3);
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
            Operation::store(span, reachable_result, Value::Parameter(ret)),
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
            Terminator::cond_br(span, Value::Constant(condition), exit, exit),
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
            Terminator::cond_br(span, Value::Constant(condition), arm, forwarding),
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
            Terminator::cond_br(span, Value::Constant(condition), left, right),
        );
        builder.append_operation(
            left,
            Operation::store(span, Value::Constant(one), Value::Parameter(ret)),
        );
        builder.set_terminator(left, Terminator::goto(span, shared));
        builder.append_operation(
            right,
            Operation::store(span, Value::Constant(two), Value::Parameter(ret)),
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
            TerminatorKind::Return { .. }
        ));
        assert!(matches!(
            simplified.body.block(right).terminator().kind,
            TerminatorKind::Return { .. }
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
            TerminatorKind::Return { .. }
        ));
    }
}
