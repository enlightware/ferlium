// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Recovery of directly representable Wasm control-flow regions from physical MIR.

use crate::{
    mir::{BlockId, Function, dominance::Dominance, terminator::TerminatorKind},
    module::id::Id,
};

use super::body::BodyMode;

/// Bounds recursive region recovery and the nesting depth of emitted Wasm control constructs.
const MAX_STRUCTURED_DEPTH: usize = 128;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct NaturalLoop {
    pub(super) header: BlockId,
    pub(super) blocks: Vec<BlockId>,
    pub(super) exit: BlockId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct IfRegion {
    pub(super) header: BlockId,
    pub(super) then_regions: Vec<ControlRegion>,
    pub(super) else_regions: Vec<ControlRegion>,
    /// The shared MIR join, or `None` when both arms terminate at the function exit.
    pub(super) join: Option<BlockId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ControlRegion {
    Block(BlockId),
    Loop(NaturalLoop),
    If(IfRegion),
}

impl ControlRegion {
    pub(super) fn entry(&self) -> BlockId {
        match self {
            Self::Block(block) => *block,
            Self::Loop(region) => region.header,
            Self::If(region) => region.header,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ControlFlow {
    /// A sequence of directly representable blocks and natural-loop regions.
    Structured(Vec<ControlRegion>),
    /// Arbitrary control flow retains the program-counter dispatcher.
    Dispatcher,
}

impl ControlFlow {
    /// Recovers the structured subset that can be represented directly with Wasm blocks and loops.
    ///
    /// Natural loops are discovered from dominance backedges rather than source syntax. Blocks are
    /// then scheduled along their CFG edges, so a loop's exit need not follow its body in MIR storage
    /// order. Disjoint loops accept fallthroughs, backedges to the header, and exits to one shared
    /// block. Outside loops, conditional branches whose arms reconverge at one post-dominating join
    /// become recursive Wasm `if` regions. Variant switches selecting between two blocks count as
    /// conditional branches. The dispatcher remains the fallback for nested loops,
    /// irreducible control flow, and branch forms not represented here.
    pub(super) fn of(body: &Function, mode: BodyMode) -> Self {
        if !matches!(mode, BodyMode::Normal) {
            return Self::Dispatcher;
        }
        let block_count = body.blocks().count();
        let successors = body
            .blocks()
            .map(|block| {
                body.block(block)
                    .terminator()
                    .successors()
                    .map(BlockId::as_index)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut predecessors = vec![Vec::new(); block_count];
        for (source, targets) in successors.iter().enumerate() {
            for &target in targets {
                predecessors[target].push(source);
            }
        }
        let dominance = Dominance::of(&successors, body.entry().as_index());
        let mut latches = vec![Vec::new(); block_count];
        for (source, targets) in successors.iter().enumerate() {
            for &target in targets {
                if dominance.dominates(target, source) {
                    latches[target].push(source);
                }
            }
        }

        let mut loops = Vec::new();
        let mut loop_for_block = vec![None; block_count];
        for (header, latches) in latches.iter().enumerate() {
            if latches.is_empty() {
                continue;
            }
            let mut members = vec![false; block_count];
            members[header] = true;
            let mut pending = latches.clone();
            while let Some(block) = pending.pop() {
                if members[block] {
                    continue;
                }
                members[block] = true;
                pending.extend(predecessors[block].iter().copied());
            }
            if predecessors.iter().enumerate().any(|(block, incoming)| {
                members[block] && block != header && incoming.iter().any(|source| !members[*source])
            }) {
                return Self::Dispatcher;
            }
            let mut exit = None;
            for target in members
                .iter()
                .enumerate()
                .filter(|(_, member)| **member)
                .flat_map(|(block, _)| successors[block].iter().copied())
                .filter(|target| !members[*target])
            {
                if exit
                    .replace(target)
                    .is_some_and(|previous| previous != target)
                {
                    return Self::Dispatcher;
                }
            }
            let Some(exit) = exit else {
                return Self::Dispatcher;
            };

            let mut blocks = Vec::new();
            let mut visited = vec![false; block_count];
            let mut current = header;
            loop {
                if visited[current] || !members[current] {
                    return Self::Dispatcher;
                }
                visited[current] = true;
                blocks.push(BlockId::from_index(current));
                let kind = &body.block(BlockId::from_index(current)).terminator().kind;
                if !matches!(kind, TerminatorKind::Goto { .. })
                    && conditional_targets(kind).is_none()
                {
                    return Self::Dispatcher;
                }
                let mut forward = None;
                for &target in &successors[current] {
                    if target == header || target == exit {
                        continue;
                    }
                    if !members[target] || visited[target] {
                        return Self::Dispatcher;
                    }
                    if forward
                        .replace(target)
                        .is_some_and(|previous| previous != target)
                    {
                        return Self::Dispatcher;
                    }
                }
                let Some(next) = forward else {
                    break;
                };
                current = next;
            }
            if members
                .iter()
                .enumerate()
                .any(|(block, member)| *member && !visited[block])
            {
                return Self::Dispatcher;
            }
            let loop_index = loops.len();
            for block in &blocks {
                if loop_for_block[block.as_index()]
                    .replace(loop_index)
                    .is_some()
                {
                    // Nested and overlapping natural loops are left to the dispatcher for now.
                    return Self::Dispatcher;
                }
            }
            loops.push(NaturalLoop {
                header: BlockId::from_index(header),
                blocks,
                exit: BlockId::from_index(exit),
            });
        }

        let mut active = vec![true; block_count];
        let mut structured_successors = successors.clone();
        for (index, region) in loops.iter().enumerate() {
            for block in &region.blocks {
                if *block == region.header {
                    structured_successors[block.as_index()] = vec![region.exit.as_index()];
                } else {
                    active[block.as_index()] = false;
                    structured_successors[block.as_index()].clear();
                }
                debug_assert_eq!(loop_for_block[block.as_index()], Some(index));
            }
        }
        for targets in &mut structured_successors {
            // A branch is classified by its distinct targets: a switch whose cases share targets
            // can be conditional, and a conditional whose targets coincide is a jump.
            let mut index = 0;
            while index < targets.len() {
                if targets[..index].contains(&targets[index]) {
                    targets.remove(index);
                } else {
                    index += 1;
                }
            }
        }
        if active.iter().enumerate().any(|(source, is_active)| {
            *is_active
                && structured_successors[source]
                    .iter()
                    .any(|target| !active[*target])
        }) {
            return Self::Dispatcher;
        }
        let Some((postdominance, synthetic_exit)) = postdominance(&structured_successors, &active)
        else {
            return Self::Dispatcher;
        };
        let mut builder = RegionBuilder {
            body,
            successors: &structured_successors,
            postdominance: &postdominance,
            loops: &loops,
            loop_for_block: &loop_for_block,
            active: &active,
            synthetic_exit,
            visited: vec![false; block_count],
        };
        let Some(regions) = builder.sequence(body.entry().as_index(), None, 0) else {
            return Self::Dispatcher;
        };
        if builder.visited.iter().any(|visited| !visited) {
            return Self::Dispatcher;
        }
        Self::Structured(regions)
    }
}

/// Returns the `(then, else)` targets of a terminator that selects between at most two blocks
/// by a condition.
///
/// A variant switch qualifies when its cases reach one target besides `default`: `then` is taken
/// when the tag matches one of these cases. The targets coincide when the branch is a jump.
pub(super) fn conditional_targets(kind: &TerminatorKind) -> Option<(BlockId, BlockId)> {
    match kind {
        TerminatorKind::CondBr {
            then_target,
            else_target,
            ..
        } => Some((*then_target, *else_target)),
        TerminatorKind::SwitchVariant { cases, default, .. } => {
            let then_target = cases
                .iter()
                .map(|(_, target)| *target)
                .find(|target| target != default)
                .unwrap_or(*default);
            cases
                .iter()
                .all(|(_, target)| *target == then_target || target == default)
                .then_some((then_target, *default))
        }
        _ => None,
    }
}

/// Computes post-dominance over the loop-collapsed graph.
///
/// A synthetic exit joins all terminal blocks. Returning `None` means some active node cannot
/// reach an exit, so it cannot participate in the acyclic region tree.
fn postdominance(successors: &[Vec<usize>], active: &[bool]) -> Option<(Dominance, usize)> {
    let block_count = successors.len();
    let exit = block_count;
    let mut reverse = vec![Vec::new(); block_count + 1];
    for (source, targets) in successors
        .iter()
        .enumerate()
        .filter(|(source, _)| active[*source])
    {
        if targets.is_empty() {
            reverse[exit].push(source);
        } else {
            for &target in targets {
                reverse[target].push(source);
            }
        }
    }
    let dominance = Dominance::of(&reverse, exit);
    if active
        .iter()
        .enumerate()
        .any(|(node, active)| *active && !dominance.is_reachable(node))
    {
        return None;
    }
    Some((dominance, exit))
}

struct RegionBuilder<'a> {
    body: &'a Function,
    successors: &'a [Vec<usize>],
    postdominance: &'a Dominance,
    loops: &'a [NaturalLoop],
    loop_for_block: &'a [Option<usize>],
    active: &'a [bool],
    synthetic_exit: usize,
    visited: Vec<bool>,
}

impl RegionBuilder<'_> {
    fn sequence(
        &mut self,
        start: usize,
        stop: Option<usize>,
        depth: usize,
    ) -> Option<Vec<ControlRegion>> {
        let mut regions = Vec::new();
        let mut current = start;
        while Some(current) != stop {
            if !self.active[current] || self.visited[current] {
                return None;
            }
            if let Some(loop_index) = self.loop_for_block[current] {
                let region = &self.loops[loop_index];
                if region.header.as_index() != current
                    || region
                        .blocks
                        .iter()
                        .any(|block| self.visited[block.as_index()])
                {
                    return None;
                }
                for block in &region.blocks {
                    self.visited[block.as_index()] = true;
                }
                current = region.exit.as_index();
                regions.push(ControlRegion::Loop(region.clone()));
                continue;
            }

            let block = BlockId::from_index(current);
            let successors = &self.successors[current];
            match successors.as_slice() {
                [] => {
                    if stop.is_some() {
                        return None;
                    }
                    self.visited[current] = true;
                    regions.push(ControlRegion::Block(block));
                    return Some(regions);
                }
                [target] => {
                    self.visited[current] = true;
                    regions.push(ControlRegion::Block(block));
                    current = *target;
                }
                [_, _] => {
                    if depth == MAX_STRUCTURED_DEPTH {
                        return None;
                    }
                    let (then_target, else_target) =
                        conditional_targets(&self.body.block(block).terminator().kind)?;
                    let join = self.postdominance.immediate_dominator(current)?;
                    self.visited[current] = true;
                    let join_block =
                        (join != self.synthetic_exit).then(|| BlockId::from_index(join));
                    let then_regions = self.sequence(
                        then_target.as_index(),
                        join_block.map(BlockId::as_index),
                        depth + 1,
                    )?;
                    let else_regions = self.sequence(
                        else_target.as_index(),
                        join_block.map(BlockId::as_index),
                        depth + 1,
                    )?;
                    regions.push(ControlRegion::If(IfRegion {
                        header: block,
                        then_regions,
                        else_regions,
                        join: join_block,
                    }));
                    let Some(join) = join_block else {
                        return Some(regions);
                    };
                    current = join.as_index();
                }
                _ => return None,
            }
        }
        Some(regions)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Location,
        mir::{BasicBlock, Value, terminator::Terminator, value::ConstantId},
        types::r#type::CallResultConvention,
    };

    fn control_flow(terminators: Vec<Terminator>) -> Function {
        Function::new(
            "control_flow".into(),
            CallResultConvention::Value,
            Vec::new(),
            Vec::new(),
            terminators
                .into_iter()
                .map(|terminator| BasicBlock::new(Vec::new(), terminator))
                .collect(),
        )
    }

    #[wasm_bindgen_test::wasm_bindgen_test]
    fn recovers_linear_bodies_and_schedules_natural_loops() {
        let span = Location::new_synthesized();
        let linear = control_flow(vec![
            Terminator::goto(span, BlockId::from_index(1)),
            Terminator::goto(span, BlockId::from_index(2)),
            Terminator::ret(span),
        ]);
        assert_eq!(
            ControlFlow::of(&linear, BodyMode::Normal),
            ControlFlow::Structured(vec![
                ControlRegion::Block(BlockId::from_index(0)),
                ControlRegion::Block(BlockId::from_index(1)),
                ControlRegion::Block(BlockId::from_index(2)),
            ])
        );
        assert_eq!(
            ControlFlow::of(
                &linear,
                BodyMode::ProjectionStart {
                    resume: crate::wasm::abi::DispatchTableSlotId::from_index(0),
                }
            ),
            ControlFlow::Dispatcher
        );

        // Storage order puts the exit before the latch, as physical MIR commonly does.
        let natural_loop = control_flow(vec![
            Terminator::goto(span, BlockId::from_index(1)),
            Terminator::cond_br(
                span,
                Value::Constant(ConstantId::from_index(0)),
                BlockId::from_index(3),
                BlockId::from_index(2),
            ),
            Terminator::ret(span),
            Terminator::goto(span, BlockId::from_index(1)),
        ]);
        assert_eq!(
            ControlFlow::of(&natural_loop, BodyMode::Normal),
            ControlFlow::Structured(vec![
                ControlRegion::Block(BlockId::from_index(0)),
                ControlRegion::Loop(NaturalLoop {
                    header: BlockId::from_index(1),
                    blocks: vec![BlockId::from_index(1), BlockId::from_index(3)],
                    exit: BlockId::from_index(2),
                }),
                ControlRegion::Block(BlockId::from_index(2)),
            ])
        );

        let skipping = control_flow(vec![
            Terminator::goto(span, BlockId::from_index(2)),
            Terminator::ret(span),
            Terminator::ret(span),
        ]);
        assert_eq!(
            ControlFlow::of(&skipping, BodyMode::Normal),
            ControlFlow::Dispatcher
        );

        let exit_free = control_flow(vec![
            Terminator::goto(span, BlockId::from_index(1)),
            Terminator::goto(span, BlockId::from_index(1)),
        ]);
        assert_eq!(
            ControlFlow::of(&exit_free, BodyMode::Normal),
            ControlFlow::Dispatcher
        );

        let multiple_exits = control_flow(vec![
            Terminator::goto(span, BlockId::from_index(1)),
            Terminator::cond_br(
                span,
                Value::Constant(ConstantId::from_index(0)),
                BlockId::from_index(2),
                BlockId::from_index(3),
            ),
            Terminator::cond_br(
                span,
                Value::Constant(ConstantId::from_index(0)),
                BlockId::from_index(1),
                BlockId::from_index(4),
            ),
            Terminator::ret(span),
            Terminator::ret(span),
        ]);
        assert_eq!(
            ControlFlow::of(&multiple_exits, BodyMode::Normal),
            ControlFlow::Dispatcher
        );
    }

    #[wasm_bindgen_test::wasm_bindgen_test]
    fn recovers_nested_acyclic_branches() {
        let span = Location::new_synthesized();
        // The outer else arm is empty. Its then arm contains a nested diamond before the shared
        // outer join, and neither join follows its branches in storage order by construction.
        let nested = control_flow(vec![
            Terminator::cond_br(
                span,
                Value::Constant(ConstantId::from_index(0)),
                BlockId::from_index(1),
                BlockId::from_index(5),
            ),
            Terminator::cond_br(
                span,
                Value::Constant(ConstantId::from_index(1)),
                BlockId::from_index(2),
                BlockId::from_index(3),
            ),
            Terminator::goto(span, BlockId::from_index(4)),
            Terminator::goto(span, BlockId::from_index(4)),
            Terminator::goto(span, BlockId::from_index(5)),
            Terminator::ret(span),
        ]);
        assert_eq!(
            ControlFlow::of(&nested, BodyMode::Normal),
            ControlFlow::Structured(vec![
                ControlRegion::If(IfRegion {
                    header: BlockId::from_index(0),
                    then_regions: vec![
                        ControlRegion::If(IfRegion {
                            header: BlockId::from_index(1),
                            then_regions: vec![ControlRegion::Block(BlockId::from_index(2))],
                            else_regions: vec![ControlRegion::Block(BlockId::from_index(3))],
                            join: Some(BlockId::from_index(4)),
                        }),
                        ControlRegion::Block(BlockId::from_index(4)),
                    ],
                    else_regions: Vec::new(),
                    join: Some(BlockId::from_index(5)),
                }),
                ControlRegion::Block(BlockId::from_index(5)),
            ])
        );

        // Separate terminal arms share the synthetic function exit and form a terminal Wasm if.
        let early_return = control_flow(vec![
            Terminator::cond_br(
                span,
                Value::Constant(ConstantId::from_index(0)),
                BlockId::from_index(1),
                BlockId::from_index(2),
            ),
            Terminator::ret(span),
            Terminator::ret(span),
        ]);
        assert_eq!(
            ControlFlow::of(&early_return, BodyMode::Normal),
            ControlFlow::Structured(vec![ControlRegion::If(IfRegion {
                header: BlockId::from_index(0),
                then_regions: vec![ControlRegion::Block(BlockId::from_index(1))],
                else_regions: vec![ControlRegion::Block(BlockId::from_index(2))],
                join: None,
            })])
        );

        let guard_chain = |guard_count| {
            let mut terminators = Vec::with_capacity(guard_count * 2 + 1);
            for guard in 0..guard_count {
                terminators.push(Terminator::cond_br(
                    span,
                    Value::Constant(ConstantId::from_index(guard)),
                    BlockId::from_index(guard_count + guard),
                    BlockId::from_index(if guard + 1 == guard_count {
                        guard_count * 2
                    } else {
                        guard + 1
                    }),
                ));
            }
            terminators.extend((0..=guard_count).map(|_| Terminator::ret(span)));
            control_flow(terminators)
        };
        assert!(matches!(
            ControlFlow::of(&guard_chain(MAX_STRUCTURED_DEPTH), BodyMode::Normal),
            ControlFlow::Structured(_)
        ));
        assert_eq!(
            ControlFlow::of(&guard_chain(MAX_STRUCTURED_DEPTH + 1), BodyMode::Normal),
            ControlFlow::Dispatcher,
            "excessive structured nesting must retain the non-recursive dispatcher"
        );
    }

    #[wasm_bindgen_test::wasm_bindgen_test]
    fn recovers_variant_switches_with_two_targets_as_branches() {
        let span = Location::new_synthesized();
        let tag = || Value::Constant(ConstantId::from_index(0));
        // Two cases share the then target, the third one shares the default target.
        let two_targets = control_flow(vec![
            Terminator::switch_variant(
                span,
                tag(),
                vec![
                    ("A".into(), BlockId::from_index(1)),
                    ("B".into(), BlockId::from_index(2)),
                    ("C".into(), BlockId::from_index(1)),
                ],
                BlockId::from_index(2),
            ),
            Terminator::goto(span, BlockId::from_index(3)),
            Terminator::goto(span, BlockId::from_index(3)),
            Terminator::ret(span),
        ]);
        assert_eq!(
            ControlFlow::of(&two_targets, BodyMode::Normal),
            ControlFlow::Structured(vec![
                ControlRegion::If(IfRegion {
                    header: BlockId::from_index(0),
                    then_regions: vec![ControlRegion::Block(BlockId::from_index(1))],
                    else_regions: vec![ControlRegion::Block(BlockId::from_index(2))],
                    join: Some(BlockId::from_index(3)),
                }),
                ControlRegion::Block(BlockId::from_index(3)),
            ])
        );

        let three_targets = control_flow(vec![
            Terminator::switch_variant(
                span,
                tag(),
                vec![
                    ("A".into(), BlockId::from_index(1)),
                    ("B".into(), BlockId::from_index(2)),
                ],
                BlockId::from_index(3),
            ),
            Terminator::goto(span, BlockId::from_index(3)),
            Terminator::goto(span, BlockId::from_index(3)),
            Terminator::ret(span),
        ]);
        assert_eq!(
            ControlFlow::of(&three_targets, BodyMode::Normal),
            ControlFlow::Dispatcher
        );
    }
}
