// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Recovery of directly representable Wasm control-flow regions from physical MIR.

use crate::{
    mir::{BlockId, Function, dominance::Dominance, terminator::TerminatorKind},
    module::id::Id,
};

use super::body::BodyMode;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct NaturalLoop {
    pub(super) header: BlockId,
    pub(super) blocks: Vec<BlockId>,
    pub(super) exit: BlockId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ControlRegion {
    Block(BlockId),
    Loop(NaturalLoop),
}

impl ControlRegion {
    pub(super) fn entry(&self) -> BlockId {
        match self {
            Self::Block(block) => *block,
            Self::Loop(region) => region.header,
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
    /// order. This first form accepts disjoint loops whose edges are fallthroughs, backedges to the
    /// header, or exits to one shared block. The dispatcher remains the fallback for nested,
    /// irreducible, or more generally joined control flow.
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
                if !matches!(
                    body.block(BlockId::from_index(current)).terminator().kind,
                    TerminatorKind::Goto { .. } | TerminatorKind::CondBr { .. }
                ) {
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

        let mut regions = Vec::new();
        let mut visited = vec![false; block_count];
        let mut current = body.entry().as_index();
        loop {
            if visited[current] {
                return Self::Dispatcher;
            }
            if let Some(loop_index) = loop_for_block[current] {
                let region = &loops[loop_index];
                if region.header.as_index() != current {
                    return Self::Dispatcher;
                }
                for block in &region.blocks {
                    visited[block.as_index()] = true;
                }
                current = region.exit.as_index();
                regions.push(ControlRegion::Loop(region.clone()));
                continue;
            }
            visited[current] = true;
            regions.push(ControlRegion::Block(BlockId::from_index(current)));
            let mut targets = successors[current].iter().copied();
            let Some(target) = targets.next() else {
                break;
            };
            if targets.any(|other| other != target) {
                return Self::Dispatcher;
            }
            current = target;
        }
        if visited.iter().any(|visited| !visited) {
            return Self::Dispatcher;
        }
        Self::Structured(regions)
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
}
