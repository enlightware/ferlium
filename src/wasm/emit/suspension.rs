// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! The values of a yielded accessor that survive its suspension.

use crate::{
    FxHashMap, FxHashSet,
    mir::{
        BlockId, Function, OperationKind, ParameterKind, Value, ValueId, terminator::TerminatorKind,
    },
    module::id::Id,
};

use super::{control_flow::distinct_targets, operations};

/// The parameters and registers that the resumed half of a yielded accessor reads, but only the
/// half before the yield defines.
///
/// A register is retained when its definition may execute before the yield and a block reachable
/// from the resume block uses it. Its definition dominates that use, so a register defined only
/// after resumption is recomputed there instead. The projection frame of a nested `project` is
/// only read by its `end_project`, which does not read the yielded address itself.
#[derive(Debug, Default)]
pub(super) struct Crossing {
    /// Indexed by parameter.
    pub inputs: Vec<bool>,
    pub registers: FxHashSet<ValueId>,
    pub projection_frames: FxHashSet<ValueId>,
}

impl Crossing {
    pub(super) fn of(body: &Function) -> Self {
        let successors = |block: BlockId| match body.block(block).terminator().kind {
            // Suspension returns to the caller; resumption enters the resume block afresh.
            TerminatorKind::Yield { .. } => Vec::new(),
            ref kind => distinct_targets(kind),
        };
        let before = reachable(body, [body.entry()], successors);
        let resumes = body
            .blocks()
            .filter(|block| before[block.as_index()])
            .filter_map(|block| match body.block(block).terminator().kind {
                TerminatorKind::Yield { resume, .. } => Some(resume),
                _ => None,
            });
        let after = reachable(body, resumes, successors);

        let mut definitions = FxHashMap::default();
        let mut borrowed = FxHashMap::default();
        for block in body.blocks() {
            for operation in operations(body.block(block)) {
                if let Some(id) = operation.result_id() {
                    definitions.insert(id, block);
                    if matches!(operation.kind, OperationKind::BorrowSubscriptMember { .. }) {
                        borrowed.insert(id, &operation.operands[0]);
                    }
                }
            }
        }
        let mut crossing = Self {
            inputs: vec![false; body.parameters().len()],
            ..Self::default()
        };
        let mut pending = Vec::new();
        for block in body.blocks().filter(|block| after[block.as_index()]) {
            let block = body.block(block);
            for operation in operations(block) {
                if matches!(operation.kind, OperationKind::EndProject)
                    && let Value::Register(id) = operation.operands[0]
                    && definitions
                        .get(&id)
                        .is_some_and(|block| before[block.as_index()])
                {
                    crossing.projection_frames.insert(id);
                    continue;
                }
                pending.extend(operation.operands.iter());
            }
            if !matches!(block.terminator().kind, TerminatorKind::Invoke { .. }) {
                pending.extend(block.terminator().operands());
            }
        }
        let mut visited = FxHashSet::default();
        while let Some(value) = pending.pop() {
            match value {
                Value::Parameter(id) => {
                    if body.parameters()[id.as_index()].kind != ParameterKind::Return {
                        crossing.inputs[id.as_index()] = true;
                    }
                }
                Value::Register(id) => {
                    if !visited.insert(*id)
                        || !definitions
                            .get(id)
                            .is_some_and(|block| before[block.as_index()])
                    {
                        continue;
                    }
                    // A borrowed member has no storage of its own: its projection reads the
                    // subscript it was borrowed from.
                    if let Some(source) = borrowed.get(id) {
                        pending.push(source);
                    } else {
                        crossing.registers.insert(*id);
                    }
                }
                _ => (),
            }
        }
        crossing
    }
}

fn reachable(
    body: &Function,
    roots: impl IntoIterator<Item = BlockId>,
    successors: impl Fn(BlockId) -> Vec<BlockId>,
) -> Vec<bool> {
    let mut reached = vec![false; body.blocks().count()];
    let mut stack = Vec::new();
    for root in roots {
        if !reached[root.as_index()] {
            reached[root.as_index()] = true;
            stack.push(root);
        }
    }
    while let Some(block) = stack.pop() {
        for target in successors(block) {
            if !reached[target.as_index()] {
                reached[target.as_index()] = true;
                stack.push(target);
            }
        }
    }
    reached
}
