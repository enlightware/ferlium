// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Natural loops, as the loop passes recognize them: a header that dominates the tail of a back
//! edge, the blocks that reach that tail without passing the header, and one unconditional
//! preheader through which every outside path enters.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    mir::{BlockId, Function, dominance::Dominance, terminator::TerminatorKind},
    module::id::Id,
};

#[derive(Clone)]
pub(crate) struct NaturalLoop {
    pub(crate) blocks: FxHashSet<BlockId>,
    pub(crate) header: BlockId,
    /// The one block outside the loop that enters it, by an unconditional jump to the header.
    pub(crate) preheader: BlockId,
}

/// The successor indices and the deduplicated predecessors of every block.
pub(crate) fn cfg(func: &Function) -> (Vec<Vec<usize>>, Vec<Vec<BlockId>>) {
    let count = func.blocks().count();
    let mut successors = vec![Vec::new(); count];
    let mut predecessors = vec![Vec::new(); count];
    for block in func.blocks() {
        for successor in func.block(block).terminator().successors() {
            successors[block.as_index()].push(successor.as_index());
            if !predecessors[successor.as_index()].contains(&block) {
                predecessors[successor.as_index()].push(block);
            }
        }
    }
    (successors, predecessors)
}

/// The natural loops with a single unconditional preheader, in no particular order. A loop entered
/// from several outside blocks, or conditionally, has no place to put code that runs once before it
/// and is left out.
pub(crate) fn natural_loops(
    func: &Function,
    successors: &[Vec<usize>],
    predecessors: &[Vec<BlockId>],
    dominance: &Dominance,
) -> Vec<NaturalLoop> {
    let mut by_header = FxHashMap::<BlockId, FxHashSet<BlockId>>::default();
    for tail in func.blocks() {
        if !dominance.is_reachable(tail.as_index()) {
            continue;
        }
        for &header in &successors[tail.as_index()] {
            if !dominance.dominates(header, tail.as_index()) {
                continue;
            }
            let header = BlockId::from_index(header);
            let natural = by_header.entry(header).or_default();
            natural.insert(header);
            if natural.insert(tail) {
                let mut pending = vec![tail];
                while let Some(block) = pending.pop() {
                    for &predecessor in &predecessors[block.as_index()] {
                        if natural.insert(predecessor) && predecessor != header {
                            pending.push(predecessor);
                        }
                    }
                }
            }
        }
    }

    by_header
        .into_iter()
        .filter_map(|(header, blocks)| {
            let outside = predecessors[header.as_index()]
                .iter()
                .copied()
                .filter(|predecessor| !blocks.contains(predecessor))
                .collect::<Vec<_>>();
            let [preheader] = outside.as_slice() else {
                return None;
            };
            matches!(
                func.block(*preheader).terminator().kind,
                TerminatorKind::Goto { target } if target == header
            )
            .then_some(NaturalLoop {
                blocks,
                header,
                preheader: *preheader,
            })
        })
        .collect()
}
