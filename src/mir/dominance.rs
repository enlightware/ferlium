// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Dominance over a rooted directed graph given as successor lists.
//!
//! Two consumers want it over two different graphs, which is why this takes bare successor lists
//! rather than a [`Function`](crate::mir::Function): the verifier dominates *instructions*, since an
//! invoked operation's result is anchored at the normal successor and must not reach the error one,
//! while [`cse`](crate::mir::pass::cse) dominates *blocks*, which is all a scoped walk needs.
//!
//! Immediate dominators come from the Cooper-Harvey-Kennedy algorithm; the resulting tree is then
//! numbered in depth-first order, so a dominance query is an interval containment and answers in
//! constant time.
//!
//! The physical verifier uses dominance for validity checks, while Wasm control-flow translation
//! walks the dominator tree to place blocks in structured Wasm control constructs.
#![allow(dead_code)]

use crate::graph::reverse_postorder;

/// The dominator tree of a rooted graph, and constant-time dominance queries over it.
pub(crate) struct Dominance {
    immediate_dominator: Vec<Option<usize>>,
    children: Vec<Vec<usize>>,
    preorder: Vec<usize>,
    postorder: Vec<usize>,
}

impl Dominance {
    const UNREACHABLE: usize = usize::MAX;

    /// Computes dominance over the graph `successors` describes, rooted at `entry`.
    ///
    /// Nodes are the indices of `successors`. One a path from `entry` never reaches is neither
    /// dominated nor dominating; [`is_reachable`](Self::is_reachable) is what distinguishes it.
    pub(crate) fn of(successors: &[Vec<usize>], entry: usize) -> Self {
        let node_count = successors.len();
        let mut predecessors = vec![Vec::new(); node_count];
        for (node, targets) in successors.iter().enumerate() {
            for &target in targets {
                predecessors[target].push(node);
            }
        }

        let reverse_postorder = reverse_postorder(successors, entry);
        let mut reverse_postorder_index = vec![Self::UNREACHABLE; node_count];
        for (index, &node) in reverse_postorder.iter().enumerate() {
            reverse_postorder_index[node] = index;
        }

        let mut immediate_dominator = vec![None; node_count];
        immediate_dominator[entry] = Some(entry);
        loop {
            let mut changed = false;
            for &node in reverse_postorder.iter().skip(1) {
                let mut known_predecessors = predecessors[node]
                    .iter()
                    .copied()
                    .filter(|&predecessor| immediate_dominator[predecessor].is_some());
                let mut new_dominator = known_predecessors
                    .next()
                    .expect("a reachable non-entry node must have a known predecessor");
                for predecessor in known_predecessors {
                    new_dominator = intersect_dominator_paths(
                        predecessor,
                        new_dominator,
                        &immediate_dominator,
                        &reverse_postorder_index,
                    );
                }
                if immediate_dominator[node] != Some(new_dominator) {
                    immediate_dominator[node] = Some(new_dominator);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        let mut children = vec![Vec::new(); node_count];
        for &node in reverse_postorder.iter().skip(1) {
            let dominator = immediate_dominator[node]
                .expect("every reachable node must have an immediate dominator");
            children[dominator].push(node);
        }

        let mut preorder = vec![Self::UNREACHABLE; node_count];
        let mut postorder = vec![Self::UNREACHABLE; node_count];
        let mut timestamp = 0;
        let mut stack = vec![(entry, false)];
        while let Some((node, exiting)) = stack.pop() {
            if exiting {
                postorder[node] = timestamp;
                timestamp += 1;
                continue;
            }
            preorder[node] = timestamp;
            timestamp += 1;
            stack.push((node, true));
            for &child in children[node].iter().rev() {
                stack.push((child, false));
            }
        }

        Self {
            immediate_dominator,
            children,
            preorder,
            postorder,
        }
    }

    pub(crate) fn is_reachable(&self, node: usize) -> bool {
        self.preorder[node] != Self::UNREACHABLE
    }

    pub(crate) fn dominates(&self, definition: usize, usage: usize) -> bool {
        self.is_reachable(definition)
            && self.is_reachable(usage)
            && self.preorder[definition] <= self.preorder[usage]
            && self.postorder[usage] <= self.postorder[definition]
    }

    /// The closest strict dominator of `node`, or `None` when `node` is unreachable or the root.
    pub(crate) fn immediate_dominator(&self, node: usize) -> Option<usize> {
        self.immediate_dominator[node].filter(|dominator| *dominator != node)
    }

    /// The nodes `node` immediately dominates, which is what a walk of the tree recurses into.
    pub(crate) fn children(&self, node: usize) -> &[usize] {
        &self.children[node]
    }
}

fn intersect_dominator_paths(
    mut left: usize,
    mut right: usize,
    immediate_dominator: &[Option<usize>],
    reverse_postorder_index: &[usize],
) -> usize {
    while left != right {
        while reverse_postorder_index[left] > reverse_postorder_index[right] {
            left = immediate_dominator[left]
                .expect("dominance intersection must stay on the known dominator tree");
        }
        while reverse_postorder_index[right] > reverse_postorder_index[left] {
            right = immediate_dominator[right]
                .expect("dominance intersection must stay on the known dominator tree");
        }
    }
    left
}
