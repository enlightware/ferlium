// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Translation of physical MIR control flow into structured Wasm control flow.
//!
//! This follows Norman Ramsey, *Beyond Relooper: Recursive Translation of Unstructured Control
//! Flow to Structured Control Flow* (ICFP 2022). The translation walks the dominator tree. Each
//! block is classified by its incoming edges: a *loop header* is the target of a backedge and gets
//! a Wasm `loop`; a *merge node* has several forward predecessors, so its code follows a Wasm
//! `block` opened in its immediate dominator, and its predecessors branch out of that `block`.
//! Every other block has a single forward predecessor, its immediate dominator, and is emitted
//! inline in that predecessor's terminator. Any reducible control-flow graph is translated this
//! way; irreducible ones keep the program-counter dispatcher.
//!
//! Among the inline targets of a terminator, the one with the largest dominator subtree continues
//! the enclosing sequence without a test, and the others are nested in Wasm `if`s. A chain of
//! guards thus stays flat, and the nesting of `if`s grows logarithmically with the body size.

use std::cmp::Reverse;

use crate::{
    graph::reverse_postorder,
    mir::{BlockId, Function, dominance::Dominance, terminator::TerminatorKind},
    module::id::Id,
};

use super::body::BodyMode;

/// Bounds the nesting depth of emitted Wasm control constructs, and the recursion producing them.
const MAX_STRUCTURED_DEPTH: usize = 128;

/// One step of a structured body. A sequence of items is emitted in order; only its last item
/// may end without transferring control to the next one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Item {
    /// A Wasm `block` that `body` exits by branching to `follower`. The items after this one in
    /// the sequence start with the code of `follower`.
    Block { follower: BlockId, body: Vec<Item> },
    /// A Wasm `loop` that `body` continues by branching to `header`; `body` starts with `header`.
    /// It is the last item of its sequence.
    Loop { header: BlockId, body: Vec<Item> },
    /// The operations and terminator of a MIR block. The terminator enters each target in
    /// `nested` inside a Wasm `if` at its arm, and `continuation`, when present, without a test:
    /// the items after this one start with its code. Other targets are branches to the label of an
    /// enclosing `block` or `loop`. A node without continuation is the last item of its sequence.
    Node {
        block: BlockId,
        nested: Vec<(BlockId, Vec<Item>)>,
        continuation: Option<BlockId>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ControlFlow {
    /// The items of the entry block's dominator subtree, which covers the whole body.
    Structured(Vec<Item>),
    /// Projections, irreducible control flow and excessive nesting use the program-counter
    /// dispatcher.
    Dispatcher,
}

impl ControlFlow {
    /// Translates the body into structured control flow, or selects the dispatcher.
    ///
    /// Projection bodies resume at suspension points inside their body, so they keep the
    /// dispatcher. So do bodies with unreachable blocks, which the dispatcher emits regardless.
    pub(super) fn of(body: &Function, mode: BodyMode) -> Self {
        if !matches!(mode, BodyMode::Normal)
            || body.blocks().any(|block| {
                matches!(
                    body.block(block).terminator().kind,
                    TerminatorKind::Yield { .. }
                )
            })
        {
            return Self::Dispatcher;
        }
        let successors = body
            .blocks()
            .map(|block| {
                distinct_targets(&body.block(block).terminator().kind)
                    .into_iter()
                    .map(BlockId::as_index)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let entry = body.entry().as_index();
        let order = reverse_postorder(&successors, entry);
        if order.len() != successors.len() {
            return Self::Dispatcher;
        }
        let mut order_index = vec![0; successors.len()];
        for (index, &block) in order.iter().enumerate() {
            order_index[block] = index;
        }
        let dominance = Dominance::of(&successors, entry);

        let mut forward_predecessors = vec![0_usize; successors.len()];
        let mut loop_header = vec![false; successors.len()];
        for (source, targets) in successors.iter().enumerate() {
            for &target in targets {
                if order_index[target] > order_index[source] {
                    forward_predecessors[target] += 1;
                } else if dominance.dominates(target, source) {
                    loop_header[target] = true;
                } else {
                    // A retreating edge that is not a backedge makes the graph irreducible.
                    return Self::Dispatcher;
                }
            }
        }
        // Dominator-tree children follow their parent in reverse postorder.
        let mut weight = vec![1_usize; successors.len()];
        for &block in order.iter().rev() {
            if let Some(dominator) = dominance.immediate_dominator(block) {
                weight[dominator] += weight[block];
            }
        }
        let translation = Translation {
            successors: &successors,
            dominance: &dominance,
            order_index: &order_index,
            merge: forward_predecessors
                .iter()
                .map(|count| *count > 1)
                .collect(),
            loop_header,
            weight,
        };
        let mut items = Vec::new();
        match translation.tree(entry, 0, &mut items) {
            Some(()) => Self::Structured(items),
            None => Self::Dispatcher,
        }
    }
}

/// Returns the distinct targets of a terminator, in the order of its successors.
pub(super) fn distinct_targets(kind: &TerminatorKind) -> Vec<BlockId> {
    let mut targets = Vec::new();
    for target in kind.successors() {
        if !targets.contains(&target) {
            targets.push(target);
        }
    }
    targets
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

struct Translation<'a> {
    successors: &'a [Vec<usize>],
    dominance: &'a Dominance,
    order_index: &'a [usize],
    merge: Vec<bool>,
    loop_header: Vec<bool>,
    /// The size of each block's dominator subtree.
    weight: Vec<usize>,
}

impl Translation<'_> {
    /// Appends the items of `block`'s dominator subtree to `out`, at nesting `depth`.
    fn tree(&self, block: usize, depth: usize, out: &mut Vec<Item>) -> Option<()> {
        if !self.loop_header[block] {
            return self.within(block, depth, out);
        }
        if depth == MAX_STRUCTURED_DEPTH {
            return None;
        }
        let mut body = Vec::new();
        self.within(block, depth + 1, &mut body)?;
        out.push(Item::Loop {
            header: BlockId::from_index(block),
            body,
        });
        Some(())
    }

    /// Appends `block`'s code, wrapped in one `block` per merge child, followed by the trees of
    /// these merge children. Continuations and the last merge tree are tails, so that sequential
    /// regions are translated iteratively and only actual nesting recurses.
    fn within(&self, mut block: usize, depth: usize, out: &mut Vec<Item>) -> Option<()> {
        loop {
            // Children are in reverse postorder; the last one gets the outermost `block`, so that
            // every merge child is emitted after all the blocks that can branch to it.
            let merges = self
                .dominance
                .children(block)
                .iter()
                .copied()
                .filter(|child| self.merge[*child])
                .collect::<Vec<_>>();
            let Some((&last, inner)) = merges.split_last() else {
                let Some(continuation) = self.node(block, depth, out)? else {
                    return Some(());
                };
                if self.loop_header[continuation] {
                    return self.tree(continuation, depth, out);
                }
                block = continuation;
                continue;
            };
            let inner_depth = depth + merges.len();
            if inner_depth > MAX_STRUCTURED_DEPTH {
                return None;
            }
            let mut body = Vec::new();
            if let Some(continuation) = self.node(block, inner_depth, &mut body)? {
                self.tree(continuation, inner_depth, &mut body)?;
            }
            for (index, &merge) in inner.iter().enumerate() {
                let mut enclosing = vec![Item::Block {
                    follower: BlockId::from_index(merge),
                    body,
                }];
                self.tree(merge, inner_depth - index - 1, &mut enclosing)?;
                body = enclosing;
            }
            out.push(Item::Block {
                follower: BlockId::from_index(last),
                body,
            });
            if self.loop_header[last] {
                return self.tree(last, depth, out);
            }
            block = last;
        }
    }

    /// Appends the node item of `block` and returns its continuation.
    fn node(&self, block: usize, depth: usize, out: &mut Vec<Item>) -> Option<Option<usize>> {
        let inline = self.successors[block]
            .iter()
            .copied()
            .filter(|target| {
                self.order_index[*target] > self.order_index[block] && !self.merge[*target]
            })
            .collect::<Vec<_>>();
        debug_assert!(
            inline
                .iter()
                .all(|target| self.dominance.immediate_dominator(*target) == Some(block))
        );
        let continuation = inline
            .iter()
            .copied()
            .max_by_key(|target| (self.weight[*target], Reverse(*target)));
        let mut nested = Vec::new();
        for &target in &inline {
            if Some(target) == continuation {
                continue;
            }
            if depth == MAX_STRUCTURED_DEPTH {
                return None;
            }
            let mut items = Vec::new();
            self.tree(target, depth + 1, &mut items)?;
            nested.push((BlockId::from_index(target), items));
        }
        out.push(Item::Node {
            block: BlockId::from_index(block),
            nested,
            continuation: continuation.map(BlockId::from_index),
        });
        Some(continuation)
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

    fn b(index: usize) -> BlockId {
        BlockId::from_index(index)
    }

    fn span() -> Location {
        Location::new_synthesized()
    }

    fn goto(target: usize) -> Terminator {
        Terminator::goto(span(), b(target))
    }

    fn cond_br(then_target: usize, else_target: usize) -> Terminator {
        Terminator::cond_br(
            span(),
            Value::Constant(ConstantId::from_index(0)),
            b(then_target),
            b(else_target),
        )
    }

    fn switch(cases: &[usize], default: usize) -> Terminator {
        Terminator::switch_variant(
            span(),
            Value::Constant(ConstantId::from_index(0)),
            cases
                .iter()
                .enumerate()
                .map(|(index, target)| (format!("V{index}").into(), b(*target)))
                .collect(),
            b(default),
        )
    }

    fn ret() -> Terminator {
        Terminator::ret(span())
    }

    fn node(block: usize, continuation: Option<usize>) -> Item {
        nesting(block, Vec::new(), continuation)
    }

    fn nesting(block: usize, nested: Vec<(usize, Vec<Item>)>, continuation: Option<usize>) -> Item {
        Item::Node {
            block: b(block),
            nested: nested
                .into_iter()
                .map(|(target, items)| (b(target), items))
                .collect(),
            continuation: continuation.map(b),
        }
    }

    fn structured(terminators: Vec<Terminator>) -> Vec<Item> {
        match ControlFlow::of(&control_flow(terminators), BodyMode::Normal) {
            ControlFlow::Structured(items) => items,
            ControlFlow::Dispatcher => panic!("expected structured control flow"),
        }
    }

    /// The nesting depth of Wasm control constructs.
    fn depth(items: &[Item]) -> usize {
        items
            .iter()
            .map(|item| match item {
                Item::Block { body, .. } | Item::Loop { body, .. } => 1 + depth(body),
                Item::Node { nested, .. } => nested
                    .iter()
                    .map(|(_, items)| 1 + depth(items))
                    .max()
                    .unwrap_or(0),
            })
            .max()
            .unwrap_or(0)
    }

    #[wasm_bindgen_test::wasm_bindgen_test]
    fn sequences_single_predecessor_blocks_inline() {
        assert_eq!(
            structured(vec![goto(1), goto(2), ret()]),
            vec![node(0, Some(1)), node(1, Some(2)), node(2, None)]
        );
        assert_eq!(
            ControlFlow::of(
                &control_flow(vec![goto(1), ret()]),
                BodyMode::ProjectionStart {
                    resume: crate::wasm::abi::DispatchTableSlotId::from_index(0),
                }
            ),
            ControlFlow::Dispatcher,
            "projections resume through the dispatcher"
        );
    }

    #[wasm_bindgen_test::wasm_bindgen_test]
    fn places_merge_nodes_after_blocks_in_their_dominator() {
        // Both arms reach the join, so it follows a `block` that they exit.
        assert_eq!(
            structured(vec![cond_br(1, 2), goto(3), goto(3), ret()]),
            vec![
                Item::Block {
                    follower: b(3),
                    body: vec![
                        nesting(0, vec![(2, vec![node(2, None)])], Some(1)),
                        node(1, None),
                    ],
                },
                node(3, None),
            ]
        );
        // Two merge nodes of one dominator nest in reverse postorder: the later, outer one can be
        // reached from the earlier one.
        assert_eq!(
            structured(vec![cond_br(1, 2), cond_br(3, 4), goto(3), goto(4), ret()]),
            vec![
                Item::Block {
                    follower: b(4),
                    body: vec![
                        Item::Block {
                            follower: b(3),
                            body: vec![
                                nesting(0, vec![(2, vec![node(2, None)])], Some(1)),
                                node(1, None),
                            ],
                        },
                        node(3, None),
                    ],
                },
                node(4, None),
            ]
        );
    }

    #[wasm_bindgen_test::wasm_bindgen_test]
    fn translates_loops_with_several_exits_and_nesting() {
        // Storage order puts the exit before the latch, as physical MIR commonly does.
        assert_eq!(
            structured(vec![goto(1), cond_br(3, 2), ret(), goto(1)]),
            vec![
                node(0, Some(1)),
                Item::Loop {
                    header: b(1),
                    body: vec![
                        nesting(1, vec![(3, vec![node(3, None)])], Some(2)),
                        node(2, None)
                    ],
                },
            ]
        );
        // A loop leaving to a shared exit from its header and from its body, as a `break` does.
        // The header dominates the exit, so the exit follows a `block` inside the `loop`.
        assert_eq!(
            structured(vec![goto(1), cond_br(2, 4), cond_br(4, 3), goto(1), ret()]),
            vec![
                node(0, Some(1)),
                Item::Loop {
                    header: b(1),
                    body: vec![
                        Item::Block {
                            follower: b(4),
                            body: vec![node(1, Some(2)), node(2, Some(3)), node(3, None)],
                        },
                        node(4, None),
                    ],
                },
            ]
        );
        // Nested loops, with a branch in the inner body.
        let items = structured(vec![
            goto(1),
            cond_br(2, 7),
            cond_br(3, 6),
            cond_br(4, 5),
            goto(5),
            goto(2),
            goto(1),
            ret(),
        ]);
        let loops = |items: &[Item]| {
            fn count(items: &[Item]) -> usize {
                items
                    .iter()
                    .map(|item| match item {
                        Item::Loop { body, .. } => 1 + count(body),
                        Item::Block { body, .. } => count(body),
                        Item::Node { nested, .. } => {
                            nested.iter().map(|(_, items)| count(items)).sum()
                        }
                    })
                    .sum()
            }
            count(items)
        };
        assert_eq!(loops(&items), 2);
        // An exit-free loop.
        assert_eq!(
            structured(vec![goto(1), goto(1)]),
            vec![
                node(0, Some(1)),
                Item::Loop {
                    header: b(1),
                    body: vec![node(1, None)],
                },
            ]
        );
    }

    #[wasm_bindgen_test::wasm_bindgen_test]
    fn translates_variant_switches_of_any_arity() {
        let items = structured(vec![
            switch(&[1, 2, 1], 3),
            goto(4),
            goto(4),
            goto(4),
            ret(),
        ]);
        let [Item::Block { body, .. }, _] = items.as_slice() else {
            panic!("expected one join: {items:?}");
        };
        let Item::Node { nested, .. } = &body[0] else {
            panic!("expected the switch first: {body:?}");
        };
        assert_eq!(nested.len(), 2, "three targets: one continues, two nest");
    }

    #[wasm_bindgen_test::wasm_bindgen_test]
    fn keeps_guard_chains_flat() {
        // Each guard exits to its own return block and continues to the next guard.
        let guard_count = 4 * MAX_STRUCTURED_DEPTH;
        let mut terminators = Vec::with_capacity(guard_count * 2 + 1);
        for guard in 0..guard_count {
            terminators.push(cond_br(guard_count + 1 + guard, guard + 1));
        }
        terminators.push(ret());
        terminators.extend((0..guard_count).map(|_| ret()));
        let items = structured(terminators);
        assert_eq!(items.len(), guard_count + 1);
        assert_eq!(depth(&items), 1);
    }

    #[wasm_bindgen_test::wasm_bindgen_test]
    fn keeps_the_dispatcher_for_irreducible_or_unreachable_blocks() {
        // The cycle between 1 and 2 has two entries.
        assert_eq!(
            ControlFlow::of(
                &control_flow(vec![cond_br(1, 2), cond_br(2, 3), goto(1), ret()]),
                BodyMode::Normal
            ),
            ControlFlow::Dispatcher
        );
        assert_eq!(
            ControlFlow::of(&control_flow(vec![goto(2), ret(), ret()]), BodyMode::Normal),
            ControlFlow::Dispatcher
        );
    }
}
