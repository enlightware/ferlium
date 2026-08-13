// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Forwarding of booleans that control flow materializes only to branch on again.
//!
//! Lowering and inlining can turn one predicate into this diamond:
//!
//! ```text
//! condbr predicate, left, right
//! left:  store true  to flag; br join
//! right: store false to flag; br join
//! join:  stack_restore marker; equal = comp_eq flag true; condbr equal, yes, no
//! ```
//!
//! The second comparison and branch recover information the incoming edge already carries. This
//! pass redirects each storing block to `yes` or `no`, retaining on that edge the `stack_restore`s
//! it used to reach on the way. The join then becomes unreachable, and ordinary DCE removes the
//! boolean allocation and stores.
//!
//! A store need not sit in an immediate predecessor of the join. A short-circuit `or` or `and` with
//! three or more arms lowers to a *tree* of stores, whose deeper arms reach the join through a
//! block that only restores the stack:
//!
//! ```text
//! outer: condbr first, left, inner
//! inner: condbr second, right, middle
//! left:   store true  to flag; br join
//! middle: store true  to flag; br forward
//! right:  store false to flag; br forward
//! forward: stack_restore marker; br join
//! join:   equal = comp_eq flag true; condbr equal, yes, no
//! ```
//!
//! So the search walks back from the join to the stores that reach it, through blocks that carry
//! only edge cleanup, and replays that cleanup on each arm it redirects.
//!
//! The proof is intentionally local and linear. The flag must be a local boolean `alloca`; every
//! use must be one known-boolean store or the one final comparison; every block on a walked path
//! must end in an unconditional jump; a store-free block on a path may contain only
//! `stack_restore`s; the join may contain only `stack_restore`s before the comparison; and the
//! stores found must be exactly those the use census saw, which is what proves no other definition
//! reaches the join. Two paths may not meet at one block, since rewriting it would mean duplicating
//! it. General predicate propagation — forwarding a boolean that is *computed* rather than stored
//! as a literal — is a separate optimization with a larger dataflow proof.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    mir::{
        self, BlockId, Function, Operation, OperationKind,
        edit::FunctionEdit,
        pass::budget::{FORWARD_BOOLEAN_BLOCKS, FORWARD_BOOLEAN_REPLAYED_OPERATIONS},
        terminator::{Terminator, TerminatorKind},
        value::ValueId,
    },
    module::id::Id,
    std::logic::bool_type,
};

use super::site::{OperationIndex, OperationSite};

#[derive(Clone, Copy)]
struct Store {
    block: BlockId,
    value: bool,
}

#[derive(Default)]
struct Uses {
    stores: Vec<Store>,
    comparisons: Vec<OperationSite>,
    other: bool,
}

/// One store that reaches the join, and the edge cleanup it must run in place of the blocks the
/// rewrite removes between it and the join.
struct Arm {
    source: BlockId,
    target: BlockId,
    replay: Vec<Operation>,
}

struct Forward {
    arms: Vec<Arm>,
}

/// Bypasses boolean storage diamonds, returning `None` when the function has none.
pub(crate) fn forward_boolean_branches(func: &Function) -> Option<Function> {
    // Restrict the use census to local boolean storage. This takes one definition walk and one
    // operand walk; planning below only visits the uses and predecessors belonging to a candidate.
    let mut uses: FxHashMap<ValueId, Uses> = func
        .blocks()
        .flat_map(|block| func.block(block).operations())
        .filter_map(|operation| {
            if let OperationKind::Alloca { ty } = operation.kind
                && ty == bool_type()
            {
                operation.result_id().map(|id| (id, Uses::default()))
            } else {
                None
            }
        })
        .collect();
    if uses.is_empty() {
        return None;
    }
    let value_uses = census_uses(func, &mut uses);
    if !uses.values().any(|summary| {
        !summary.other && summary.comparisons.len() == 1 && summary.stores.len() >= 2
    }) {
        return None;
    }
    // Building the predecessor map is a separate CFG walk. Most functions have no boolean
    // storage diamond, so defer it until the cheaper definition/use census found a viable shape.
    let incoming = incoming_predecessors(func);

    let mut forwards = Vec::new();
    for join in func.blocks() {
        if let Some(forward) = plan_join(func, join, &incoming, &uses, &value_uses) {
            forwards.push(forward);
        }
    }
    if forwards.is_empty() {
        return None;
    }

    // All plans use the original block identities. Apply every edge rewrite before the one
    // structural cleanup that renumbers blocks.
    let mut edit = FunctionEdit::new(func.clone());
    for forward in forwards {
        for arm in forward.arms {
            let block = edit.block_mut(arm.source);
            block.operations.extend(arm.replay);
            let span = block.terminator.span;
            block.terminator = Terminator::goto(span, arm.target);
        }
    }
    edit.remove_unreachable_blocks();
    edit.merge_blocks_into_predecessors();
    Some(edit.finish_unverified())
}

fn incoming_predecessors(func: &Function) -> Vec<Vec<BlockId>> {
    let mut incoming = vec![Vec::new(); func.blocks().count()];
    for predecessor in func.blocks() {
        match &func.block(predecessor).terminator().kind {
            TerminatorKind::Goto { target } => incoming[target.as_index()].push(predecessor),
            TerminatorKind::CondBr {
                then_target,
                else_target,
                ..
            } => {
                incoming[then_target.as_index()].push(predecessor);
                incoming[else_target.as_index()].push(predecessor);
            }
            TerminatorKind::Invoke { normal, error, .. } => {
                incoming[normal.as_index()].push(predecessor);
                incoming[error.as_index()].push(predecessor);
            }
            TerminatorKind::Yield { resume, .. } => {
                incoming[resume.as_index()].push(predecessor);
            }
            TerminatorKind::Return
            | TerminatorKind::PropagateError
            | TerminatorKind::FailureDuringCleanup => {}
        }
    }
    incoming
}

fn census_uses(func: &Function, uses: &mut FxHashMap<ValueId, Uses>) -> FxHashMap<ValueId, usize> {
    let mut value_uses = FxHashMap::default();
    for block in func.blocks() {
        let basic_block = func.block(block);
        for (index, operation) in basic_block.operations().iter().enumerate() {
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            for (operand_index, operand) in operation.operands.iter().enumerate() {
                let mir::Value::Register(id) = operand else {
                    continue;
                };
                *value_uses.entry(*id).or_default() += 1;
                let Some(summary) = uses.get_mut(id) else {
                    continue;
                };
                match operation.kind {
                    OperationKind::Store if operand_index == 1 => {
                        if let Some(value) = bool_value(func, &operation.operands[0]) {
                            summary.stores.push(Store { block, value });
                        } else {
                            summary.other = true;
                        }
                    }
                    OperationKind::CompareEqual => summary.comparisons.push(site),
                    _ => summary.other = true,
                }
            }
        }
        for operand in basic_block.terminator().operands() {
            if let mir::Value::Register(id) = operand {
                *value_uses.entry(*id).or_default() += 1;
                if let Some(summary) = uses.get_mut(id) {
                    summary.other = true;
                }
            }
        }
    }
    value_uses
}

fn plan_join(
    func: &Function,
    join: BlockId,
    incoming: &[Vec<BlockId>],
    uses: &FxHashMap<ValueId, Uses>,
    value_uses: &FxHashMap<ValueId, usize>,
) -> Option<Forward> {
    let block = func.block(join);
    let (comparison_index, comparison) =
        block.operations().len().checked_sub(1).and_then(|index| {
            let operation = &block.operations()[index];
            matches!(operation.kind, OperationKind::CompareEqual).then_some((index, operation))
        })?;
    let result = comparison.result_id()?;
    let TerminatorKind::CondBr {
        condition: mir::Value::Register(condition),
        then_target,
        else_target,
    } = block.terminator().kind
    else {
        return None;
    };
    if condition != result || value_uses.get(&result) != Some(&1) {
        return None;
    }
    if then_target == join || else_target == join {
        // This rewrite removes the comparison block. A self-edge would keep it reachable and run
        // the copied stack restorations once on the predecessor and again on the join.
        return None;
    }

    let (flag, expected) = compared_boolean_flag(func, comparison)?;
    let summary = uses.get(&flag)?;
    let comparison_site = OperationSite {
        block: join,
        index: OperationIndex::from_index(comparison_index),
    };
    if summary.other
        || summary.comparisons.as_slice() != [comparison_site]
        || summary.stores.len() < 2
        || !block.operations()[..comparison_index]
            .iter()
            .all(|operation| matches!(operation.kind, OperationKind::StackRestore))
    {
        return None;
    }

    // The join's own cleanup runs after whatever the path already replayed, exactly as it did when
    // control still passed through these blocks in order.
    let join_prefix = &block.operations()[..comparison_index];
    let arms = reaching_stores(func, join, summary, incoming)?
        .into_iter()
        .map(|reaching| {
            let mut replay = reaching.replay;
            replay.extend(join_prefix.iter().cloned());
            Arm {
                source: reaching.source,
                target: if reaching.value == expected {
                    then_target
                } else {
                    else_target
                },
                replay,
            }
        })
        .collect();

    Some(Forward { arms })
}

/// One store found by the backward walk, with the cleanup between it and the join.
struct Reaching {
    source: BlockId,
    value: bool,
    replay: Vec<Operation>,
}

/// The stores that reach `join`, walking back through blocks that only carry edge cleanup.
///
/// Returns `None` unless the stores found are exactly those the use census recorded for the flag:
/// that equality is what proves the walk saw every definition reaching the join, and so that
/// redirecting these blocks cannot drop one.
fn reaching_stores(
    func: &Function,
    join: BlockId,
    summary: &Uses,
    incoming: &[Vec<BlockId>],
) -> Option<Vec<Reaching>> {
    let mut found: Vec<Reaching> = Vec::new();
    let mut visited: FxHashSet<BlockId> = FxHashSet::default();
    let mut pending: Vec<(BlockId, Vec<Operation>)> = incoming[join.as_index()]
        .iter()
        .map(|predecessor| (*predecessor, Vec::new()))
        .collect();

    while let Some((block, replay)) = pending.pop() {
        // A repeat is either a cycle or two paths meeting, and both would need this block to be
        // duplicated rather than redirected. A `condbr` with both arms on the join arrives here as
        // the same predecessor twice.
        if block == join || !visited.insert(block) || visited.len() > FORWARD_BOOLEAN_BLOCKS {
            return None;
        }
        if !matches!(
            func.block(block).terminator().kind,
            TerminatorKind::Goto { .. }
        ) {
            return None;
        }

        let mut stores = summary.stores.iter().filter(|store| store.block == block);
        if let Some(store) = stores.next() {
            if stores.next().is_some() {
                return None;
            }
            found.push(Reaching {
                source: block,
                value: store.value,
                replay,
            });
            continue;
        }

        // A store-free block on the path is only passed through if it does nothing an arm cannot
        // replay. Its operations run before whatever the path below it already carries.
        let operations = func.block(block).operations();
        if !operations
            .iter()
            .all(|operation| matches!(operation.kind, OperationKind::StackRestore))
        {
            return None;
        }
        let predecessors = &incoming[block.as_index()];
        if predecessors.is_empty() {
            return None;
        }
        let mut carried = operations.to_vec();
        carried.extend(replay);
        if carried.len() > FORWARD_BOOLEAN_REPLAYED_OPERATIONS {
            return None;
        }
        for predecessor in predecessors {
            pending.push((*predecessor, carried.clone()));
        }
    }

    (found.len() == summary.stores.len()).then_some(found)
}

fn compared_boolean_flag(func: &Function, operation: &Operation) -> Option<(ValueId, bool)> {
    let [left, right] = operation.operands.as_ref() else {
        return None;
    };
    match (left, right) {
        (mir::Value::Register(flag), literal) | (literal, mir::Value::Register(flag)) => {
            bool_value(func, literal).map(|value| (*flag, value))
        }
        _ => None,
    }
}

fn bool_value(func: &Function, value: &mir::Value) -> Option<bool> {
    let literal = match value {
        mir::Value::Constant(id) => &func.constant(*id).representation,
        mir::Value::Pattern(literal) => literal,
        _ => return None,
    };
    literal.as_primitive_ty::<bool>().copied()
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, Location, MirOptimization,
        containers::b,
        hir::value::LiteralValue,
        mir::{Operation, Value, builder::FunctionBuilder, terminator::Terminator},
        types::r#type::Type,
    };

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("branch_forward", src)
    }

    fn body_of<'a>(module: &'a str, name: &str) -> &'a str {
        module
            .split(&format!("fn {name}"))
            .nth(1)
            .unwrap_or_else(|| panic!("module has no `{name}`:\n{module}"))
            .split("\nfn ")
            .next()
            .unwrap()
    }

    /// Integer ordering lowers through an `Ordering` tag, materializes a boolean in two arms, then
    /// the source `if` immediately branches on that boolean. The optimized body should retain only
    /// the first branch and must keep the inlined comparison's stack restoration on both paths.
    #[test]
    fn an_ordering_boolean_is_forwarded_to_its_consumers() {
        let module = optimized("fn choose(x: int) -> int { if x < 10 { 1 } else { 2 } }");
        let body = body_of(&module, "choose");

        assert_eq!(
            body.matches("condbr").count(),
            1,
            "the boolean must not be stored and branched on a second time:\n{body}"
        );
        assert!(
            !body.contains("alloca bool"),
            "the materialized boolean storage must be removed by DCE:\n{body}"
        );
        assert!(
            body.matches("stack_restore").count() >= 2,
            "both redirected paths must still restore the inlined frame:\n{body}"
        );
    }

    /// A short-circuit `or` stores its flag from three arms, two of which reach the join through a
    /// block that only restores the stack. The stores are still all constant, so the whole boolean
    /// must disappear rather than only the arms that happen to sit next to the join.
    #[test]
    fn a_short_circuit_boolean_is_forwarded_through_its_join_path() {
        let module = optimized("fn f(i: int, n: int) { if i < 0 or i >= n { 1 } else { 2 } }");
        let body = body_of(&module, "f");

        assert_eq!(
            body.matches("condbr").count(),
            2,
            "only the two operand tests must remain, not the branch on the stored flag:\n{body}"
        );
        assert!(
            !body.contains("alloca bool"),
            "the flag holding the `or` result must be removed by DCE:\n{body}"
        );
        assert_eq!(
            body.matches("comp_eq").count(),
            2,
            "each operand is compared once, and the flag not at all:\n{body}"
        );
        assert!(
            body.matches("stack_restore").count() >= 3,
            "every redirected arm must still restore the frames it passed:\n{body}"
        );
    }

    /// Redirecting around arbitrary work in the join would silently delete it. Only stack
    /// restoration is part of the recognized edge-cleanup prefix.
    #[test]
    fn a_join_with_other_work_is_refused() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let bool_ty = Type::primitive::<bool>();
        let mut builder = FunctionBuilder::new("other_join_work".into(), Default::default());
        let condition = builder.add_constant(bool_ty, LiteralValue::new_native(true), &env);
        let true_value = condition;
        let false_value = builder.add_constant(bool_ty, LiteralValue::new_native(false), &env);
        let entry = builder.add_block();
        let left = builder.add_block();
        let right = builder.add_block();
        let join = builder.add_block();
        let yes = builder.add_block();
        let no = builder.add_block();

        let flag = builder
            .append_operation(entry, Operation::alloca(span, bool_ty))
            .unwrap();
        builder.set_terminator(
            entry,
            Terminator::cond_br(span, Value::Constant(condition), left, right),
        );
        builder.append_operation(
            left,
            Operation::store(span, Value::Constant(true_value), flag.clone()),
        );
        builder.set_terminator(left, Terminator::goto(span, join));
        builder.append_operation(
            right,
            Operation::store(span, Value::Constant(false_value), flag.clone()),
        );
        builder.set_terminator(right, Terminator::goto(span, join));
        builder.append_operation(join, Operation::check_fuel(span));
        let comparison = builder
            .append_operation(
                join,
                Operation::compare_eq(
                    span,
                    flag,
                    Value::Pattern(b(LiteralValue::new_native(true))),
                ),
            )
            .unwrap();
        builder.set_terminator(join, Terminator::cond_br(span, comparison, yes, no));
        builder.set_terminator(yes, Terminator::ret(span));
        builder.set_terminator(no, Terminator::ret(span));

        let function = builder.finish(env);
        assert!(super::forward_boolean_branches(&function).is_none());
    }
}
