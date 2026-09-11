// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Reduce equality decision chains over a small known domain to one test.
//!
//! For each possible outcome, follow tests of the same unchanged operand to its destination.
//! If one outcome reaches one destination and all others reach another, test that outcome once.
//! This uses result domains, not identities or laws of the function that produced the value.
//!
//! Only empty forwarding blocks and single equality tests whose result has no other users may
//! be bypassed. Everything else, including stack restoration, is a destination rather than an
//! operation to hoist or discard. Thus calls, ownership, failure and cleanup retain their order.
//!
//! A returned/stored Boolean can instead end in a literal store on one arm and a computed
//! predicate store on the other. Evaluate those small tails over the same domain, then materialize
//! the singleton predicate (and, if necessary, its Boolean negation) without branching. Both tails
//! must have identical stores/cleanup/continuations and no other incoming edges. No calls or writes
//! except the one Boolean store are crossed, and no computed result may escape its original tail.

use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use super::{
    budget::{OUTCOME_BOOLEAN_OPERATIONS, OUTCOME_BRANCH_BLOCKS},
    dataflow::{self, Const, Outcome},
    peephole::bool_value,
};
use crate::{
    hir::value::LiteralValue,
    mir::{
        self, BlockId, Function, Operation, OperationKind, ValueId,
        edit::FunctionEdit,
        terminator::{Terminator, TerminatorKind},
    },
    module::ModuleEnv,
    std::logic::bool_type,
};

struct Test<'a> {
    operand: &'a mir::Value,
    pattern: Outcome,
    yes: BlockId,
    no: BlockId,
}

/// The last operation must define precisely the condition used by this block.
fn test(func: &Function, block: BlockId) -> Option<Test<'_>> {
    let block = func.block(block);
    let TerminatorKind::CondBr {
        condition,
        then_target,
        else_target,
    } = &block.terminator().kind
    else {
        return None;
    };
    let operation = block.operations().last()?;
    if operation.kind != OperationKind::CompareEqual
        || operation.result_id().map(mir::Value::Register).as_ref() != Some(condition)
    {
        return None;
    }
    let mir::Value::Pattern(pattern) = &operation.operands[1] else {
        return None;
    };
    Some(Test {
        operand: &operation.operands[0],
        pattern: Outcome::pattern(pattern)?,
        yes: *then_target,
        no: *else_target,
    })
}

/// A cheap structural gate before paying for dataflow or the use census.
fn has_chain(func: &Function) -> bool {
    func.blocks().any(|block| {
        test(func, block).is_some_and(|first| {
            if is_boolean_tail(func, first.yes) && is_boolean_tail(func, first.no) {
                return true;
            }
            [first.yes, first.no].into_iter().any(|mut successor| {
                // Match the forwarding blocks destination can cross, independently of whether
                // another pass has already removed them. The same bound also stops empty cycles.
                for _ in 0..OUTCOME_BRANCH_BLOCKS {
                    if let Some(target) = empty_forwarding_target(func, successor) {
                        successor = target;
                    } else {
                        return func.block(successor).operations().len() == 1
                            && test(func, successor)
                                .is_some_and(|next| next.operand == first.operand);
                    }
                }
                false
            })
        })
    })
}

/// Only comparisons, stack restoration, and one Boolean store are candidates. Comparisons must
/// precede the store; the semantic evaluator below checks their actual operands and stored value.
fn is_boolean_tail(func: &Function, block: BlockId) -> bool {
    let body = func.block(block);
    if !matches!(
        body.terminator().kind,
        TerminatorKind::Goto { .. } | TerminatorKind::Return
    ) || body.operations().len() > OUTCOME_BOOLEAN_OPERATIONS
    {
        return false;
    }
    let mut store = false;
    for operation in body.operations() {
        match operation.kind {
            OperationKind::CompareEqual if !store => {}
            OperationKind::StackRestore => {}
            OperationKind::Store if !store => {
                store = true;
            }
            _ => return false,
        }
    }
    store
}

enum BooleanResult {
    Constant(bool),
    Predicate { outcome: Outcome, positive: bool },
}

struct BooleanRewrite {
    block: BlockId,
    template: BlockId,
    result: BooleanResult,
}

/// Removing the comparisons must leave precisely the same operations and continuation. Source
/// spans may differ; stack marker identities, destination storage and their order must not.
fn same_boolean_tail(func: &Function, left: BlockId, right: BlockId) -> bool {
    let left = func.block(left);
    let right = func.block(right);
    let retained = |operation: &&Operation| operation.kind != OperationKind::CompareEqual;
    let mut left_ops = left.operations().iter().filter(retained);
    let mut right_ops = right.operations().iter().filter(retained);
    loop {
        match (left_ops.next(), right_ops.next()) {
            (Some(a), Some(b)) if a.kind == b.kind => {
                let same = if a.kind == OperationKind::Store {
                    a.operands[1] == b.operands[1]
                } else {
                    a.operands == b.operands
                };
                if !same {
                    return false;
                }
            }
            (None, None) => return left.terminator().kind == right.terminator().kind,
            _ => return false,
        }
    }
}

fn tail_results_are_local(
    func: &Function,
    block: BlockId,
    uses: &FxHashMap<ValueId, usize>,
) -> bool {
    let body = func.block(block);
    body.operations()
        .iter()
        .filter_map(Operation::result_id)
        .all(|id| {
            let local = body
                .operations()
                .iter()
                .flat_map(|op| op.operands.iter())
                .filter(|operand| **operand == mir::Value::Register(id))
                .count();
            uses.get(&id).copied().unwrap_or(0) == local
        })
}

fn boolean_tail_value(
    func: &Function,
    block: BlockId,
    operand: &mir::Value,
    outcome: Outcome,
) -> Option<bool> {
    let mut values: SmallVec<[(ValueId, bool); 4]> = SmallVec::new();
    let mut result = None;
    let value = |operand: &mir::Value, values: &[(ValueId, bool)]| {
        bool_value(func, operand).or_else(|| {
            let mir::Value::Register(id) = operand else {
                return None;
            };
            values
                .iter()
                .rev()
                .find_map(|(known, value)| (*known == *id).then_some(*value))
        })
    };
    for operation in func.block(block).operations() {
        match operation.kind {
            OperationKind::CompareEqual => {
                let mir::Value::Pattern(pattern) = &operation.operands[1] else {
                    return None;
                };
                let equal = if &operation.operands[0] == operand {
                    outcome == Outcome::pattern(pattern)?
                } else {
                    value(&operation.operands[0], &values)? == *pattern.as_primitive_ty::<bool>()?
                };
                values.push((operation.result_id()?, equal));
            }
            OperationKind::Store => {
                result = Some(value(&operation.operands[0], &values)?);
            }
            OperationKind::StackRestore => {}
            _ => return None,
        }
    }
    result
}

fn plan_boolean_result(
    func: &Function,
    block: BlockId,
    test: &Test<'_>,
    outcomes: impl Iterator<Item = Outcome>,
    uses: &FxHashMap<ValueId, usize>,
    incoming: &FxHashMap<BlockId, usize>,
) -> Option<BooleanRewrite> {
    if test.yes == test.no || [test.yes, test.no].contains(&block) {
        return None;
    }
    for tail in [test.yes, test.no] {
        // Do not copy a tail shared with another caller into this root.
        if !is_boolean_tail(func, tail)
            || incoming.get(&tail) != Some(&1)
            || !tail_results_are_local(func, tail, uses)
        {
            return None;
        }
    }
    if !same_boolean_tail(func, test.yes, test.no) {
        return None;
    }
    let values: Option<SmallVec<[_; 8]>> = outcomes
        .map(|outcome| {
            let tail = if outcome == test.pattern {
                test.yes
            } else {
                test.no
            };
            boolean_tail_value(func, tail, test.operand, outcome).map(|value| (outcome, value))
        })
        .collect();
    let values = values?;
    let &(_, first) = values.first()?;
    let result = if values.iter().all(|(_, value)| *value == first) {
        BooleanResult::Constant(first)
    } else {
        // Prefer a positive singleton: its complement needs one extra Boolean negation.
        let (outcome, positive) = [true, false].into_iter().find_map(|positive| {
            let mut selected = values.iter().filter(|(_, value)| *value == positive);
            let &(outcome, _) = selected.next()?;
            selected.next().is_none().then_some((outcome, positive))
        })?;
        BooleanResult::Predicate { outcome, positive }
    };
    Some(BooleanRewrite {
        block,
        template: test.yes,
        result,
    })
}

fn outcome_pattern(outcome: Outcome) -> LiteralValue {
    match outcome.constant() {
        Const::Literal(value) => value,
        Const::VariantTag(tag) => LiteralValue::new_variant_tag(tag),
        _ => unreachable!("outcomes are integers or tags"),
    }
}

fn empty_forwarding_target(func: &Function, block: BlockId) -> Option<BlockId> {
    let body = func.block(block);
    if body.operations().is_empty()
        && let TerminatorKind::Goto { target } = body.terminator().kind
    {
        Some(target)
    } else {
        None
    }
}

/// Returns a destination and whether an additional comparison was bypassed.
fn destination(
    func: &Function,
    root: BlockId,
    mut block: BlockId,
    operand: &mir::Value,
    outcome: Outcome,
    uses: &FxHashMap<ValueId, usize>,
) -> Option<(BlockId, bool)> {
    let mut compared = false;
    for _ in 0..OUTCOME_BRANCH_BLOCKS {
        if block == root {
            return None;
        }
        let body = func.block(block);
        if let Some(target) = empty_forwarding_target(func, block) {
            block = target;
        } else if body.operations().len() == 1
            && let Some(next) = test(func, block)
            && next.operand == operand
            && uses.get(&body.operations()[0].result_id()?) == Some(&1)
        {
            compared = true;
            block = if outcome == next.pattern {
                next.yes
            } else {
                next.no
            };
        } else {
            return Some((block, compared));
        }
    }
    // Includes cycles: no finite destination was proved within the local work bound.
    None
}

pub(crate) fn simplify_outcome_branches(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    if !has_chain(func) {
        return None;
    }
    let analysis = dataflow::analyze(func, env);
    let mut uses = FxHashMap::default();
    let mut incoming = FxHashMap::default();
    for block in func.blocks() {
        let body = func.block(block);
        for successor in body.terminator().successors() {
            *incoming.entry(successor).or_insert(0) += 1;
        }
        for operand in body
            .operations()
            .iter()
            .flat_map(|op| op.operands.iter())
            .chain(body.terminator().operands())
        {
            if let mir::Value::Register(id) = operand {
                *uses.entry(*id).or_insert(0) += 1;
            }
        }
    }
    let mut rewrites = Vec::new();
    let mut booleans = Vec::new();
    for block in func.blocks() {
        let Some(first) = test(func, block) else {
            continue;
        };
        // Retarget the existing predicate rather than computing an extra one. If it has another
        // consumer, changing its meaning would be invalid and retaining it could add runtime work.
        let result = func
            .block(block)
            .operations()
            .last()
            .unwrap()
            .result_id()
            .unwrap();
        if uses.get(&result) != Some(&1) {
            continue;
        }
        let mut state = analysis.entry_state(block);
        for operation in func.block(block).operations() {
            analysis.step(func, env, operation, &mut state);
        }
        let fact = if let Some(place) = analysis.tracked_place_of(first.operand) {
            state.place(place)
        } else if let mir::Value::Register(id) = first.operand {
            state.register(*id).cloned().unwrap_or_default()
        } else {
            continue;
        };
        let Some(outcomes) = fact.outcomes() else {
            continue;
        };
        if let Some(rewrite) =
            plan_boolean_result(func, block, &first, outcomes.clone(), &uses, &incoming)
        {
            booleans.push(rewrite);
            continue;
        }
        let destinations: Option<SmallVec<[_; 8]>> = outcomes
            .map(|outcome| {
                let target = if outcome == first.pattern {
                    first.yes
                } else {
                    first.no
                };
                destination(func, block, target, first.operand, outcome, &uses)
                    .map(|(target, compared)| (outcome, target, compared))
            })
            .collect();
        let Some(destinations) = destinations else {
            continue;
        };
        if !destinations.iter().any(|(_, _, compared)| *compared) {
            continue;
        }
        // A singleton destination is the complement of every other outcome in the domain.
        // If there are more than two destinations, retain the existing decision chain.
        // Singleton domains are left to constant folding.
        for (index, &(outcome, yes, _)) in destinations.iter().enumerate() {
            let mut others = destinations
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != index)
                .map(|(_, (_, target, _))| *target);
            let Some(no) = others.next() else { continue };
            if others.all(|target| target == no) {
                rewrites.push((block, first.operand.clone(), outcome, yes, no));
                break;
            }
        }
    }
    if rewrites.is_empty() && booleans.is_empty() {
        return None;
    }
    let mut edit = FunctionEdit::new(func.clone());
    for (block, operand, outcome, yes, no) in rewrites {
        let span = edit.block(block).terminator.span;
        let terminator = if yes == no {
            Terminator::goto(span, yes)
        } else {
            let pattern = outcome_pattern(outcome);
            let comparison = edit.block_mut(block).operations.last_mut().unwrap();
            debug_assert_eq!(comparison.operands[0], operand);
            comparison.operands[1] = mir::Value::Pattern(Box::new(pattern));
            let condition = mir::Value::Register(comparison.result_id().unwrap());
            Terminator::cond_br(span, condition, yes, no)
        };
        edit.block_mut(block).terminator = terminator;
    }
    for rewrite in booleans {
        let span = edit.block(rewrite.block).terminator.span;
        let value = match rewrite.result {
            BooleanResult::Constant(value) => mir::Value::Constant(edit.add_constant(
                bool_type(),
                LiteralValue::new_native(value),
                &env,
            )),
            BooleanResult::Predicate { outcome, positive } => {
                let comparison = edit.block_mut(rewrite.block).operations.last_mut().unwrap();
                comparison.operands[1] = mir::Value::Pattern(Box::new(outcome_pattern(outcome)));
                let value = mir::Value::Register(comparison.result_id().unwrap());
                if positive {
                    value
                } else {
                    let mut negate = Operation::compare_eq(
                        span,
                        value,
                        mir::Value::Pattern(Box::new(LiteralValue::new_native(false))),
                    );
                    let value = edit.assign_new_result(&mut negate).unwrap();
                    edit.block_mut(rewrite.block).operations.push(negate);
                    value
                }
            }
        };
        // Read the immutable original template: plans may overlap in the original CFG, but no
        // rewrite can change which cleanup sequence or storage this proof selected.
        let template = func.block(rewrite.template);
        let block = edit.block_mut(rewrite.block);
        for operation in template.operations() {
            if operation.kind == OperationKind::CompareEqual {
                continue;
            }
            let mut operation = operation.clone();
            if operation.kind == OperationKind::Store {
                operation.operands[0] = value.clone();
            }
            block.operations.push(operation);
        }
        block.terminator = template.terminator().clone();
    }
    edit.remove_unreachable_blocks();
    edit.merge_blocks_into_predecessors();
    Some(edit.finish_unverified())
}

#[cfg(test)]
mod tests {
    use ustr::ustr;

    use super::{super::dce::remove_dead_trivial_results, *};
    use crate::{
        CompilerSession, ExecutionTarget, Location, MirOptimization, Path,
        hir::{function::ArgConvention, native_functions::NativeFnNN},
        mir::{Operation, ParameterKind, builder::FunctionBuilder},
        module::Module,
        std::{logic::bool_type, ordering::ordering_type},
        types::effects::no_effects,
    };

    #[derive(Clone, Copy)]
    enum Shape {
        Plain,
        Cleanup,
        EscapingTest,
        RootTestUsed,
        Cycle,
        DifferentValue,
        Forwarded,
        ForwardCycle,
        Converged,
    }

    fn chain(session: &CompilerSession, shape: Shape) -> Function {
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("chain".into(), Default::default());
        let input = mir::Value::Parameter(builder.add_parameter(
            ordering_type(),
            ParameterKind::Parameter(ArgConvention::Let),
        ));
        let other = mir::Value::Parameter(builder.add_parameter(
            ordering_type(),
            ParameterKind::Parameter(ArgConvention::Let),
        ));
        let root = builder.add_block();
        let next = builder.add_block();
        let yes = builder.add_block();
        let no = builder.add_block();
        let tag = builder
            .append_operation(root, Operation::extract_tag(span, input))
            .unwrap();
        let other_tag = builder
            .append_operation(root, Operation::extract_tag(span, other))
            .unwrap();
        let first = builder
            .append_operation(
                root,
                Operation::compare_eq(
                    span,
                    tag.clone(),
                    mir::Value::Pattern(Box::new(LiteralValue::new_variant_tag("Less".into()))),
                ),
            )
            .unwrap();
        let continuation = if matches!(shape, Shape::Forwarded | Shape::ForwardCycle) {
            let forward = builder.add_block();
            builder.set_terminator(
                forward,
                Terminator::goto(
                    span,
                    if matches!(shape, Shape::ForwardCycle) {
                        forward
                    } else {
                        next
                    },
                ),
            );
            forward
        } else {
            next
        };
        builder.set_terminator(
            root,
            Terminator::cond_br(span, first.clone(), yes, continuation),
        );
        if matches!(shape, Shape::Cleanup) {
            let marker = builder
                .append_operation(next, Operation::stack_save(span))
                .unwrap();
            builder.append_operation(next, Operation::stack_restore(span, marker));
        }
        let second = builder
            .append_operation(
                next,
                Operation::compare_eq(
                    span,
                    if matches!(shape, Shape::DifferentValue) {
                        other_tag
                    } else {
                        tag
                    },
                    mir::Value::Pattern(Box::new(LiteralValue::new_variant_tag("Equal".into()))),
                ),
            )
            .unwrap();
        builder.set_terminator(
            next,
            Terminator::cond_br(
                span,
                second.clone(),
                yes,
                if matches!(shape, Shape::Cycle) {
                    next
                } else if matches!(shape, Shape::Converged) {
                    yes
                } else {
                    no
                },
            ),
        );
        // The first predicate may have consumers besides its branch; its value must not change.
        for (block, value) in [(yes, first), (no, second)] {
            if matches!(
                (shape, block == yes),
                (Shape::RootTestUsed, true) | (Shape::EscapingTest, false)
            ) {
                let slot = builder
                    .append_operation(block, Operation::alloca(span, bool_type()))
                    .unwrap();
                builder.append_operation(block, Operation::store(span, value, slot));
            }
            builder.set_terminator(block, Terminator::ret(span));
        }
        builder.finish(session.module_env())
    }

    #[test]
    fn semantic_tag_chain_uses_the_singleton_complement() {
        let session = CompilerSession::new();
        let simplified =
            simplify_outcome_branches(&chain(&session, Shape::Plain), session.module_env())
                .unwrap();
        let simplified = FunctionEdit::new(simplified).finish(session.module_env());
        let entry = simplified.block(simplified.entry());
        let last = entry.operations().last().unwrap();
        assert!(last.kind == OperationKind::CompareEqual);
        let mir::Value::Pattern(pattern) = &last.operands[1] else {
            panic!()
        };
        assert_eq!(pattern.as_variant_tag(), Some(&ustr("Greater")));
        assert_eq!(
            simplified
                .blocks()
                .filter(|block| matches!(
                    simplified.block(*block).terminator().kind,
                    TerminatorKind::CondBr { .. }
                ))
                .count(),
            1
        );
    }

    #[test]
    fn preserves_cleanup_other_values_external_uses_and_cycles() {
        let session = CompilerSession::new();
        for shape in [
            Shape::Cleanup,
            Shape::EscapingTest,
            Shape::Cycle,
            Shape::DifferentValue,
            Shape::ForwardCycle,
        ] {
            assert!(
                simplify_outcome_branches(&chain(&session, shape), session.module_env()).is_none()
            );
        }
    }

    #[test]
    fn does_not_add_a_test_to_preserve_other_predicate_consumers() {
        let session = CompilerSession::new();
        assert!(
            simplify_outcome_branches(&chain(&session, Shape::RootTestUsed), session.module_env())
                .is_none()
        );
    }

    #[test]
    fn recognizes_chains_through_empty_forwarding_blocks() {
        let session = CompilerSession::new();
        let simplified =
            simplify_outcome_branches(&chain(&session, Shape::Forwarded), session.module_env())
                .unwrap();
        let simplified = FunctionEdit::new(simplified).finish(session.module_env());
        assert_eq!(
            simplified
                .blocks()
                .filter(|block| matches!(
                    simplified.block(*block).terminator().kind,
                    TerminatorKind::CondBr { .. }
                ))
                .count(),
            1
        );
    }

    #[test]
    fn converging_outcomes_remove_the_branch_and_leave_a_collectable_test() {
        let session = CompilerSession::new();
        let simplified =
            simplify_outcome_branches(&chain(&session, Shape::Converged), session.module_env())
                .unwrap();
        let simplified = FunctionEdit::new(simplified).finish(session.module_env());
        assert!(simplified.blocks().all(|block| !matches!(
            simplified.block(block).terminator().kind,
            TerminatorKind::CondBr { .. }
        )));
        assert!(simplified.blocks().any(|block| {
            simplified
                .block(block)
                .operations()
                .iter()
                .any(|operation| operation.kind == OperationKind::CompareEqual)
        }));
        let cleaned = remove_dead_trivial_results(&simplified).unwrap();
        let cleaned = FunctionEdit::new(cleaned).finish(session.module_env());
        assert!(cleaned.blocks().all(|block| {
            cleaned
                .block(block)
                .operations()
                .iter()
                .all(|operation| operation.kind != OperationKind::CompareEqual)
        }));
    }

    #[test]
    fn host_domains_simplify_without_assuming_operand_laws() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let path = Path::single_str("host");
        let mut host = Module::new(session.modules().next_id(), path.clone());
        host.add_function(
            "compare".into(),
            NativeFnNN::from_rust_ordering_code(|a: isize, b: isize| b.cmp(&a)).description(
                ["a", "b"],
                "Reversed host ordering",
                no_effects(),
            ),
        );
        host.add_function(
            "ordinary".into(),
            NativeFnNN::from_rust(isize::wrapping_sub).description(
                ["a", "b"],
                "Unrestricted integer",
                no_effects(),
            ),
        );
        session.register_module(path, host);
        let source = "fn classify(a: int, b: int) -> int {
            match host::compare(a, b) { -1 => 7, 0 => 7, _ => 9 }
        }
        fn ordinary(a: int, b: int) -> bool {
            match host::ordinary(a, b) { -1 => true, 0 => true, _ => false }
        }
        fn predicate(a: int, b: int) -> bool {
            match host::compare(a, b) { -1 => true, 0 => true, _ => false }
        }
        fn main() { (classify(9, 2), classify(2, 9), classify(3, 3), ordinary(1, 9), predicate(9, 2), predicate(2, 9), predicate(3, 3)) }";
        let module = session
            .compile_for(
                ExecutionTarget::Mir,
                source,
                "chains",
                Path::single_str("chains"),
            )
            .unwrap()
            .module_id;
        let mir = session.emit_mir_module(module);
        let body = mir
            .split("fn classify(")
            .nth(1)
            .unwrap()
            .split("\nfn ")
            .next()
            .unwrap();
        assert_eq!(body.matches("comp_eq ").count(), 1, "{body}");
        assert_eq!(body.matches("call host::compare(").count(), 1, "{body}");
        let body = mir
            .split("fn ordinary(")
            .nth(1)
            .unwrap()
            .split("\nfn ")
            .next()
            .unwrap();
        assert_eq!(body.matches("comp_eq ").count(), 2, "{body}");
        let body = mir
            .split("fn predicate(")
            .nth(1)
            .unwrap()
            .split("\nfn ")
            .next()
            .unwrap();
        assert!(!body.contains("condbr "), "{body}");
        assert_eq!(body.matches("call host::compare(").count(), 1, "{body}");
        let optimized = session.eval_mir("optimized_chains", source);
        session.set_mir_optimization(MirOptimization::Disabled);
        let raw = session.eval_mir("raw_chains", source);
        assert_eq!(optimized, raw);
        assert_eq!(optimized, "(7, 9, 7, false, true, false, true)");
    }

    #[test]
    fn integer_and_float_comparison_branches_use_one_code_test() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let source = "fn int_le(a: int, b: int) -> int { if a <= b { 7 } else { 9 } }
            fn float_le(a: float, b: float) -> int { if a <= b { 7 } else { 9 } }
            fn main() { (int_le(2, 1), int_le(1, 1), float_le(-0.0, 0.0), float_le(2.0, 1.0)) }";
        let mir = session.emit_mir("std_chains", source);
        for name in ["int_le", "float_le"] {
            let body = mir
                .split(&format!("fn {name}("))
                .nth(1)
                .unwrap()
                .split("\nfn ")
                .next()
                .unwrap();
            assert_eq!(body.matches("comp_eq ").count(), 1, "{body}");
            assert_eq!(body.matches("condbr ").count(), 1, "{body}");
        }
        let optimized = session.eval_mir("optimized_std_chains", source);
        session.set_mir_optimization(MirOptimization::Disabled);
        assert_eq!(optimized, session.eval_mir("raw_std_chains", source));
        assert_eq!(optimized, "(9, 7, 7, 9)");
    }

    #[derive(Clone, Copy)]
    enum BooleanShape {
        Positive,
        Negative,
        Constant,
        DifferentCleanup,
        DifferentOperand,
        ExtraWrite,
        SharedTail,
    }

    fn boolean_result_chain(session: &CompilerSession, shape: BooleanShape) -> Function {
        let span = Location::new_synthesized();
        let env = session.module_env();
        let mut builder = FunctionBuilder::new("boolean_tail".into(), Default::default());
        let input = mir::Value::Parameter(builder.add_parameter(
            ordering_type(),
            ParameterKind::Parameter(ArgConvention::Let),
        ));
        let other = mir::Value::Parameter(builder.add_parameter(
            ordering_type(),
            ParameterKind::Parameter(ArgConvention::Let),
        ));
        let flag = mir::Value::Parameter(
            builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let)),
        );
        let destination =
            mir::Value::Parameter(builder.add_parameter(bool_type(), ParameterKind::Return));
        let entry = builder.add_block();
        let root = builder.add_block();
        let yes = builder.add_block();
        let no = builder.add_block();
        let tag = builder
            .append_operation(entry, Operation::extract_tag(span, input))
            .unwrap();
        let other_tag = builder
            .append_operation(entry, Operation::extract_tag(span, other))
            .unwrap();
        let marker = builder
            .append_operation(entry, Operation::stack_save(span))
            .unwrap();
        let scratch = builder
            .append_operation(entry, Operation::alloca(span, bool_type()))
            .unwrap();
        let later_marker = builder
            .append_operation(entry, Operation::stack_save(span))
            .unwrap();
        if matches!(shape, BooleanShape::SharedTail) {
            let flag = builder
                .append_operation(entry, Operation::load(span, flag))
                .unwrap();
            builder.set_terminator(entry, Terminator::cond_br(span, flag, root, yes));
        } else {
            builder.set_terminator(entry, Terminator::goto(span, root));
        }
        let first = builder
            .append_operation(
                root,
                Operation::compare_eq(
                    span,
                    tag.clone(),
                    mir::Value::Pattern(Box::new(LiteralValue::new_variant_tag("Less".into()))),
                ),
            )
            .unwrap();
        builder.set_terminator(root, Terminator::cond_br(span, first, yes, no));
        let literal = builder.add_constant(
            bool_type(),
            LiteralValue::new_native(!matches!(
                shape,
                BooleanShape::Positive | BooleanShape::Constant
            )),
            &env,
        );
        if matches!(shape, BooleanShape::ExtraWrite) {
            builder.append_operation(
                yes,
                Operation::store(span, mir::Value::Constant(literal), scratch),
            );
        }
        builder.append_operation(yes, Operation::stack_restore(span, marker.clone()));
        builder.append_operation(
            yes,
            Operation::store(span, mir::Value::Constant(literal), destination.clone()),
        );
        builder.set_terminator(yes, Terminator::ret(span));
        let result = builder
            .append_operation(
                no,
                Operation::compare_eq(
                    span,
                    if matches!(shape, BooleanShape::DifferentOperand) {
                        other_tag
                    } else {
                        tag
                    },
                    mir::Value::Pattern(Box::new(LiteralValue::new_variant_tag(
                        if matches!(shape, BooleanShape::Constant) {
                            "Less"
                        } else {
                            "Equal"
                        }
                        .into(),
                    ))),
                ),
            )
            .unwrap();
        builder.append_operation(
            no,
            Operation::stack_restore(
                span,
                if matches!(shape, BooleanShape::DifferentCleanup) {
                    later_marker
                } else {
                    marker
                },
            ),
        );
        builder.append_operation(no, Operation::store(span, result, destination));
        builder.set_terminator(no, Terminator::ret(span));
        builder.finish(env)
    }

    #[test]
    fn materializes_boolean_domains_and_preserves_real_cleanup() {
        let session = CompilerSession::new();
        for (shape, comparisons) in [
            (BooleanShape::Positive, 1),
            (BooleanShape::Negative, 2),
            (BooleanShape::Constant, 0),
        ] {
            let original = boolean_result_chain(&session, shape);
            let simplified = simplify_outcome_branches(&original, session.module_env()).unwrap();
            let simplified = remove_dead_trivial_results(&simplified).unwrap_or(simplified);
            let simplified = FunctionEdit::new(simplified).finish(session.module_env());
            assert!(simplified.blocks().all(|block| !matches!(
                simplified.block(block).terminator().kind,
                TerminatorKind::CondBr { .. }
            )));
            let operations: Vec<_> = simplified
                .blocks()
                .flat_map(|block| simplified.block(block).operations())
                .collect();
            assert_eq!(
                operations
                    .iter()
                    .filter(|operation| operation.kind == OperationKind::CompareEqual)
                    .count(),
                comparisons
            );
            assert_eq!(
                operations
                    .iter()
                    .filter(|operation| operation.kind == OperationKind::Store)
                    .count(),
                1
            );
            assert_eq!(
                operations
                    .iter()
                    .filter(|operation| operation.kind == OperationKind::StackRestore)
                    .count(),
                1
            );
            assert!(
                operations
                    .iter()
                    .any(|operation| matches!(operation.kind, OperationKind::Alloca { .. }))
            );
            assert!(simplified.operation_count() <= original.operation_count());
        }
    }

    #[test]
    fn boolean_results_reject_unrelated_values_writes_cleanup_and_shared_tails() {
        let session = CompilerSession::new();
        for shape in [
            BooleanShape::DifferentCleanup,
            BooleanShape::DifferentOperand,
            BooleanShape::ExtraWrite,
            BooleanShape::SharedTail,
        ] {
            assert!(
                simplify_outcome_branches(
                    &boolean_result_chain(&session, shape),
                    session.module_env()
                )
                .is_none()
            );
        }
    }

    #[test]
    fn boolean_planner_rejects_extra_writes_without_the_structural_gate() {
        let session = CompilerSession::new();
        // The positive control ensures the census and domain actually permit a rewrite; the
        // extra-write case must be rejected by the planner itself, independently of has_chain.
        for (shape, accepted) in [
            (BooleanShape::Positive, true),
            (BooleanShape::ExtraWrite, false),
        ] {
            let function = boolean_result_chain(&session, shape);
            let (root, first) = function
                .blocks()
                .find_map(|block| test(&function, block).map(|first| (block, first)))
                .unwrap();
            let mut uses = FxHashMap::default();
            let mut incoming = FxHashMap::default();
            for block in function.blocks() {
                let body = function.block(block);
                for successor in body.terminator().successors() {
                    *incoming.entry(successor).or_insert(0) += 1;
                }
                for operand in body
                    .operations()
                    .iter()
                    .flat_map(|operation| operation.operands.iter())
                    .chain(body.terminator().operands())
                {
                    if let mir::Value::Register(id) = operand {
                        *uses.entry(*id).or_insert(0) += 1;
                    }
                }
            }
            let outcomes = ["Less", "Equal", "Greater"]
                .into_iter()
                .map(|tag| Outcome::Tag(tag.into()));
            assert_eq!(
                plan_boolean_result(&function, root, &first, outcomes, &uses, &incoming).is_some(),
                accepted
            );
        }
    }

    #[test]
    fn native_boolean_wrappers_are_branchless_without_changing_results() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let source = "fn le(a: int, b: int) -> bool { a <= b }
            fn ge(a: int, b: int) -> bool { a >= b }
            fn float_le(a: float, b: float) -> bool { a <= b }
            fn main() { (le(1, 2), le(2, 1), le(1, 1), ge(1, 2), ge(2, 1), ge(1, 1), float_le(-0.0, 0.0), float_le(2.0, 1.0)) }";
        let mir = session.emit_mir("boolean_values", source);
        for name in ["le", "ge", "float_le"] {
            let body = mir
                .split(&format!("fn {name}("))
                .nth(1)
                .unwrap()
                .split("\nfn ")
                .next()
                .unwrap();
            assert!(!body.contains("condbr "), "{body}");
            // This bracket reclaims the native comparison's real result storage.
            assert_eq!(body.matches("stack_save").count(), 1, "{body}");
            assert_eq!(body.matches("stack_restore").count(), 1, "{body}");
            assert_eq!(
                body.lines()
                    .filter(|line| line.trim_start().starts_with("store "))
                    .count(),
                1,
                "{body}"
            );
        }
        let optimized = session.eval_mir("optimized_boolean_values", source);
        session.set_mir_optimization(MirOptimization::Disabled);
        assert_eq!(optimized, session.eval_mir("raw_boolean_values", source));
        assert_eq!(
            optimized,
            "(true, false, true, false, true, true, true, false)"
        );
    }
}
