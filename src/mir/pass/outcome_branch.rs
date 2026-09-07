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

use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use crate::{
    hir::value::LiteralValue,
    mir::{
        self, BlockId, Function, OperationKind,
        edit::FunctionEdit,
        terminator::{Terminator, TerminatorKind},
    },
    module::ModuleEnv,
};

use super::{
    budget::OUTCOME_BRANCH_BLOCKS,
    dataflow::{self, Const, Outcome},
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
    uses: &FxHashMap<mir::ValueId, usize>,
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
    for block in func.blocks() {
        let body = func.block(block);
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
    if rewrites.is_empty() {
        return None;
    }
    let mut edit = FunctionEdit::new(func.clone());
    for (block, operand, outcome, yes, no) in rewrites {
        let span = edit.block(block).terminator.span;
        let terminator = if yes == no {
            Terminator::goto(span, yes)
        } else {
            let pattern = match outcome.constant() {
                Const::Literal(value) => value,
                Const::VariantTag(tag) => LiteralValue::new_variant_tag(tag),
                _ => unreachable!("outcomes are integers or tags"),
            };
            let comparison = edit.block_mut(block).operations.last_mut().unwrap();
            debug_assert_eq!(comparison.operands[0], operand);
            comparison.operands[1] = mir::Value::Pattern(Box::new(pattern));
            let condition = mir::Value::Register(comparison.result_id().unwrap());
            Terminator::cond_br(span, condition, yes, no)
        };
        edit.block_mut(block).terminator = terminator;
    }
    edit.remove_unreachable_blocks();
    edit.merge_blocks_into_predecessors();
    Some(edit.finish_unverified())
}

#[cfg(test)]
mod tests {
    use super::*;
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
        assert_eq!(pattern.as_variant_tag(), Some(&ustr::ustr("Greater")));
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
        let cleaned = super::super::dce::remove_dead_trivial_results(&simplified).unwrap();
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
        fn main() { (classify(9, 2), classify(2, 9), classify(3, 3), ordinary(1, 9)) }";
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
        let optimized = session.eval_mir("optimized_chains", source);
        session.set_mir_optimization(MirOptimization::Disabled);
        let raw = session.eval_mir("raw_chains", source);
        assert_eq!(optimized, raw);
        assert_eq!(optimized, "(7, 9, 7, false)");
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
}
