// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Post-expansion scheduling of the shared MIR passes.

use crate::{
    compiler::MirArtifacts,
    mir::Function,
    module::{FunctionId, ModuleEnv},
};

use super::{
    OptimizationStage, branch_forward, budget, copy_forward, cse, dce, dead_store, fold, inline,
    known_callee::KnownCallees,
    peephole,
    provenance::{AddressorSummaries, AddressorSummary},
    stack_region,
    string_accumulate::StringFunctions,
    tail_merge,
};

pub(crate) fn optimize(
    bodies: &[Option<Function>],
    semantic: &MirArtifacts,
    env: ModuleEnv<'_>,
    known: &KnownCallees,
) -> Vec<Option<Function>> {
    let module = env.current.module_id();
    let stage = OptimizationStage::Physical {
        module,
        bodies,
        semantic,
    };
    let summaries =
        AddressorSummaries::of_module(bodies, module, env, &|_| AddressorSummary::UNKNOWN);
    let summary = |callee: FunctionId| {
        if callee.module == module {
            summaries.summary(callee.function)
        } else {
            AddressorSummary::UNKNOWN
        }
    };
    let strings = StringFunctions::resolve(env);
    let materializer = fold::StringMaterializer::resolve(env, strings.static_constructor());
    bodies
        .iter()
        .map(|body| {
            body.as_ref().map(|body| {
                let original_size = body.operation_count();
                let mut current = body.clone();
                for _ in 0..budget::MAX_ROUNDS {
                    let mut changed = false;
                    macro_rules! apply {
                        ($result:expr) => {
                            if let Some(next) = $result {
                                current = next;
                                changed = true;
                            }
                        };
                    }
                    if let Some(folded) = fold::fold_function(
                        &current,
                        original_size,
                        env,
                        stage,
                        fold::KnownCallSemantics::new(known, &|callee| {
                            Some(stage.original(callee))
                        }),
                        &materializer,
                    ) {
                        current = folded.body;
                        changed |= folded.warrants_another_round;
                    }
                    apply!(cse::eliminate_common_calls(
                        &current,
                        env,
                        &summary,
                        &|callee| known
                            .resolve(callee, |callee| Some(stage.original(callee)))
                            .is_some_and(super::known_callee::KnownCallee::is_optimization_barrier),
                    ));
                    apply!(cse::eliminate_common_subexpressions(&current));
                    apply!(copy_forward::forward_redundant_storage(
                        &current, env, stage
                    ));
                    apply!(inline::inline_function(&current, original_size, env, stage));
                    apply!(branch_forward::forward_boolean_branches(&current));
                    apply!(peephole::materialize_boolean_results(&current));
                    apply!(dead_store::remove_overwritten_trivial_copy_stores(
                        &current, env
                    ));
                    apply!(dce::remove_dead_storage(&current));
                    apply!(stack_region::remove_redundant_stack_markers(&current));
                    apply!(dce::remove_dead_trivial_results(&current));
                    apply!(tail_merge::simplify_tails(&current).map(|result| result.body));
                    if !changed {
                        break;
                    }
                }
                current
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, MirOptimization,
        hir::value::Value,
        mir::{
            OperationKind, operation::OperationKindDiscriminant, pass::known_callee::KnownCallee,
            profile::MirInstructionKind, terminator::TerminatorKind,
        },
        module::{FunctionId, Path},
    };
    use ustr::ustr;

    #[test]
    fn physical_optimization_preserves_execution_and_reduces_dispatch() {
        let mut session = CompilerSession::new();
        let module = session
            .compile(
                "enum List { Nil, Cons(int, List) }
             pub fn compute(x: int) -> int {
                 let xs = List::Cons(x, List::Cons(x + 1, List::Nil));
                 match xs { Cons(head, tail) => head, Nil => 0 }
             }",
                "physical_optimization",
                Path::single_str("physical_optimization"),
            )
            .unwrap()
            .module_id;
        let entry = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr("compute"))
            .unwrap();
        let mut counts = Vec::new();
        for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
            session.set_physical_mir_optimization(optimization);
            let (value, profile) = session
                .run_physical_mir_entry_profiled(module, entry, vec![Value::native(41isize)])
                .unwrap();
            assert_eq!(value.into_primitive_ty::<isize>().unwrap(), 41);
            assert!(profile.peak_cells() > 0);
            counts.push(profile.total().total());
        }
        assert!(
            counts[1] < counts[0],
            "expanded/optimized dynamic counts: {counts:?}"
        );
        // Switching back must select the same cached expansion, not the optimized artifact.
        session.set_physical_mir_optimization(MirOptimization::Disabled);
        let (value, profile) = session
            .run_physical_mir_entry_profiled(module, entry, vec![Value::native(41isize)])
            .unwrap();
        value.discard_storage();
        assert_eq!(profile.total().total(), counts[0]);
    }

    #[test]
    fn physical_optimization_respects_inline_never() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.set_physical_mir_optimization(MirOptimization::Enabled);
        let module = session
            .compile(
                "#[inline(never)]
                 fn add_one(x: int) -> int { x + 1 }
                 pub fn compute(x: int) -> int { add_one(x) }",
                "physical_inline_never",
                Path::single_str("physical_inline_never"),
            )
            .unwrap()
            .module_id;
        let physical = session.emit_physical_mir_module(module).unwrap();
        assert!(
            physical.contains("call physical_inline_never::add_one"),
            "#[inline(never)] call disappeared from optimized physical MIR:\n{physical}"
        );
    }

    #[test]
    fn physical_optimization_preserves_black_box() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.set_physical_mir_optimization(MirOptimization::Enabled);
        let module = session
            .compile(
                "pub fn compute(x: int) -> int {
                     black_box(x);
                     let left = black_box(x);
                     let right = black_box(x);
                     let mut total = 0;
                     for i in 0..2 { total += black_box(x) };
                     left + right + total
                 }",
                "physical_black_box",
                Path::single_str("physical_black_box"),
            )
            .unwrap()
            .module_id;
        let entry = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr("compute"))
            .unwrap();
        let physical = session.emit_physical_mir_module(module).unwrap();
        let targets = {
            let program = session.prepare_physical_program(module).unwrap();
            let body = program
                .function(FunctionId::new(module, entry))
                .expect("compute has a physical body");
            body.blocks()
                .flat_map(|block| {
                    let block = body.block(block);
                    block
                        .operations()
                        .iter()
                        .chain(match &block.terminator().kind {
                            TerminatorKind::Invoke { operation, .. } => Some(operation),
                            _ => None,
                        })
                })
                .filter_map(|operation| {
                    matches!(operation.kind, OperationKind::Call { .. })
                        .then(|| operation.operands.first())
                        .flatten()
                        .and_then(|callee| match callee {
                            crate::mir::Value::Function(callee) => Some(*callee),
                            _ => None,
                        })
                })
                .collect::<Vec<_>>()
        };
        let black_box_calls = targets
            .into_iter()
            .filter(|&callee| {
                session.known_callees().resolve(callee, |callee| {
                    Some(session.hir_identity_of(callee, MirOptimization::Enabled))
                }) == Some(KnownCallee::BlackBox)
            })
            .count();
        assert_eq!(
            black_box_calls, 4,
            "black_box calls were folded, merged, or removed:\n{physical}"
        );
        let (value, profile) = session
            .run_physical_mir_entry_profiled(module, entry, vec![Value::native(1isize)])
            .unwrap();
        assert_eq!(value.into_primitive_ty::<isize>().unwrap(), 4);
        assert_eq!(
            profile.total().get(MirInstructionKind::Operation(
                OperationKindDiscriminant::BlackBox,
            )),
            5,
            "the loop's black_box call must execute once per iteration"
        );
        assert!(
            physical.contains("black_box"),
            "black_box disappeared from optimized physical MIR:\n{physical}"
        );
    }
}
