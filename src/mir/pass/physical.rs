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
                    apply!(cse::eliminate_common_calls(&current, env, &summary));
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
    use crate::{CompilerSession, MirOptimization, hir::value::Value, module::Path};
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
}
