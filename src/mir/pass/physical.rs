// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Post-expansion scheduling of the shared MIR passes.

use crate::{
    FxHashSet,
    compiler::MirArtifacts,
    mir::Function,
    module::{FunctionId, ModuleEnv, id::Id},
};

use super::{
    OptimizationStage, branch_forward, budget,
    call_graph::CallGraph,
    copy_forward, cost, cse, dce, dead_store, fold, inline,
    known_callee::{KnownCallee, KnownCallees},
    normalize::{self, Pass, Rewrite},
    peephole,
    provenance::{AddressorSummaries, AddressorSummary},
    stack_region, store_forward,
    string_accumulate::StringFunctions,
    tail_merge,
};

/// Optimizes every body of a module, callees first, as the semantic stage does: a callee is
/// finished before its callers read it, so inlining copies an optimized body rather than one each
/// caller has to optimize again. Within a cycle, a callee not finished yet is read as expanded.
pub(crate) fn optimize(
    mut bodies: Vec<Option<Function>>,
    semantic: &MirArtifacts,
    env: ModuleEnv<'_>,
    known: &KnownCallees,
) -> Vec<Option<Function>> {
    let module = env.current.module_id();
    // Expansion adds edges the raw graph lacks, such as calls to generated helpers.
    let components = CallGraph::of_module(&bodies, env.current).components_callees_first();
    let summaries = AddressorSummaries::of_module(&bodies, &components, module, env, &|_| {
        AddressorSummary::UNKNOWN
    });
    let summary = |callee: FunctionId| {
        if callee.module == module {
            summaries.summary(callee.function)
        } else {
            AddressorSummary::UNKNOWN
        }
    };
    let strings = StringFunctions::resolve(env);
    let materializer = fold::StringMaterializer::resolve(env, strings.static_constructor());
    for id in components.into_iter().flatten() {
        let Some(body) = &bodies[id.as_index()] else {
            continue;
        };
        let stage = OptimizationStage::Physical {
            module,
            bodies: &bodies,
            semantic,
        };
        let optimized = optimize_body(body, stage, env, known, &summary, &materializer);
        bodies[id.as_index()] = Some(optimized);
    }
    bodies
}

/// Optimizes one body as the semantic driver does: normalization to a fixpoint alternates with one
/// inlining step, so that the inliner prices a settled body, for at most
/// [`MAX_ROUNDS`](budget::MAX_ROUNDS), and a last normalization settles what the final one exposed.
fn optimize_body(
    body: &Function,
    stage: OptimizationStage<'_>,
    env: ModuleEnv<'_>,
    known: &KnownCallees,
    summary: &dyn Fn(FunctionId) -> AddressorSummary,
    materializer: &fold::StringMaterializer,
) -> Function {
    let growth_base = cost::GrowthBase::of(body);
    let mut current: Option<Function> = None;
    let mut rounds_exhausted = true;
    for _ in 0..budget::MAX_ROUNDS {
        let source = current.as_ref().unwrap_or(body);
        if let Some(normalized) = normalize_physical(
            source,
            growth_base,
            stage,
            env,
            known,
            summary,
            materializer,
        ) {
            current = Some(normalized);
        }
        // Normalization has already folded every call it could, so no call is left for folding to
        // subsume and none needs deferring.
        let source = current.as_ref().unwrap_or(body);
        let Some(inlined) =
            inline::inline_function(source, growth_base, env, stage, &FxHashSet::default())
        else {
            rounds_exhausted = false;
            break;
        };
        current = Some(inlined);
    }
    if rounds_exhausted {
        let source = current.as_ref().unwrap_or(body);
        if let Some(normalized) = normalize_physical(
            source,
            growth_base,
            stage,
            env,
            known,
            summary,
            materializer,
        ) {
            current = Some(normalized);
        }
    }
    current.unwrap_or_else(|| body.clone())
}

/// The shrinking physical rewrites, run to a fixpoint; see [`normalize`](super::normalize).
fn normalize_physical(
    function: &Function,
    growth_base: cost::GrowthBase,
    stage: OptimizationStage<'_>,
    env: ModuleEnv<'_>,
    known: &KnownCallees,
    summary: &dyn Fn(FunctionId) -> AddressorSummary,
    materializer: &fold::StringMaterializer,
) -> Option<Function> {
    let fold = |f: &Function| {
        fold::fold_function(
            f,
            growth_base,
            env,
            stage,
            fold::KnownCallSemantics::new(known, &|callee| Some(stage.original(callee))),
            materializer,
        )
        .map(|folded| Rewrite {
            body: folded.body,
            enables_itself: folded.warrants_another_round,
        })
    };
    let common_calls = |f: &Function| {
        cse::eliminate_common_calls(f, env, summary, &|callee| {
            known
                .resolve(callee, |callee| Some(stage.original(callee)))
                .is_some_and(KnownCallee::is_optimization_barrier)
        })
        .map(Rewrite::settled)
    };
    let common_subexpressions =
        |f: &Function| cse::eliminate_common_subexpressions(f).map(Rewrite::settled);
    // One forwarding can expose another, as in the semantic stage.
    let redundant_storage = |f: &Function| {
        copy_forward::forward_redundant_storage(f, env, stage).map(|body| Rewrite {
            body,
            enables_itself: true,
        })
    };
    let stored_values = |f: &Function| {
        store_forward::forward_stored_values(f, env).map(|body| Rewrite {
            body,
            enables_itself: true,
        })
    };
    let boolean_branches =
        |f: &Function| branch_forward::forward_boolean_branches(f).map(Rewrite::settled);
    let boolean_results =
        |f: &Function| peephole::materialize_boolean_results(f).map(Rewrite::settled);
    let overwritten_stores = |f: &Function| {
        dead_store::remove_overwritten_trivial_copy_stores(f, env).map(Rewrite::settled)
    };
    let dead_storage = |f: &Function| dce::remove_dead_storage(f).map(Rewrite::settled);
    let stack_markers =
        |f: &Function| stack_region::remove_redundant_stack_markers(f).map(Rewrite::settled);
    let dead_trivial_results =
        |f: &Function| dce::remove_dead_trivial_results(f).map(Rewrite::settled);
    let tails = |f: &Function| {
        tail_merge::simplify_tails(f).map(|result| Rewrite {
            body: result.body,
            enables_itself: true,
        })
    };
    normalize::normalize(
        function,
        &[
            Pass {
                name: "fold",
                run: &fold,
                enables: &[],
            },
            Pass {
                name: "common_calls",
                run: &common_calls,
                enables: &[],
            },
            Pass {
                name: "common_subexpressions",
                run: &common_subexpressions,
                // Merging two places can make the calls reading them identical.
                enables: &["common_calls"],
            },
            Pass {
                name: "redundant_storage",
                run: &redundant_storage,
                enables: &[],
            },
            Pass {
                name: "stored_values",
                run: &stored_values,
                enables: &["fold", "common_calls", "common_subexpressions"],
            },
            Pass {
                name: "boolean_branches",
                run: &boolean_branches,
                enables: &[],
            },
            Pass {
                name: "boolean_results",
                run: &boolean_results,
                enables: &["stored_values"],
            },
            Pass {
                name: "overwritten_stores",
                run: &overwritten_stores,
                enables: &["stored_values"],
            },
            Pass {
                name: "dead_storage",
                run: &dead_storage,
                enables: &[
                    "common_subexpressions",
                    "stored_values",
                    "overwritten_stores",
                ],
            },
            Pass {
                name: "stack_markers",
                run: &stack_markers,
                enables: &["common_calls"],
            },
            Pass {
                name: "dead_trivial_results",
                run: &dead_trivial_results,
                enables: &["overwritten_stores", "dead_storage"],
            },
            Pass {
                name: "tails",
                run: &tails,
                enables: &[
                    "overwritten_stores",
                    "dead_storage",
                    "stack_markers",
                    "dead_trivial_results",
                ],
            },
        ],
    )
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, MirOptimization,
        hir::value::{LiteralValue, Value},
        mir::{
            self, BlockId, Operation, OperationKind,
            builder::FunctionBuilder,
            operation::OperationKindDiscriminant,
            pass::known_callee::KnownCallee,
            profile::MirInstructionKind,
            terminator::{Terminator, TerminatorKind},
        },
        module::{FunctionId, LocalFunctionId, ModuleEnv, Path, id::Id},
        std::math::int_type,
        types::r#type::CallResultConvention,
    };
    use ustr::ustr;

    use super::optimize;

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
        let mut allocation_helper_loads = Vec::new();
        for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
            session.set_physical_mir_optimization(optimization);
            let (value, profile) = session
                .run_physical_mir_entry_profiled(module, entry, vec![Value::native(41isize)])
                .unwrap();
            assert_eq!(value.into_primitive_ty::<isize>().unwrap(), 41);
            assert!(profile.peak_cells() > 0);
            counts.push(profile.total().total());
            let program = session.prepare_physical_program(module).unwrap();
            let artifacts = program.module(module).unwrap();
            let loads = (0..artifacts.entry_count())
                .filter_map(|index| artifacts.get(LocalFunctionId::from_index(index)))
                .filter(|body| {
                    body.name
                        .as_str()
                        .starts_with("#physical:variant_payload_allocation:")
                })
                .flat_map(|body| {
                    body.blocks()
                        .flat_map(|block| body.block(block).operations())
                })
                .filter(|operation| operation.kind == OperationKind::Load)
                .count();
            allocation_helper_loads.push(loads);
        }
        assert!(
            allocation_helper_loads[0] > 0,
            "the expansion must exercise literal loads"
        );
        assert_eq!(
            allocation_helper_loads[1], 0,
            "allocation sizes and offsets must read literals directly"
        );
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

    /// Place CSE can make two calls identical after call CSE has run, which must then run again:
    /// here, two copies of an address passed to the same call.
    #[test]
    fn merging_places_merges_the_calls_reading_them() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.set_physical_mir_optimization(MirOptimization::Enabled);
        let module = session
            .compile(
                "#[inline(never)]
                 fn first(x: (int, int)) -> int { x.0 }
                 pub fn compute(p: ((int, int), int)) -> int { first(p.0) + 1 }",
                "physical_place_calls",
                Path::single_str("physical_place_calls"),
            )
            .unwrap()
            .module_id;
        let compute = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr("compute"))
            .unwrap();
        let program = session.prepare_physical_program(module).unwrap();
        let artifacts = program.module(module).unwrap();
        let mut bodies: Vec<_> = (0..artifacts.entry_count())
            .map(|index| artifacts.get(LocalFunctionId::from_index(index)).cloned())
            .collect();
        // `compute` reads `p.0` and calls `first` on it; rebuild it doing both twice.
        let template = bodies[compute.as_index()].take().unwrap();
        let operations = template.block(BlockId::from_index(0)).operations();
        let address = operations
            .iter()
            .find(|operation| matches!(operation.kind, OperationKind::AddressOffset { .. }))
            .unwrap();
        let place = mir::Value::Register(address.result_id().unwrap());
        let call = operations
            .iter()
            .find(|operation| operation.operands.get(1) == Some(&place))
            .unwrap();
        let env = ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules());
        let mut builder = FunctionBuilder::new(template.name, CallResultConvention::Value);
        builder.set_value_result(int_type());
        let parameter = template.parameters()[0].clone();
        let base = mir::Value::Parameter(builder.add_parameter(parameter.ty, parameter.kind));
        let offset = mir::Value::Constant(builder.add_constant(
            int_type(),
            LiteralValue::new_native(0isize),
            &env,
        ));
        let block = builder.add_block();
        let OperationKind::AddressOffset { ty, member } = &address.kind else {
            unreachable!()
        };
        let OperationKind::Call { ty: call_ty, .. } = &call.kind else {
            unreachable!()
        };
        let callee = &call.operands[0];
        // A call ends what CSE knows of physical addresses, so both are computed before the calls.
        let places: Vec<_> = (0..2)
            .map(|_| {
                let address = Operation::address_offset(
                    address.span,
                    base.clone(),
                    offset.clone(),
                    *ty,
                    *member,
                );
                builder.append_operation(block, address).unwrap()
            })
            .collect();
        let results: Vec<_> = places
            .into_iter()
            .map(|place| {
                let call = Operation::call(call.span, callee.clone(), [place], (**call_ty).clone())
                    .with_value_result();
                builder.append_operation(block, call).unwrap()
            })
            .collect();
        let sum = builder
            .append_operation(
                block,
                Operation::call(
                    call.span,
                    mir::Value::Function(session.known_callees().int_add().0),
                    results,
                    session.known_callees().int_add().1.clone(),
                )
                .with_value_result(),
            )
            .unwrap();
        builder.set_terminator(block, Terminator::ret_value(call.span, sum));
        bodies[compute.as_index()] = Some(builder.finish_physical(env));
        let semantic = session
            .mir_artifacts_for(module, MirOptimization::Enabled)
            .unwrap();
        let optimized = optimize(bodies, semantic, env, session.known_callees());
        let body = optimized[compute.as_index()].as_ref().unwrap();
        let calls = body
            .blocks()
            .flat_map(|block| body.block(block).operations())
            .filter(|operation| operation.operands.first() == Some(callee))
            .count();
        assert_eq!(calls, 1, "{}", body.render_with_source_map(&env).text);
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
