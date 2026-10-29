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
    copy_forward, cost, cse, dce, dead_loop, dead_store, fold, inline,
    known_callee::{KnownCallee, KnownCallees},
    normalize::{self, NormalizingPass, Pass, Rewrite},
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
    // Place CSE forgets addresses at writes, calls and stack restores, so a pass removing one can
    // let it merge the addresses around it.
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
    // An unread `TrivialCopy` local goes with the writes into it, such as the element a drop loop
    // takes out of its buffer. That can leave the local moved or copied into it only written.
    let discarded_results = |f: &Function| {
        dce::remove_discarded_trivial_copy_results(f, env).map(|body| Rewrite {
            body,
            enables_itself: true,
        })
    };
    // Only calls known to be total: a script body may not return.
    let dead_calls = |f: &Function| {
        dce::remove_dead_proven_calls(
            f,
            env,
            known,
            &|callee| Some(stage.original(callee)),
            &|_| false,
        )
        .map(Rewrite::settled)
    };
    // Terminating loops come from trusted code, whose loops have no fuel check.
    let dead_loops = |f: &Function| {
        dead_loop::remove_dead_loops(
            f,
            env,
            known,
            &|callee| Some(stage.original(callee)),
            &|_| false,
        )
        .map(Rewrite::settled)
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
                id: NormalizingPass::Fold,
                run: &fold,
                enables: &[],
            },
            Pass {
                id: NormalizingPass::CommonCalls,
                run: &common_calls,
                enables: &[],
            },
            Pass {
                id: NormalizingPass::CommonSubexpressions,
                run: &common_subexpressions,
                // Merging two places can make the calls reading them identical.
                enables: &[NormalizingPass::CommonCalls],
            },
            Pass {
                id: NormalizingPass::RedundantStorage,
                run: &redundant_storage,
                // A call or address computation on a copy becomes one on its source.
                enables: &[
                    NormalizingPass::CommonCalls,
                    NormalizingPass::CommonSubexpressions,
                ],
            },
            Pass {
                id: NormalizingPass::StoredValues,
                run: &stored_values,
                enables: &[
                    NormalizingPass::Fold,
                    NormalizingPass::CommonCalls,
                    NormalizingPass::CommonSubexpressions,
                ],
            },
            Pass {
                id: NormalizingPass::BooleanBranches,
                run: &boolean_branches,
                enables: &[],
            },
            Pass {
                id: NormalizingPass::BooleanResults,
                run: &boolean_results,
                enables: &[NormalizingPass::StoredValues],
            },
            Pass {
                id: NormalizingPass::OverwrittenStores,
                run: &overwritten_stores,
                enables: &[
                    NormalizingPass::CommonSubexpressions,
                    NormalizingPass::StoredValues,
                ],
            },
            Pass {
                id: NormalizingPass::DiscardedResults,
                run: &discarded_results,
                enables: &[NormalizingPass::CommonSubexpressions],
            },
            Pass {
                id: NormalizingPass::DeadCalls,
                run: &dead_calls,
                // Removing a call can remove the last load of a local.
                enables: &[
                    NormalizingPass::CommonSubexpressions,
                    NormalizingPass::DiscardedResults,
                ],
            },
            Pass {
                id: NormalizingPass::DeadLoops,
                run: &dead_loops,
                // Deleting a loop deletes the writes and calls in it, and joins the code around it.
                enables: &[
                    NormalizingPass::CommonCalls,
                    NormalizingPass::CommonSubexpressions,
                    NormalizingPass::StoredValues,
                    NormalizingPass::OverwrittenStores,
                    NormalizingPass::DiscardedResults,
                    NormalizingPass::DeadCalls,
                ],
            },
            Pass {
                id: NormalizingPass::DeadStorage,
                run: &dead_storage,
                enables: &[
                    NormalizingPass::CommonSubexpressions,
                    NormalizingPass::StoredValues,
                    NormalizingPass::OverwrittenStores,
                    NormalizingPass::DeadCalls,
                ],
            },
            Pass {
                id: NormalizingPass::StackMarkers,
                run: &stack_markers,
                enables: &[
                    NormalizingPass::CommonCalls,
                    NormalizingPass::CommonSubexpressions,
                ],
            },
            Pass {
                id: NormalizingPass::DeadTrivialResults,
                run: &dead_trivial_results,
                // Removing an unread load can leave a local only written, or a loop computing
                // what it read dead.
                enables: &[
                    NormalizingPass::OverwrittenStores,
                    NormalizingPass::DiscardedResults,
                    NormalizingPass::DeadCalls,
                    NormalizingPass::DeadLoops,
                    NormalizingPass::DeadStorage,
                ],
            },
            Pass {
                id: NormalizingPass::Tails,
                run: &tails,
                enables: &[
                    NormalizingPass::OverwrittenStores,
                    NormalizingPass::DeadStorage,
                    NormalizingPass::StackMarkers,
                    NormalizingPass::DeadTrivialResults,
                ],
            },
        ],
    )
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, Location, MirOptimization,
        hir::value::{LiteralValue, Value},
        mir::{
            self, BlockId, Operation, OperationKind,
            builder::FunctionBuilder,
            operation::OperationKindDiscriminant,
            pass::known_callee::{KnownCallee, KnownCallees},
            profile::MirInstructionKind,
            terminator::{Terminator, TerminatorKind},
        },
        module::{FunctionId, LocalFunctionId, ModuleEnv, Path, id::Id},
        std::math::int_type,
        types::r#type::{CallResultConvention, Type},
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
        // A call ends what CSE knows of physical addresses, so both are computed before the calls.
        calls_merge_once_their_places_are(|builder, address| [address(builder), address(builder)]);
    }

    /// Storage forwarding can make two calls identical after call CSE has run, which must then run
    /// again: here, a call on a local and on its copy.
    #[test]
    fn forwarding_storage_merges_the_calls_reading_it() {
        calls_merge_once_their_places_are(|builder, address| {
            let block = BlockId::from_index(0);
            let span = Location::new_synthesized();
            let source = address(builder);
            let ty = Type::tuple(vec![int_type(), int_type()]);
            let local = builder
                .append_operation(block, Operation::alloca(span, ty))
                .unwrap();
            builder.append_operation(block, Operation::memcpy(span, source, local.clone()));
            let copy = builder
                .append_operation(block, Operation::alloca(span, ty))
                .unwrap();
            builder.append_operation(block, Operation::memcpy(span, local.clone(), copy.clone()));
            [local, copy]
        });
    }

    /// Checks that a body calling an `#[inline(never)]` function on the two places `places` builds
    /// keeps one call once optimized. `places` builds them in the body's only block, and is given a
    /// function appending one more address of the same argument field.
    fn calls_merge_once_their_places_are(
        places: impl FnOnce(
            &mut FunctionBuilder,
            &dyn Fn(&mut FunctionBuilder) -> mir::Value,
        ) -> [mir::Value; 2],
    ) {
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
        // `compute` reads `p.0` and calls `first` on it; rebuild it calling `first` twice.
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
        let append_address = |builder: &mut FunctionBuilder| {
            let address =
                Operation::address_offset(address.span, base.clone(), offset.clone(), *ty, *member);
            builder.append_operation(block, address).unwrap()
        };
        let results: Vec<_> = places(&mut builder, &append_address)
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

    /// Removing a local whose only use moves another one into it leaves that other one only
    /// written, so the cleanup must run again.
    #[test]
    fn removing_an_unread_local_frees_the_one_moved_into_it() {
        moves_are_removed(|builder, block, local, _, _| {
            let span = Location::new_synthesized();
            let ty = Type::tuple(vec![int_type(), int_type()]);
            let last = builder
                .append_operation(block, Operation::alloca(span, ty))
                .unwrap();
            builder.append_operation(block, Operation::move_value(span, local, last));
        });
    }

    /// Removing an unused call can remove a local's last read, so the cleanup must run again.
    #[test]
    fn removing_an_unused_call_frees_the_local_it_read() {
        moves_are_removed(|builder, block, local, field, known| {
            let span = Location::new_synthesized();
            let address = field(builder, local);
            let value = builder
                .append_operation(block, Operation::load(span, address))
                .unwrap();
            let (add, add_ty) = known.int_add();
            let sum = Operation::call(
                span,
                mir::Value::Function(add),
                [value.clone(), value],
                add_ty.clone(),
            );
            builder.append_operation(block, sum.with_value_result());
        });
    }

    /// Checks that no move is left once optimized in a body which moves one of two call results
    /// into a local, depending on a branch, then hands that local to `uses` after the join, which
    /// must not keep it alive. `uses` is also given a function appending the address of a place's
    /// second field, and the known callees. The calls and the branch keep storage forwarding from
    /// writing the local directly. A third call result's field is read just before and after
    /// `uses`, whose operations must not keep the two addresses from merging once removed.
    fn moves_are_removed(
        uses: impl FnOnce(
            &mut FunctionBuilder,
            BlockId,
            mir::Value,
            &dyn Fn(&mut FunctionBuilder, mir::Value) -> mir::Value,
            &KnownCallees,
        ),
    ) {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.set_physical_mir_optimization(MirOptimization::Enabled);
        let module = session
            .compile(
                "#[inline(never)]
                 fn pair(x: int) -> (int, int) { (x, x + 1) }
                 pub fn compute(c: bool, x: int) -> int { pair(x).1 }",
                "physical_unread_locals",
                Path::single_str("physical_unread_locals"),
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
        // `compute` calls `pair` into a local and reads its second field; rebuild it as above.
        let template = bodies[compute.as_index()].take().unwrap();
        let operations = template.block(BlockId::from_index(0)).operations();
        let call = operations
            .iter()
            .find(|operation| matches!(operation.kind, OperationKind::Call { .. }))
            .unwrap();
        let address = operations
            .iter()
            .find(|operation| matches!(operation.kind, OperationKind::AddressOffset { .. }))
            .unwrap();
        let env = ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules());
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new(template.name, CallResultConvention::Value);
        builder.set_value_result(int_type());
        let [condition, argument] = [0, 1].map(|index| {
            let parameter = template.parameters()[index].clone();
            mir::Value::Parameter(builder.add_parameter(parameter.ty, parameter.kind))
        });
        let [zero, offset] = [0isize, 8].map(|value| {
            mir::Value::Constant(builder.add_constant(
                int_type(),
                LiteralValue::new_native(value),
                &env,
            ))
        });
        let ty = Type::tuple(vec![int_type(), int_type()]);
        let entry = builder.add_block();
        let [read, results @ ..] = [argument.clone(), argument, zero.clone()].map(|argument| {
            let result = builder
                .append_operation(entry, Operation::alloca(span, ty))
                .unwrap();
            let mut call = call.clone();
            call.operands = Box::new([call.operands[0].clone(), argument, result.clone()]);
            builder.append_operation(entry, call);
            result
        });
        let local = builder
            .append_operation(entry, Operation::alloca(span, ty))
            .unwrap();
        let join = builder.add_block();
        let branches = results.map(|result| {
            let branch = builder.add_block();
            builder.append_operation(branch, Operation::move_value(span, result, local.clone()));
            builder.set_terminator(branch, Terminator::goto(span, join));
            branch
        });
        builder.set_terminator(
            entry,
            Terminator::cond_br(span, condition, branches[0], branches[1]),
        );
        let OperationKind::AddressOffset { ty, member } = &address.kind else {
            unreachable!()
        };
        let field = |builder: &mut FunctionBuilder, base: mir::Value| {
            let address = Operation::address_offset(span, base, offset.clone(), *ty, *member);
            builder.append_operation(join, address).unwrap()
        };
        // Reading `read`'s field around `uses` keeps its two addresses live but separated.
        let load_field = |builder: &mut FunctionBuilder| {
            let address = field(builder, read.clone());
            builder
                .append_operation(join, Operation::load(span, address))
                .unwrap()
        };
        let before = load_field(&mut builder);
        uses(&mut builder, join, local, &field, session.known_callees());
        let after = load_field(&mut builder);
        let (add, add_ty) = session.known_callees().int_add();
        let sum = Operation::call(
            span,
            mir::Value::Function(add),
            [before, after],
            add_ty.clone(),
        );
        let sum = builder
            .append_operation(join, sum.with_value_result())
            .unwrap();
        builder.set_terminator(join, Terminator::ret_value(span, sum));
        bodies[compute.as_index()] = Some(builder.finish_physical(env));
        let semantic = session
            .mir_artifacts_for(module, MirOptimization::Enabled)
            .unwrap();
        let optimized = optimize(bodies, semantic, env, session.known_callees());
        let body = optimized[compute.as_index()].as_ref().unwrap();
        let count = |kind: OperationKindDiscriminant| {
            body.blocks()
                .flat_map(|block| body.block(block).operations())
                .filter(|operation| OperationKindDiscriminant::from(&operation.kind) == kind)
                .count()
        };
        let text = body.render_with_source_map(&env).text;
        assert_eq!(count(OperationKindDiscriminant::Move), 0, "{text}");
        assert_eq!(count(OperationKindDiscriminant::AddressOffset), 1, "{text}");
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
