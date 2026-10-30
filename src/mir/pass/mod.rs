// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! The MIR optimization passes and the driver that runs them.
//!
//! A function is opened with [`FunctionEdit`](crate::mir::edit::FunctionEdit), rewritten in place,
//! and closed again to restore canonical form. Internal pass transitions deliberately skip global
//! verification; [`MirArtifacts`](crate::compiler::artifacts::MirArtifacts) verifies every final
//! body once after the whole-module cleanup. The driver alternates normalization (folding and the
//! other shrinking rewrites, run to a fixpoint; see `normalize`) with expansion (specialization
//! and inlining) for a bounded number of rounds, because the two feed each other: inlining binds a
//! callee's dictionary parameters to constants, folding then resolves the callee's `dict_entry`s
//! into known function places, and the calls that become direct are new candidates for both.
//! Normalizing first means the inliner measures a settled body against its growth budget.
//!
//! Both passes **merge** jump-joined blocks before closing their own edit, because both leave them:
//! inlining splits every call site's block whether or not the callee needed it, and folding turns a
//! `condbr` on a known condition into a jump. Merging belongs inside each pass rather than as a
//! round of its own — keeping canonical cleanup with the rewrite that creates it avoids another
//! body decomposition and reconstruction.
//!
//! Optimization terminates on independent bounds: the dataflow lattice is monotone within a run,
//! inlining is bounded by its growth budget and the non-recursive restriction,
//! [`MAX_ROUNDS`](budget::MAX_ROUNDS) bounds the expansion rounds, and normalization caps its pass
//! runs.
//!
//! Each stage optimizes callees before their callers, which read a callee's finished body once it
//! is, and its body as first built within their own call-graph cycle. Semantic inlining may cross module boundaries — that is
//! where most inlinable script callees live — which is sound because function, dictionary and
//! subscript identities are global while constant identities are function-local and remapped into
//! the caller's pool. This is not whole-program optimization: nothing outside the module being
//! optimized is modified.
//! Physical scheduling reuses these passes after expansion, with the same alternation of
//! normalization and inlining, without semantic specialization or boxed script evaluation. Its
//! callee view includes module-local physical bodies and helpers.

pub(crate) mod absent_drop;
pub(crate) mod bounds_check;
pub(crate) mod branch_forward;
pub mod budget;
pub(crate) mod call_graph;
pub(crate) mod clone_borrow;
pub(crate) mod copy_forward;
pub(crate) mod cost;
pub(crate) mod cse;
pub(crate) mod dataflow;
pub(crate) mod dce;
pub(crate) mod dead_evidence;
pub(crate) mod dead_loop;
pub(crate) mod dead_store;
pub(crate) mod float_speculation;
pub(crate) mod fold;
pub(crate) mod inline;
pub(crate) mod known_callee;
pub(crate) mod licm;
pub(crate) mod local_cells;
pub(crate) mod loop_checks;
pub(crate) mod loops;
pub(crate) mod monomorphize;
pub(crate) mod negation;
mod normalize;
pub(crate) mod outcome_branch;
pub(crate) mod owned_arguments;
pub(crate) mod peephole;
pub(crate) mod physical;
pub(crate) mod provenance;
pub(crate) mod prune_specializations;
pub(crate) mod relations;
pub mod report;
pub(crate) mod scalar_arguments;
pub(crate) mod scalar_replace;
pub(crate) mod share_specializations;
pub(crate) use crate::mir::site;
mod call_depth;
pub(crate) mod specialization_table;
pub(crate) mod stack_region;
mod stage;
pub(crate) mod store_forward;
pub(crate) mod string_accumulate;
pub(crate) mod tail_merge;
pub(crate) mod value_cells;
pub(crate) mod will_return;

pub(crate) use monomorphize::Specializations;
pub(crate) use stage::{OptimizationStage, SemanticCallees};

use crate::{
    FxHashSet,
    compiler::CompilerSession,
    mir::{self, Function, edit::FunctionEdit, terminator::TerminatorKind},
    module::{FunctionId, LocalFunctionId, ModuleEnv, ModuleId},
};

/// Aggregate facts about rewrites whose results cannot be reconstructed from final MIR.
///
/// Most of the optimization report is derived after the fact. A removed operation is different:
/// once cleanup has collected the call and its error path, the artifact contains no reliable way
/// to distinguish that rewrite from folding or inlining. Keep only those irrecoverable counts here.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct OptimizationStats {
    pub(crate) bounds_checks_removed: usize,
}

impl OptimizationStats {
    pub(crate) fn add(&mut self, other: OptimizationStats) {
        self.bounds_checks_removed += other.bounds_checks_removed;
    }
}

/// Standard-library identities resolved once for every body optimized in one module.
///
/// [`known_callee::KnownCallees`] remains the shared semantic model used by dataflow analyses;
/// pass-specific identity bundles live beside it rather than broadening that model with operations
/// only one exact rewrite understands.
pub(crate) struct OptimizationContext<'a> {
    known_callees: &'a known_callee::KnownCallees,
    string_functions: string_accumulate::StringFunctions,
    string_materializer: fold::StringMaterializer,
}

impl<'a> OptimizationContext<'a> {
    pub(crate) fn new(session: &'a CompilerSession, env: ModuleEnv<'_>) -> Self {
        let string_functions = string_accumulate::StringFunctions::resolve(env);
        Self {
            known_callees: session.known_callees(),
            string_functions,
            string_materializer: fold::StringMaterializer::resolve(
                env,
                string_functions.static_constructor(),
            ),
        }
    }
}

/// Collects the predicate and representation scaffolding a rewrite made dead.
///
/// Tail merging and condition forwarding both leave it: a boolean nothing tests any more, and the
/// cell, store and load that carried it. These passes form one conceptual cleanup even though they
/// alternate to a fixed point: removing a trivial representation result can expose a proven-total
/// call, whose removal can in turn make its result storage dead. Every successful step removes at
/// least one operation, so the loop is bounded by the rewritten body's operation count.
/// Forwards stored values, negations and boolean joins to their canonical form, repeating while
/// the body shrinks: each pass can produce the shape another reads.
fn canonicalize_boolean_flow(
    function: &Function,
    env: ModuleEnv<'_>,
    context: &OptimizationContext,
    callees: SemanticCallees<'_>,
    will_return: &impl Fn(FunctionId) -> bool,
) -> Option<Function> {
    let mut current: Option<Function> = None;
    loop {
        let source = current.as_ref().unwrap_or(function);
        let before = source.operation_count() + source.blocks().count();
        let mut changed = false;
        if let Some(forwarded) = store_forward::forward_stored_values(source, env) {
            current = Some(forwarded);
            changed = true;
        }
        let source = current.as_ref().unwrap_or(function);
        if let Some(forwarded) = negation::forward_boolean_negations(source) {
            current = Some(cleanup_dead_representation_chains(
                forwarded,
                env,
                context,
                callees,
                will_return,
            ));
            changed = true;
        }
        let source = current.as_ref().unwrap_or(function);
        if let Some(forwarded) = branch_forward::forward_boolean_branches(source) {
            current = Some(cleanup_dead_representation_chains(
                forwarded,
                env,
                context,
                callees,
                will_return,
            ));
            changed = true;
        }
        let result = current.as_ref().unwrap_or(function);
        if !changed || result.operation_count() + result.blocks().count() >= before {
            return current;
        }
    }
}

fn cleanup_dead_representation_chains(
    current: Function,
    env: ModuleEnv<'_>,
    context: &OptimizationContext,
    callees: SemanticCallees<'_>,
    will_return: &impl Fn(FunctionId) -> bool,
) -> Function {
    clean_dead_representation_chains(&current, env, context, callees, will_return)
        .unwrap_or(current)
}

/// Removes dead representation chains to a fixpoint; `None` if there was none.
fn clean_dead_representation_chains(
    function: &Function,
    env: ModuleEnv<'_>,
    context: &OptimizationContext,
    callees: SemanticCallees<'_>,
    will_return: &impl Fn(FunctionId) -> bool,
) -> Option<Function> {
    let mut current: Option<Function> = None;
    loop {
        let mut cleaned_any = false;
        if let Some(cleaned) =
            dce::remove_dead_trivial_results(current.as_ref().unwrap_or(function))
        {
            current = Some(cleaned);
            cleaned_any = true;
        }
        if let Some(cleaned) = dce::remove_dead_proven_calls(
            current.as_ref().unwrap_or(function),
            env,
            context.known_callees,
            &callees.original_of(),
            will_return,
        ) {
            current = Some(cleaned);
            cleaned_any = true;
        }
        if let Some(cleaned) =
            dce::remove_dead_nonconsuming_storage(current.as_ref().unwrap_or(function))
        {
            current = Some(cleaned);
            cleaned_any = true;
        }
        if !cleaned_any {
            return current;
        }
    }
}

/// The specializations `function` dispatches to that wait to be optimized before a caller reads
/// them, in the order of their first dispatch.
fn ready_callees(function: &Function, specializations: &Specializations) -> Vec<LocalFunctionId> {
    let mut ready = Vec::new();
    for block in function.blocks() {
        let block = function.block(block);
        for operation in block
            .operations()
            .iter()
            .chain(match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            })
        {
            if let Some(index) = operation.dispatch_callee_index()
                && let mir::Value::Function(callee) = &operation.operands[index]
                && specializations.is_ready(*callee)
                && !ready.contains(&callee.function)
            {
                ready.push(callee.function);
            }
        }
    }
    ready
}

/// Optimizes the ready specialization `id` before the worklist reaches it, keeping the result only
/// when it read nothing that is not final yet; see `monomorphize::Progress`.
pub(crate) fn optimize_specialization_ahead(
    id: LocalFunctionId,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
    specializations: &mut Specializations,
    context: &OptimizationContext,
) {
    // A specialization optimized for an earlier callee in the list may have made this one ready
    // no longer.
    if !specializations.is_ready(FunctionId::new(module_id, id)) {
        return;
    }
    let (body, frame) = specializations.begin_ahead(id);
    // Counted apart from the caller's rewrites: a kept result stays kept even when the caller's
    // own optimization ahead is discarded, and a discarded one is counted by the worklist.
    let mut stats = OptimizationStats::default();
    let optimized = optimize_function(
        &body,
        env,
        session,
        module_id,
        specializations,
        context,
        &mut stats,
    );
    specializations.end_ahead(id, optimized, frame, stats);
}

/// The shrinking rewrites run between expansions, to a fixpoint; see [`normalize`].
///
/// Order matters: each pass's comment says what it consumes from the ones before it. The back
/// edges are the measured cases where a pass enables an earlier one or itself.
fn normalize_semantic(
    function: &Function,
    growth_base: cost::GrowthBase,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    specializations: &Specializations,
    context: &OptimizationContext,
) -> Option<Function> {
    let callees = SemanticCallees::new(session, Some(specializations));
    let summary_of = |callee| callees.addressor_summary(callee);
    let is_optimization_barrier = |callee| {
        context
            .known_callees
            .resolve(callee, callees.original_of())
            .is_some_and(known_callee::KnownCallee::is_optimization_barrier)
    };
    // Scalar arguments are values read at their calls. Merging the loads of a place nothing wrote
    // in between, those of the body arriving and those the last inlining exposed, makes a place
    // read twice one value, which folding's identities and call CSE compare.
    let common_loads =
        |f: &Function| cse::eliminate_common_loads(f, env, &summary_of).map(Rewrite::settled);
    // Inlining binds dictionary parameters to constants, which can leave a dictionary closed over
    // static evidence only; as static evidence, folding devirtualizes its entries.
    let static_dictionaries =
        |f: &Function| peephole::close_static_dictionaries(f, env).map(Rewrite::settled);
    // Fold early: it is what makes arguments known. Most folds shrink before the inliner measures
    // the body; constructive folds reserve their setup against the whole-function growth budget. A
    // chain of folds that crosses block boundaries needs the analysis to run again to propagate,
    // which only a rewrite producing something known warrants (see `Folded`).
    let fold = |f: &Function| {
        fold::fold_function(
            f,
            growth_base,
            env,
            OptimizationStage::Semantic(callees),
            fold::KnownCallSemantics::new(context.known_callees, &callees.original_of()),
            &context.string_materializer,
        )
        .map(|folded| Rewrite {
            body: folded.body,
            enables_itself: folded.warrants_another_round,
        })
    };
    // Calls are merged before inlining so one body is copied per distinct computation, rather
    // than copying duplicates and trying to rediscover the whole computation afterwards.
    // Addressors additionally use provenance. A specialization inherits its original's
    // conservative addressor summary: substitution cannot change provenance, and a repeatability
    // proof remains true when types are substituted or operations removed. An unresolved original
    // remains conservatively non-repeatable even when its concrete copy could prove more.
    let common_calls = |f: &Function| {
        cse::eliminate_common_calls(f, env, &summary_of, &is_optimization_barrier)
            .map(Rewrite::settled)
    };
    // Lowering and value-call CSE both leave results in fresh slots before transferring them to
    // their real destinations. Storage forwarding is a separate proof from expression equivalence,
    // run before inlining so the body being priced has already lost provably redundant result
    // slots, transfers and allocations.
    // One forwarding can expose another (std's parser `bump` helpers).
    let redundant_storage = |f: &Function| {
        copy_forward::forward_redundant_storage(f, env, OptimizationStage::Semantic(callees)).map(
            |body| Rewrite {
                body,
                enables_itself: true,
            },
        )
    };
    // Its register counterpart: a value parked in a single-store cell, such as an inlined callee's
    // `@ret`, is read where it is computed. That can name a callee or an argument folding and call
    // CSE consume (a function stored in a local, then called), and expose another such cell.
    let stored_values = |f: &Function| {
        store_forward::forward_stored_values(f, env).map(|body| Rewrite {
            body,
            enables_itself: true,
        })
    };
    // The place-producing operations are merged before inlining too, because their redundancy is
    // already present: a generic body reads the same `dict_entry` once per use of the trait
    // method. Merging them shrinks the body before the inliner prices it, and two calls whose only
    // difference was which copy of an entry they named become one expression for call CSE.
    let common_subexpressions =
        |f: &Function| cse::eliminate_common_subexpressions(f).map(Rewrite::settled);
    // Ownership canonicalization. A read-only clone borrows a source that outlives it; the place
    // it substitutes is then named twice, which place CSE merges, and calls reading it may become
    // identical, which call CSE merges.
    let clone_borrowing =
        |f: &Function| clone_borrow::borrow_read_only_clones(f, &summary_of).map(Rewrite::settled);
    // A private local's last ownership moves into its clone destination. Borrowing comes first
    // because it can eliminate the destination storage too.
    let terminal_moves = |f: &Function| {
        owned_arguments::forward_terminal_clones(f, env, &summary_of).map(Rewrite::settled)
    };
    // A local product owning managed fields, such as an inlined iterator holding the array it
    // reads, becomes one local per field. Each field's storage and lifetime is then on its own: a
    // callback field is a known callee, a copied collection a clone to borrow.
    // Lowering drops a scope's locals on every failure path, including where nothing initialized
    // them yet, and inlining carries those drops into callers. Earlier passes expose more: a merged
    // call or a borrowed clone leaves its result's drops behind, and folding or place merging lets
    // the analysis prove more storage absent. The managed split expands a drop into its
    // destructor, which would read the tag of a variant never built: remove them first.
    let absent_drops =
        |f: &Function| absent_drop::remove_absent_drops(f, env).map(Rewrite::settled);
    let managed_split = |f: &Function| {
        scalar_replace::split_managed_local_products(f, env, OptimizationStage::Semantic(callees))
            .map(Rewrite::settled)
    };
    use normalize::{NormalizingPass, Rewrite};
    normalize::normalize(
        function,
        &[
            normalize::Pass {
                id: NormalizingPass::CommonLoads,
                run: &common_loads,
                enables: &[],
            },
            normalize::Pass {
                id: NormalizingPass::StaticDictionaries,
                run: &static_dictionaries,
                enables: &[],
            },
            normalize::Pass {
                id: NormalizingPass::Fold,
                run: &fold,
                enables: &[],
            },
            normalize::Pass {
                id: NormalizingPass::CommonCalls,
                run: &common_calls,
                enables: &[],
            },
            normalize::Pass {
                id: NormalizingPass::RedundantStorage,
                run: &redundant_storage,
                // A load or call reading a copy becomes one reading its source.
                enables: &[NormalizingPass::CommonLoads, NormalizingPass::CommonCalls],
            },
            normalize::Pass {
                id: NormalizingPass::StoredValues,
                run: &stored_values,
                enables: &[
                    NormalizingPass::CommonLoads,
                    NormalizingPass::Fold,
                    NormalizingPass::CommonCalls,
                ],
            },
            normalize::Pass {
                id: NormalizingPass::CommonSubexpressions,
                run: &common_subexpressions,
                enables: &[NormalizingPass::CommonLoads, NormalizingPass::CommonCalls],
            },
            normalize::Pass {
                id: NormalizingPass::CloneBorrowing,
                run: &clone_borrowing,
                enables: &[
                    NormalizingPass::CommonLoads,
                    NormalizingPass::CommonCalls,
                    NormalizingPass::CommonSubexpressions,
                ],
            },
            normalize::Pass {
                id: NormalizingPass::TerminalMoves,
                run: &terminal_moves,
                enables: &[
                    NormalizingPass::CommonLoads,
                    NormalizingPass::RedundantStorage,
                ],
            },
            normalize::Pass {
                id: NormalizingPass::AbsentDrops,
                run: &absent_drops,
                // A drop was a use and a write of its place.
                enables: &[
                    NormalizingPass::CommonLoads,
                    NormalizingPass::CommonCalls,
                    NormalizingPass::RedundantStorage,
                    NormalizingPass::StoredValues,
                    NormalizingPass::CloneBorrowing,
                    NormalizingPass::TerminalMoves,
                ],
            },
            normalize::Pass {
                id: NormalizingPass::ManagedSplit,
                run: &managed_split,
                enables: &[
                    NormalizingPass::CommonLoads,
                    NormalizingPass::CommonCalls,
                    NormalizingPass::StaticDictionaries,
                    NormalizingPass::Fold,
                    NormalizingPass::RedundantStorage,
                    NormalizingPass::StoredValues,
                    NormalizingPass::CommonSubexpressions,
                    NormalizingPass::CloneBorrowing,
                    NormalizingPass::TerminalMoves,
                ],
            },
        ],
    )
}

/// Optimizes one function, returning the body to install.
///
/// The driver alternates normalization, run to a fixpoint, with one expansion step: specializing
/// generic calls, then inlining. Expansion grows code under budgets; normalization shrinks it, so
/// the inliner always prices a settled body. Each pass rewrites an immutable function into a new
/// one, so it never reads an analysis that its own edits have invalidated. The loop ends when an
/// expansion step changes nothing, or after [`MAX_ROUNDS`](budget::MAX_ROUNDS) of them, followed by
/// a last normalization of what the final one exposed.
pub(crate) fn optimize_function(
    function: &Function,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
    specializations: &mut Specializations,
    context: &OptimizationContext,
    stats: &mut OptimizationStats,
) -> Function {
    let growth_base = cost::GrowthBase::of(function);
    let mut current: Option<Function> = None;
    let mut rounds_exhausted = true;
    let mut inlined_any = false;
    for _round in 0..budget::MAX_ROUNDS {
        let source = current.as_ref().unwrap_or(function);
        if let Some(normalized) =
            normalize_semantic(source, growth_base, env, session, specializations, context)
        {
            current = Some(normalized);
        }
        let mut expanded = false;
        // Specialization before inlining: it rewrites a generic call into a call on a concrete
        // copy, whose dictionaries are constants the next normalization's folding resolves. That
        // is what reaches this language's generic code at all — see `monomorphize`.
        let source = current.as_ref().unwrap_or(function);
        if let Some(specialized) =
            monomorphize::specialize_call_sites(source, env, session, module_id, specializations)
        {
            current = Some(specialized);
            expanded = true;
        }
        // A specialization is a callee found while optimizing. Like a declared callee, it is
        // optimized before the inliner reads it, whenever its inputs are final.
        if specializations.has_ready() {
            let source = current.as_ref().unwrap_or(function);
            for id in ready_callees(source, specializations) {
                optimize_specialization_ahead(
                    id,
                    env,
                    session,
                    module_id,
                    specializations,
                    context,
                );
            }
        }
        // Optimizing a specialization ahead of the worklist is discarded once it reads a body that
        // is not final, so stop paying for it; see `monomorphize::Progress`.
        if specializations.abandons_ahead() {
            return function.clone();
        }
        // Normalization has already folded every call it could, so no call is left for folding to
        // subsume and none needs deferring.
        let callees = SemanticCallees::new(session, Some(specializations));
        let source = current.as_ref().unwrap_or(function);
        if let Some(inlined) = inline::inline_function(
            source,
            growth_base,
            env,
            OptimizationStage::Semantic(callees),
            &FxHashSet::default(),
        ) {
            current = Some(inlined);
            expanded = true;
            inlined_any = true;
        }
        if specializations.abandons_ahead() {
            return function.clone();
        }
        if !expanded {
            rounds_exhausted = false;
            break;
        }
    }
    if rounds_exhausted {
        let source = current.as_ref().unwrap_or(function);
        if let Some(normalized) =
            normalize_semantic(source, growth_base, env, session, specializations, context)
        {
            current = Some(normalized);
        }
    }
    // The specialization table is final from here.
    let callees = SemanticCallees::new(session, Some(specializations));
    // Whether a callee is proved to return, which the cleanups below and loop-invariant motion
    // all ask.
    let will_return = |callee| callees.will_return(callee);

    // Inlined predicates often materialize `true`/`false` in two arms only for the caller to
    // compare that slot with `true` and branch again. Forward the known edge information while
    // retaining any stack restoration at the join. DCE below then removes the dead slot/stores.
    // A one-case test of a local variant's tag is first turned into that shape.
    let source = current.as_ref().unwrap_or(function);
    if let Some(shadowed) = branch_forward::shadow_variant_tag_tests(source, env) {
        current = Some(shadowed);
    }
    let source = current.as_ref().unwrap_or(function);
    if let Some(forwarded) = branch_forward::forward_boolean_branches(source) {
        current = Some(forwarded);
    }
    // Some local variant results converge only to have their tag read and dispatched. Redirect
    // each statically tagged construction path to the selected consumer while retaining payload
    // storage for that consumer's projections.
    let source = current.as_ref().unwrap_or(function);
    if let Some(forwarded) = branch_forward::forward_variant_branches(source) {
        current = Some(forwarded);
        // Redirecting the constructor paths puts payload initialization and consumption on one
        // straight-line path. Reuse place CSE for their address calculations and let ordinary
        // storage forwarding reconsider any other temporary the changed CFG exposes.
        let source = current.as_ref().unwrap();
        if let Some(merged) = cse::eliminate_common_subexpressions(source) {
            current = Some(merged);
        }
        let source = current.as_ref().unwrap();
        if let Some(forwarded) = copy_forward::forward_redundant_storage(
            source,
            env,
            OptimizationStage::Semantic(callees),
        ) {
            current = Some(forwarded);
        }
    }
    // A predicate returned as a value often lowers to a tiny diamond whose arms only store opposite
    // boolean constants to the same destination. Collapse that materialization before DCE cleans up
    // any now-unused boolean storage and stranded blocks.
    let source = current.as_ref().unwrap_or(function);
    if let Some(materialized) = peephole::materialize_boolean_results(source) {
        current = Some(materialized);
    }
    // Both of the rewrites above leave a boolean where its consumer already had one: a `not` call
    // folded into a comparison, and a materialized predicate stored to be tested again. Bring
    // boolean flow to its canonical form before the analyses below read branch conditions.
    let source = current.as_ref().unwrap_or(function);
    if let Some(forwarded) = canonicalize_boolean_flow(source, env, context, callees, &will_return)
    {
        current = Some(forwarded);
    }
    // A literal used only by concrete string equality can use match's direct comparison.
    let source = current.as_ref().unwrap_or(function);
    if let Some(fused) =
        string_accumulate::fuse_static_string_equalities(source, context.string_functions)
    {
        current = Some(fused);
    }
    // A constructively reified string is `StaticStr` plus `string_from_static`. If its only purpose
    // is an append, use the static appender directly and leave no owned temporary to construct or
    // drop. This runs before accumulator forwarding so that pass sees the final mix of appenders.
    let source = current.as_ref().unwrap_or(function);
    if let Some(fused) =
        string_accumulate::fuse_static_string_appends(source, context.string_functions)
    {
        current = Some(fused);
    }
    // Formatting a self-prefixed assignment through an empty builder copies the complete growing
    // prefix. Forward the old string's ownership into that builder while the exact std-semantic
    // proof is visible; DCE below removes the now-unused rendering and assignment scaffolding.
    let source = current.as_ref().unwrap_or(function);
    if let Some(forwarded) =
        string_accumulate::forward_string_accumulation(source, context.string_functions)
    {
        current = Some(forwarded);
    }
    // Inlining and devirtualization name callees through call sites typed for any callee; a
    // direct call must follow its callee's failure convention.
    let source = current.as_ref().unwrap_or(function);
    if let Some(narrowed) =
        fold::narrow_infallible_direct_invokes(source, env, |callee| callees.original(callee))
    {
        current = Some(narrowed);
    }
    // After devirtualization, which is what makes a subscript's checks direct calls the analysis can
    // resolve at all, and before DCE, which removes the cleanup blocks a removed check strands.
    let source = current.as_ref().unwrap_or(function);
    if let Some((rewritten, removed)) = bounds_check::eliminate_bounds_checks(
        source,
        env,
        context.known_callees,
        &callees.original_of(),
    ) {
        stats.bounds_checks_removed += removed;
        current = Some(rewritten);
    }
    // Inlining substitutes the caller's throwaway result allocation for the callee's `@ret`. For
    // an unread `TrivialCopy` result, remove that complete write-only place tree while retaining
    // the inlined body's effects. Representation cleanup then collects the variant shells, loads
    // and other pure producers which only fed the discarded result.
    if inlined_any {
        let source = current.as_ref().unwrap_or(function);
        if let Some(cleaned) = dce::remove_discarded_trivial_copy_results(source, env) {
            current = Some(cleanup_dead_representation_chains(
                cleaned,
                env,
                context,
                callees,
                &will_return,
            ));
        }
    }
    // Purity does not imply termination, so general dead-call elimination would be unsound. Remove
    // an unused direct call only under either the known native total/speculatable contract or a
    // module-table script body's raw-MIR return proof plus passive-input and copy-result
    // restrictions. A call's result register is often read only by a store into a local nothing
    // reads, so the cleanup removes such stores and the calls they leave unused to a fixpoint;
    // ordinary DCE then collects the unread cells.
    let source = current.as_ref().unwrap_or(function);
    if let Some(cleaned) =
        clean_dead_representation_chains(source, env, context, callees, &will_return)
    {
        current = Some(cleaned);
    }
    // A local `TrivialCopy` cell often receives an initializer only for every branch to replace it
    // before its first read. Backward exact-place liveness removes that initializer; ordinary DCE
    // below then sees any allocation or literal which became wholly unread.
    let source = current.as_ref().unwrap_or(function);
    if let Some(cleaned) = dead_store::remove_overwritten_trivial_copy_stores(source, env) {
        current = Some(cleaned);
    }
    // Hoist initialized copyable reads and terminating pure direct calls into a natural loop's
    // unique preheader. Calls require invariant passive inputs and `TrivialCopy` result storage.
    // Empty effects exclude source-visible failure and mutation; the raw-MIR summary separately
    // proves that speculation preserves termination.
    // Reads use the shared root-access and storage-lifetime proofs. No operation is added.
    // Run after the passes that remove writes and copies: a loop reading a borrowed clone reads
    // its unchanged source, while the clone's destination shared its product with written fields.
    let source = current.as_ref().unwrap_or(function);
    if let Some(hoisted) = licm::hoist_loop_invariants(
        source,
        env,
        &will_return,
        &|callee| {
            context
                .known_callees
                .resolve(callee, callees.original_of())
                .is_some_and(known_callee::KnownCallee::is_optimization_barrier)
        },
        &|callee| callees.addressor_summary(callee),
    ) {
        current = Some(hoisted);
    }
    // Cleanup runs once, after the rounds have settled, and on every body rather than only on one a
    // pass changed. A specialization arrives already carrying dead code — substitution turns its
    // semantic clones and drops into representation copies and nothing, leaving the dictionary
    // entries they read unread — so "nothing changed it, so nothing is dead" no longer holds.
    let source = current.as_ref().unwrap_or(function);
    if let Some(cleaned) = dce::remove_dead_storage(source) {
        current = Some(cleaned);
    }
    // After DCE has emptied every bracket it can, and *before* tail merging. What remains reclaims
    // real storage and must stay: a bracket is where a live range ends, which a backend's stack-slot
    // allocator needs. Only a marker duplicating one already held, and a restore to the frontier
    // already current, are removed here — neither carries information the surviving marker does not.
    //
    // Ordering with tail merging runs this way because canonicalization *creates* alpha-equivalence
    // rather than consuming it: two arms which restore duplicate markers of the same frontier are
    // the same block only once both name the surviving marker. Merging first would compare them
    // while they still differ by a register name and conclude, wrongly, that they are distinct.
    let source = current.as_ref().unwrap_or(function);
    if let Some(canonicalized) = stack_region::remove_redundant_stack_markers(source) {
        current = Some(canonicalized);
    }
    // Collect unread representation results once here, including stack saves stranded by
    // canonicalization and dead comparisons, loads, tags, payload indirections and initialization
    // tests. Successful branch rewrites below already run this same trivial-result cleanup.
    let source = current.as_ref().unwrap_or(function);
    if let Some(cleaned) = dce::remove_dead_trivial_results(source) {
        current = Some(cleaned);
    }
    // Cleanup can make mutually exclusive branch arms alpha-equivalent by removing lowering
    // scaffolding that differed between them. Merge complete equivalent blocks without moving
    // their operations, collapse a conditional whose two edges now agree, and fold shared empty
    // exits into their predecessors. Only the first two can make computations dead; revisit
    // proven-total calls and storage for those, while an exit-only rewrite pays no second cleanup.
    let mut repeated = false;
    loop {
        // The placements above canonicalized the first sweep's input. A repeated sweep follows
        // rewrites that can concatenate arms' restores, which would hide their equivalence from
        // tail merging, and store computed predicates in front of negations and branches.
        if repeated {
            let source = current.as_ref().unwrap_or(function);
            if let Some(canonicalized) = stack_region::remove_redundant_stack_markers(source) {
                current = Some(canonicalized);
            }
        }
        let source = current.as_ref().unwrap_or(function);
        let before = source.operation_count() + source.blocks().count();
        let mut changed = false;
        // Dead-storage cleanup and the rewrites below expose boolean flow the placement before the
        // analyses could not see.
        if let Some(forwarded) =
            canonicalize_boolean_flow(source, env, context, callees, &will_return)
        {
            current = Some(forwarded);
            changed = true;
        }
        let source = current.as_ref().unwrap_or(function);
        if let Some(simplified) = tail_merge::simplify_tails(source) {
            current = Some(if simplified.exposed_dead_code {
                cleanup_dead_representation_chains(
                    simplified.body,
                    env,
                    context,
                    callees,
                    &will_return,
                )
            } else {
                simplified.body
            });
            changed = true;
        }
        // Tail merging exposes equality chains with shared destinations. Analyze after it, so
        // we do not pay for a fixpoint on the same chain before its destinations are shared.
        let source = current.as_ref().unwrap_or(function);
        if let Some(simplified) = outcome_branch::simplify_outcome_branches(source, env) {
            current = Some(cleanup_dead_representation_chains(
                simplified,
                env,
                context,
                callees,
                &will_return,
            ));
            changed = true;
        }
        // Merging forwarding blocks can expose equivalent complete tails; collecting a dead
        // predicate can expose another merge. Repeat only while this shrink-only cleanup makes
        // structural progress, so empty cycles cannot keep the sweep alive.
        let result = current.as_ref().unwrap_or(function);
        if !changed || result.operation_count() + result.blocks().count() >= before {
            break;
        }
        repeated = true;
    }
    // Forwarding a cell that holds a bare function, in the cleanups above, names callees too,
    // after the narrowing placed with devirtualization. A direct call must follow
    // its callee's failure convention in the final body.
    let source = current.as_ref().unwrap_or(function);
    if let Some(narrowed) =
        fold::narrow_infallible_direct_invokes(source, env, |callee| callees.original(callee))
    {
        current = Some(narrowed);
    }
    let source = current.as_ref().unwrap_or(function);
    if let Some(simplified) = call_depth::simplify_checks(source, env, callees) {
        current = Some(simplified);
    }
    // Final artifact verification covers unchanged functions too, so cloning is the identity here.
    // Most passes leave the constants they stop naming in the pool; prune them once, at the end.
    match current {
        Some(rewritten) => {
            let mut edit = FunctionEdit::new(rewritten);
            edit.prune_constants();
            edit.finish_unverified()
        }
        None => function.clone(),
    }
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization, Path};

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("merge", src)
    }

    fn body_of<'a>(module: &'a str, name: &str) -> &'a str {
        module
            .split(&format!("fn {name}"))
            .nth(1)
            .unwrap_or_else(|| panic!("module has no `{name}`:\n{module}"))
    }

    /// Stack-marker canonicalization runs before tail merging because it *creates* the equivalence
    /// tail merging looks for. Both arms which skip the body restore a marker of the same frontier,
    /// but they restore *duplicate* markers, and are the same block only once both name the
    /// surviving one. Merging first compares them while they still differ by a register name.
    #[test]
    fn arms_restoring_duplicate_stack_markers_are_merged() {
        let module = optimized(
            "fn f(a: int, b: int) -> int { if (match cmp(a, 0) { Less => false, _ => true }) and (match cmp(a, b) { Less => true, _ => false }) { 1 } else { 2 } }",
        );
        let body = body_of(&module, "f")
            .split("\nfn ")
            .next()
            .expect("a function has a body");
        assert!(
            !body.contains("\n    br "),
            "the two arms which skip the body must become one block, leaving nothing that merely \
             jumps:\n{body}"
        );
        assert_eq!(
            body.matches("\n  b").count(),
            4,
            "entry, the second comparison, and one block per outcome:\n{body}"
        );
    }

    #[test]
    fn ordered_operators_merge_short_circuit_stack_markers() {
        let module =
            optimized("fn f(a: int, b: int) -> int { if a >= 0 and a < b { 1 } else { 2 } }");
        let body = body_of(&module, "f").split("\nfn ").next().unwrap();
        assert!(!body.contains("\n    br "), "{body}");
        assert_eq!(body.matches("\n  b").count(), 4, "{body}");
    }

    /// Splicing a straight-line callee splits the call site's block and joins the pieces with
    /// jumps; merging must collapse them again, or every inlined call would cost two blocks that
    /// each later round re-walks.
    ///
    /// The argument is deliberately unknown, so nothing folds away and what remains to observe is
    /// the block structure itself.
    #[test]
    fn inlining_a_straight_line_callee_leaves_one_block() {
        let module = optimized(
            "fn add_one(x: int) -> int { x + 1 }\n\
             fn use_it(n: int) -> int { add_one(n) }",
        );
        let caller = body_of(&module, "use_it");
        assert!(
            !caller.contains("call merge::add_one"),
            "the callee must be inlined:\n{caller}"
        );
        assert!(
            !caller.contains("br b"),
            "the spliced pieces must be merged back into one block:\n{caller}"
        );
    }

    /// LICM runs after clone borrowing. Before it, the iterator reads the length from its clone of
    /// the array, in the product whose cursor the loop writes, so the read stays in the loop.
    #[test]
    fn an_array_loop_reads_the_borrowed_length_before_the_loop() {
        let module =
            optimized("fn sum(x: [int]) -> int { let mut s = 0; for a in x { s += a }; s }");
        let body = body_of(&module, "sum").split("\nfn ").next().unwrap();
        let entry = body.split("\n  b1:").next().unwrap();
        assert!(
            entry.contains("from %p0\n") && entry.contains(": int = load "),
            "the length of the borrowed array must be read in the entry block:\n{body}"
        );
    }

    /// The caller instantiates `zip` for arrays after `dot`, so the thunks follow `dot` in the
    /// module's function table.
    const ZIP_SUM: &str = "fn dot(x: [int], y: [int]) -> int { let mut s = 0; for (a, b) in zip(x, y) { s += a * b }; s }\nfn main() -> int { dot([1], [2]) }";

    /// `zip` reaches `iter` through a dictionary of a blanket impl, whose methods are thunks in the
    /// caller's module. The call graph orders them before the caller, which inlines their bodies.
    #[test]
    fn a_zip_loop_inlines_the_iterators_of_its_arrays() {
        let module = optimized(ZIP_SUM);
        let body = body_of(&module, "dot").split("\nfn ").next().unwrap();
        assert!(
            !body.contains("-thunk("),
            "the array iterators must be inlined:\n{body}"
        );
    }

    /// An inlined adaptor is a local product holding its callback beside the iterator it wraps.
    /// Splitting it during normalization exposes the callback as a known callee, so the round that
    /// follows inlines it, even over records owning managed fields.
    #[test]
    fn a_lazy_adaptor_over_records_inlines_its_callback() {
        let module = optimized(
            "fn map_for(people: [{ name: string, scores: [int] }]) -> int { \
             let mut n = 0; for l in iter(people) |> map(|p| len(p.scores)) { n += l }; n }",
        );
        let body = body_of(&module, "map_for").split("\nfn ").next().unwrap();
        assert!(
            !body.contains("$lambda"),
            "the map callback must be inlined:\n{body}"
        );
    }

    /// Borrowing `y`'s clone from `x` makes `len(x)` and `len(y)` the same call without creating a
    /// repeated load or place, so clone borrowing must reschedule call CSE itself.
    #[test]
    fn a_borrowed_clone_merges_the_calls_it_makes_identical() {
        let module = optimized(
            "fn f(a: [int]) -> int { let mut x = a; array_append(x, 1); let y = x; \
             len(x) + len(y) }",
        );
        let body = body_of(&module, "f").split("\nfn ").next().unwrap();
        assert_eq!(
            body.matches("clone ").count(),
            1,
            "only `x` may clone, y must borrow it:\n{body}"
        );
        let doubled = body.lines().any(|line| {
            line.split_once("::add#impl:")
                .and_then(|(_, call)| call.split_once('(')?.1.split_once(')'))
                .and_then(|(arguments, _)| arguments.split_once(", "))
                .is_some_and(|(left, right)| left == right)
        });
        assert!(
            doubled,
            "the two lengths must merge into one value:\n{body}"
        );
    }

    /// The zip iterator is built in a temporary and cloned into the loop's iterator. The temporary
    /// is dropped right after, in the entry block, so it moves instead.
    #[test]
    fn a_temporary_dropped_after_its_clone_moves() {
        let module = optimized(ZIP_SUM);
        let body = body_of(&module, "dot").split("\nfn ").next().unwrap();
        assert!(
            !body.contains("clone ZipIterator"),
            "the zip iterator must move into the loop:\n{body}"
        );
    }

    /// The zip iterator and its array iterators split into one local per field: each array clone
    /// then borrows its parameter, and each cursor is a local of its own.
    #[test]
    fn a_zip_loop_borrows_its_arrays_and_keeps_its_cursors_in_locals() {
        let module = optimized(ZIP_SUM);
        let body = body_of(&module, "dot").split("\nfn ").next().unwrap();
        assert!(
            !body.contains("clone ") && !body.contains("drop ") && !body.contains("Iterator"),
            "the iterators must be split and their arrays borrowed:\n{body}"
        );
    }

    /// Indexing reads the array's `start` inside an addition that also takes the loop's cursor.
    /// Passed as a value, that read is the caller's own `load`, which LICM hoists before the loop.
    #[test]
    fn an_array_loop_reads_its_start_once() {
        let module = optimized(
            "fn sum(x: [int]) -> int { let mut s = 0; for a in x { s += a }; s }\n\
             fn main() -> int { sum([1, 2]) }",
        );
        let body = body_of(&module, "sum").split("\nfn ").next().unwrap();
        let header = body.find("check_fuel").expect("the loop checks fuel");
        let fields = body
            .lines()
            .filter(|line| line.contains("= subfield ") && line.ends_with(" from %p0"))
            .filter_map(|line| line.trim().split(':').next())
            .collect::<Vec<_>>();
        let reads = fields
            .iter()
            .filter_map(|field| body.find(&format!("= load {field}\n")))
            .collect::<Vec<_>>();
        assert!(
            !reads.is_empty() && reads.iter().all(|read| *read < header),
            "every scalar field of the array must be read once, before the loop:\n{body}"
        );
    }

    /// The physical MIR of `source`'s `negated`, which passes a comparison's result, a value no
    /// `load` defines, to a retained call; and that call's argument.
    fn computed_boolean_argument(source: &str, callee: &str) -> (String, String) {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.set_physical_mir_optimization(MirOptimization::Enabled);
        let module = session
            .compile(
                source,
                "computed_boolean",
                Path::single_str("computed_boolean"),
            )
            .unwrap()
            .module_id;
        let physical = session.emit_physical_mir_module(module).unwrap();
        let body = body_of(&physical, "negated")
            .split("\nfn ")
            .next()
            .unwrap()
            .to_string();
        let call = format!("call {callee}(");
        assert!(
            body.contains("comp_eq") && body.contains(&call),
            "the test needs `not x` computed by a comparison and the call retained:\n{body}"
        );
        let argument = body
            .lines()
            .find_map(|line| line.split(&call).nth(1))
            .and_then(|rest| rest.split([',', ')']).next())
            .unwrap()
            .to_string();
        (body, argument)
    }

    /// A direct entry takes a scalar as a value, so physical MIR passes it one.
    #[test]
    fn a_computed_boolean_argument_stays_a_value_for_a_direct_entry() {
        let (body, argument) = computed_boolean_argument(
            "#[inline(never)]\n\
             fn pick(b: bool) -> int { if b { 1 } else { 2 } }\n\
             pub fn negated(x: bool) -> int { pick(not x) }",
            "computed_boolean::pick",
        );
        assert!(
            body.contains(&format!("{argument}: bool")),
            "the argument must be a value:\n{body}"
        );
    }

    /// A stored callable's uniform entry takes every argument through a pointer, so physical
    /// lowering binds the value to a place.
    #[test]
    fn a_computed_boolean_argument_is_passed_as_a_place_to_a_callable() {
        let (body, argument) = computed_boolean_argument(
            "pub fn negated(f: (bool) -> int, x: bool) -> int { f(not x) }",
            "%p0",
        );
        assert!(
            body.contains(&format!("{argument}: place bool")),
            "the argument must be a place:\n{body}"
        );
    }

    /// Merging must not join a block a second predecessor also reaches: the arms of a branch meet
    /// at a join block, which has to stay a block of its own.
    #[test]
    fn a_join_block_is_not_merged() {
        let module = optimized(
            "fn use_it(n: int) -> int { let mut x = 0; if n > 10 { x = 1 } else { x = 2 }; x }",
        );
        let caller = body_of(&module, "use_it");
        assert!(
            caller.contains("condbr"),
            "the branch must survive an unknown condition:\n{caller}"
        );
        assert!(
            caller.contains("br b"),
            "the arms must still jump to their join block:\n{caller}"
        );
    }
}
