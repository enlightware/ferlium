// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! The MIR optimization passes and the driver that runs them.
//!
//! A function is opened with [`FunctionEdit`](crate::mir::edit::FunctionEdit), rewritten in place,
//! and closed again to restore canonical form. Internal pass transitions deliberately skip global
//! verification; [`MirArtifacts`](crate::compiler::artifacts::MirArtifacts) verifies every final
//! body once after the whole-module cleanup. The driver alternates folding and inlining for a
//! bounded number of rounds, because the two feed each other: inlining
//! binds a callee's dictionary parameters to constants, folding then resolves the callee's
//! `dict_entry`s into known function places, and the calls that become direct are new candidates
//! for both. Fold first within a round — it is cheap, it is what makes arguments known, and it
//! shrinks a function before the inliner measures it against its growth budget.
//!
//! Both passes **merge** jump-joined blocks before closing their own edit, because both leave them:
//! inlining splits every call site's block whether or not the callee needed it, and folding turns a
//! `condbr` on a known condition into a jump. Merging belongs inside each pass rather than as a
//! round of its own — keeping canonical cleanup with the rewrite that creates it avoids another
//! body decomposition and reconstruction.
//!
//! Optimization terminates on three independent bounds: the dataflow lattice is monotone within a
//! run, inlining is bounded by its growth budget and the non-recursive restriction, and
//! [`MAX_ROUNDS`](budget::MAX_ROUNDS) bounds the outer loop.
//!
//! The driver is per module and reads the raw stage of every body it consults, so a result never
//! depends on the order functions are optimized in. Inlining may cross module boundaries — that is
//! where most inlinable script callees live — which is sound because function, dictionary and
//! subscript identities are global while constant identities are function-local and remapped into
//! the caller's pool. This is not whole-program optimization: nothing outside the module being
//! optimized is modified.

pub(crate) mod bounds_check;
pub(crate) mod branch_forward;
pub mod budget;
pub(crate) mod call_graph;
pub(crate) mod copy_forward;
pub(crate) mod cse;
pub(crate) mod dataflow;
pub(crate) mod dce;
pub(crate) mod dead_evidence;
pub(crate) mod fold;
pub(crate) mod inline;
pub(crate) mod known_callee;
pub(crate) mod monomorphize;
pub(crate) mod owned_arguments;
pub(crate) mod peephole;
pub(crate) mod provenance;
pub(crate) mod prune_specializations;
pub(crate) mod relations;
pub mod report;
pub(crate) mod share_specializations;
pub(crate) mod site;
pub(crate) mod specialization_table;
pub(crate) mod stack_region;
pub(crate) mod string_accumulate;

pub(crate) use monomorphize::Specializations;

use crate::{
    compiler::{CompilerSession, MirOptimization, Modules},
    mir::Function,
    module::{ModuleEnv, ModuleId},
};

use self::provenance::AddressorSummary;

/// Aggregate facts about rewrites whose results cannot be reconstructed from final MIR.
///
/// Most of the optimization report is derived after the fact. A removed operation is different:
/// once cleanup has collected the call and its error path, the artifact contains no reliable way
/// to distinguish that rewrite from folding or inlining. Keep only those irrecoverable counts here.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct OptimizationStats {
    pub(crate) bounds_checks_removed: usize,
}

/// Standard-library identities resolved once for every body optimized in one module.
///
/// [`known_callee::KnownCallees`] remains the shared semantic model used by dataflow analyses;
/// pass-specific identity bundles live beside it rather than broadening that model with operations
/// only one exact rewrite understands.
pub(crate) struct OptimizationContext {
    known_callees: known_callee::KnownCallees,
    string_functions: string_accumulate::StringFunctions,
}

impl OptimizationContext {
    pub(crate) fn new(modules: &Modules, env: ModuleEnv<'_>) -> Self {
        Self {
            known_callees: known_callee::KnownCallees::new(modules),
            string_functions: string_accumulate::StringFunctions::resolve(env),
        }
    }
}

/// Optimizes one function, returning the body to install.
///
/// Each round rewrites an immutable function into a new one, so a pass never reads an analysis that
/// its own edits have invalidated. A round that changes nothing ends the loop; the rounds exist
/// because folding and inlining feed each other, and because a chain of folds that crosses block
/// boundaries needs the analysis to be re-run to propagate.
pub(crate) fn optimize_function(
    function: &Function,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
    specializations: &mut Specializations,
    context: &OptimizationContext,
    stats: &mut OptimizationStats,
) -> Function {
    let original_size = function.operation_count();
    let mut current: Option<Function> = None;
    let mut rounds_exhausted = true;
    for _round in 0..budget::MAX_ROUNDS {
        // Fold first: it is cheap, it is what makes arguments known, and it shrinks a function
        // before the inliner measures it against its growth budget. Inlining then hands the next
        // round a body whose parameters have become the caller's places.
        let mut changed = false;
        let source = current.as_ref().unwrap_or(function);
        if let Some(folded) = fold::fold_function(source, env, session, module_id) {
            current = Some(folded.body);
            // A rewrite that cannot enable another one must not buy a round; see `Folded`.
            changed |= folded.warrants_another_round;
        }
        // Specialization before inlining: it rewrites a generic call into a call on a concrete
        // copy, whose dictionaries are constants the *next* round's folding resolves. That is what
        // reaches this language's generic code at all — see `monomorphize`.
        let source = current.as_ref().unwrap_or(function);
        if let Some(specialized) =
            monomorphize::specialize_call_sites(source, env, session, module_id, specializations)
        {
            current = Some(specialized);
            changed = true;
        }
        // Calls are merged before inlining so one body is copied per distinct computation, rather
        // than copying duplicates and trying to rediscover the whole computation afterwards.
        // Addressors additionally use provenance. A specialization inherits its original's
        // conservative addressor summary:
        // substitution cannot change provenance, and a repeatability proof remains true when types
        // are substituted or operations removed. An unresolved original remains conservatively
        // non-repeatable even when its concrete copy could prove more.
        let source = current.as_ref().unwrap_or(function);
        let summary_of = |callee| {
            let original = specializations.original(callee).unwrap_or(callee);
            session
                .mir_artifacts_for(original.module, MirOptimization::Disabled)
                .map_or(AddressorSummary::UNKNOWN, |artifacts| {
                    artifacts.addressor_summary(original.module, original.function)
                })
        };
        if let Some(merged) = cse::eliminate_common_calls(source, env, &summary_of) {
            current = Some(merged);
            changed = true;
        }
        // Lowering and value-call CSE both leave results in fresh slots before transferring them to
        // their real destinations. Storage forwarding is a separate proof from expression
        // equivalence. Run its cheap structural scan every round before inlining so the body being
        // priced has already lost provably redundant result slots, transfers and allocations.
        let source = current.as_ref().unwrap_or(function);
        if let Some(forwarded) = copy_forward::forward_redundant_storage(source, env) {
            current = Some(forwarded);
            changed = true;
        }
        // The place-producing operations are merged here too, before inlining rather than only
        // after it, because their redundancy is already present: a generic body reads the same
        // `dict_entry` once per use of the trait method. Merging them shrinks the body before the
        // inliner prices it against its growth budget, and two calls whose only difference was
        // which copy of an entry they named become one expression for the pass above.
        let source = current.as_ref().unwrap_or(function);
        if let Some(merged) = cse::eliminate_common_subexpressions(source) {
            current = Some(merged);
            changed = true;
        }
        // Now inlining.
        let source = current.as_ref().unwrap_or(function);
        if let Some(inlined) = inline::inline_function(
            source,
            original_size,
            env,
            session,
            module_id,
            specializations,
        ) {
            current = Some(inlined);
            changed = true;
        }
        if !changed {
            rounds_exhausted = false;
            break;
        }
    }
    if rounds_exhausted {
        // The last changing round may have exposed place computations and storage transfers after
        // their pre-inline placements. When a no-change round ended the loop, those placements have
        // already seen the settled body, so repeating them would deliver no additional work.
        let source = current.as_ref().unwrap_or(function);
        if let Some(merged) = cse::eliminate_common_subexpressions(source) {
            current = Some(merged);
        }
        let source = current.as_ref().unwrap_or(function);
        if let Some(forwarded) = copy_forward::forward_redundant_storage(source, env) {
            current = Some(forwarded);
        }
    }
    // Inlined predicates often materialize `true`/`false` in two arms only for the caller to
    // compare that slot with `true` and branch again. Forward the known edge information while
    // retaining any stack restoration at the join. DCE below then removes the dead slot/stores.
    let source = current.as_ref().unwrap_or(function);
    if let Some(forwarded) = branch_forward::forward_boolean_branches(source) {
        current = Some(forwarded);
    }
    // A predicate returned as a value often lowers to a tiny diamond whose arms only store opposite
    // boolean constants to the same destination. Collapse that materialization before DCE cleans up
    // any now-unused boolean storage and stranded blocks.
    let source = current.as_ref().unwrap_or(function);
    if let Some(materialized) = peephole::materialize_boolean_results(source) {
        current = Some(materialized);
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
    if rounds_exhausted {
        // Inlining in the last permitted round can expose a dictionary-entry dispatch after the
        // last fold placement. A converged round has already devirtualized the settled body; the
        // post-round branch, peephole and string rewrites above cannot expose a dictionary callee.
        let source = current.as_ref().unwrap_or(function);
        if let Some(devirtualized) = fold::devirtualize_known_callees(source, env) {
            current = Some(devirtualized);
        }
    }
    // After devirtualization, which is what makes a subscript's checks direct calls the analysis can
    // resolve at all, and before DCE, which removes the cleanup blocks a removed check strands.
    let source = current.as_ref().unwrap_or(function);
    if let Some((rewritten, removed)) =
        bounds_check::eliminate_bounds_checks(source, &context.known_callees, &|callee| {
            specializations.original(callee)
        })
    {
        stats.bounds_checks_removed += removed;
        current = Some(rewritten);
    }
    // Cleanup runs once, after the rounds have settled, and on every body rather than only on one a
    // pass changed. A specialization arrives already carrying dead code — substitution turns its
    // semantic clones and drops into representation copies and nothing, leaving the dictionary
    // entries they read unread — so "nothing changed it, so nothing is dead" no longer holds.
    let source = current.as_ref().unwrap_or(function);
    if let Some(cleaned) = dce::remove_dead_storage(source) {
        current = Some(cleaned);
    }
    // Last, after DCE has emptied every bracket it can. What remains reclaims real storage and
    // must stay: a bracket is where a live range ends, which a backend's stack-slot allocator
    // needs. Only a marker duplicating one already held, and a restore to the frontier already
    // current, are removed here — neither carries information the surviving marker does not.
    let source = current.as_ref().unwrap_or(function);
    if let Some(canonicalized) = stack_region::remove_redundant_stack_markers(source) {
        current = Some(canonicalized);
    }
    // Final artifact verification covers unchanged functions too, so cloning is the identity here.
    match current {
        Some(rewritten) => rewritten,
        None => function.clone(),
    }
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization};

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
