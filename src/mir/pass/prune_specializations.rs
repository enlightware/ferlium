// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Dropping the specializations nothing calls any more.
//!
//! A specialization is created for one call site, and the optimizer then keeps working on that site.
//! It may inline the copy it just asked for; the caller may itself be specialized, so the reference
//! moves to a copy of the caller and the original loses it;
//! [`owned_arguments`](super::owned_arguments) may redirect the call to an `#owned` variant. Each of
//! those leaves a finished, optimized body nothing names. Nothing revisited the table until this.
//!
//! **This needs no root analysis, which is what makes it cheap and certain.** Removing a *declared*
//! body would: an embedder can call any of them, so the roots have to be defined before anything can
//! be shown unreachable. A specialization is reachable from outside the module by no route at all —
//! `specialize_call_sites` only ever writes one into a call callee operand, self-calls are
//! redirected inside the same table, every cross-module lookup reads the raw stage, which holds no
//! specializations, and dictionaries name impls rather than functions. So the declared bodies are
//! the roots, in full, and the question is only which specializations they reach.
//!
//! Liveness only shrinks, so unlike [sharing](super::share_specializations) this needs no fixpoint —
//! one transitive closure answers it. It does have to *be* transitive: a specialization's callees
//! may be named by nothing else, and removing it makes them dead in turn.
//!
//! **After the owned-ABI variants**, which is the opposite side of them from sharing. Sharing must
//! run first so the variants are derived from the deduplicated set; pruning must run after, or every
//! body orphaned by a redirect to a variant survives. The two cannot be one pass for that reason.

use crate::{
    compiler::Specialization,
    mir::Function,
    module::{FunctionId, ModuleId},
};

use super::specialization_table::{self, SpecializationTable};

/// Removes every specialization unreachable from the module's declared functions, and compacts the
/// table.
///
/// Returns the surviving specializations and how many were dropped — a count worth keeping, because
/// it is the difference between the bodies the optimizer built and the bodies it kept, which no
/// other output states once the discarded ones are gone.
pub(crate) fn drop_unreachable_specializations(
    functions: &mut [Option<Function>],
    specializations: Vec<Specialization>,
    module: ModuleId,
) -> (Vec<Specialization>, usize) {
    let table = SpecializationTable::new(module, functions);
    if specializations.is_empty() {
        return (specializations, 0);
    }

    let live = reachable(functions, &specializations, table);
    let dropped = live.iter().filter(|reached| !**reached).count();
    let specializations =
        specialization_table::rewrite(functions, specializations, table, |index| {
            live[index].then_some(index)
        });
    (specializations, dropped)
}

/// Which specializations the declared bodies reach, directly or through another specialization.
fn reachable(
    functions: &[Option<Function>],
    specializations: &[Specialization],
    table: SpecializationTable,
) -> Vec<bool> {
    let mut live = vec![false; specializations.len()];
    let mut worklist = Vec::new();
    let discover = |id: FunctionId, live: &mut Vec<bool>, worklist: &mut Vec<usize>| {
        if let Some(index) = table.index_of(id)
            && !live[index]
        {
            live[index] = true;
            worklist.push(index);
        }
    };

    for body in functions.iter().flatten() {
        body.visit_function_ids(|id| discover(id, &mut live, &mut worklist));
    }
    while let Some(index) = worklist.pop() {
        specializations[index]
            .body
            .visit_function_ids(|id| discover(id, &mut live, &mut worklist));
    }
    live
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, MirOptimization, module::Path};

    /// Optimizes linalg and hands the finished artifact to `check`.
    ///
    /// linalg is the fixture because it calls every generic body at two element types and then
    /// inlines most of the copies it asked for, which is exactly the population this pass exists
    /// for. Its subscripts need the experimental gate. The artifact borrows the session, so the
    /// assertions run inside rather than taking a copy — `Specialization` is deliberately not
    /// `Clone`.
    fn with_optimized_linalg(
        check: impl FnOnce(ModuleId, &[Option<Function>], &[Specialization], usize),
    ) {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.set_allow_experimental(true);
        // Builds and installs the optimized stage, which is the only way to ask for it.
        session.emit_mir("linalg", include_str!("../../../tests/modules/linalg.fer"));
        let (module_id, _) = session
            .modules()
            .get_by_path(&Path::single_str("linalg"))
            .expect("the module was just compiled");
        let optimized = session
            .mir_artifacts_for(module_id, MirOptimization::Enabled)
            .expect("optimized artifacts were just built");
        check(
            module_id,
            optimized.bodies(),
            optimized.specializations(),
            optimized.pruned_specializations(),
        );
    }

    /// The property this pass exists for, stated over the finished artifact: every specialization
    /// that survives is named by something that survives.
    ///
    /// Deliberately re-derives reachability from the bodies rather than trusting the pass's own
    /// bookkeeping, so a table left holding an entry nobody calls fails here even if the count says
    /// otherwise.
    #[test]
    fn every_surviving_specialization_is_reachable() {
        with_optimized_linalg(|module_id, functions, specializations, _| {
            assert!(
                !specializations.is_empty(),
                "this module must specialize, or the assertion below is vacuous"
            );
            let table = SpecializationTable::new(module_id, functions);
            let live = reachable(functions, specializations, table);
            let unreachable: Vec<_> = specializations
                .iter()
                .zip(&live)
                .filter(|(_, reached)| !**reached)
                .map(|(specialization, _)| specialization.name)
                .collect();
            assert!(
                unreachable.is_empty(),
                "specializations nothing calls survived: {unreachable:?}"
            );
        });
    }

    /// The pass must remove bodies rather than be a no-op that trivially satisfies the property
    /// above, so this pins that the corpus really does orphan specializations.
    ///
    /// Bounds rather than an exact count: the number moves with every inlining budget change, and
    /// pinning it exactly would make this a change detector for passes it is not about.
    #[test]
    fn a_module_that_inlines_its_own_specializations_loses_some() {
        with_optimized_linalg(|_, _, specializations, pruned| {
            assert!(
                pruned > 0,
                "linalg orphans specializations by inlining them, so some must be pruned"
            );
            assert!(
                !specializations.is_empty(),
                "pruning everything would mean the declared bodies were not taken as roots"
            );
        });
    }
}
