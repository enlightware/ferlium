// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Sharing specialized bodies that become identical only once they are optimized.
//!
//! [`monomorphize`](super::monomorphize) already shares a body between the keys that produce it, at
//! the moment it is created. That reaches every group of copies that is identical *as substituted*,
//! which is most of them. It cannot reach the rest: two copies can be created distinct — reading
//! different dictionaries, say — and converge only once folding and inlining have resolved what
//! made them differ. Recognizing those means comparing bodies that have already been optimized,
//! which is what this pass does.
//!
//! **Whole-module and after the fact**, for the same reason
//! [`dead_evidence`](super::dead_evidence) is: every optimization decision was taken against the
//! set of functions the optimizer has always seen, and this only merges bodies nothing will consult
//! again. It runs *before* the owned-ABI variants are built, so those are derived from the
//! deduplicated set rather than duplicated along with it.
//!
//! Two things make this more than a grouping:
//!
//! - **The identity has to be read through the merges already decided.** Two bodies that each call
//!   a different copy of one callee are equal exactly when those copies merge, and the comparison
//!   reads raw operand ids. So the grouping repeats until a round merges nothing — one extra round
//!   in the common case, and what closes the mutually recursive one.
//! - **Compaction moves every later specialization**, so no id may be held across it. Merging and
//!   renumbering are therefore composed into one map and applied in a single rewrite; there is no
//!   intermediate module state in which some ids have moved and others have not.
//!
//! The rewrite reaches a function wherever a body names one, which is not only call callee
//! operands: `build_closure` carries a [`FunctionId`] in the operation kind, where no operand walk
//! sees it. Nothing writes a specialization there today — the specializer and the owned-ABI pass
//! both write only into call callees — but the distinction between "misses a sharing" and "leaves a
//! dangling id" is what makes that worth reaching anyway, and
//! [`OperationKind::visit_function_ids_mut`](crate::mir::OperationKind::visit_function_ids_mut) is
//! exhaustive so a later kind cannot quietly acquire one.

use rustc_hash::FxHashMap;

use crate::{
    compiler::Specialization,
    mir::{Function, edit::FunctionEdit},
    module::{FunctionId, LocalFunctionId, ModuleId, id::Id},
};

use super::monomorphize::{self_reference, structurally_identical, structure_digest};

/// Merges every specialization whose optimized body duplicates another's, and compacts the table.
///
/// `functions` is the module's HIR-declared prefix and `specializations` the bodies the optimizer
/// appended past it, which together are every body that can name one.
pub(crate) fn share_identical_specialization_bodies(
    functions: &mut [Option<Function>],
    specializations: Vec<Specialization>,
    module: ModuleId,
) -> Vec<Specialization> {
    let first_index = functions.len();
    if specializations.len() < 2 {
        return specializations;
    }
    debug_assert!(
        specializations.iter().all(|specialization| {
            specialization.original.module != module
                || specialization.original.function.as_index() < first_index
        }),
        "a specialization of a specialization would need its original remapped too"
    );

    let merged = group(&specializations, module, first_index);
    if merged
        .iter()
        .enumerate()
        .all(|(index, &into)| index == into)
    {
        return specializations;
    }

    // Merging and renumbering in one map: a body is rewritten once, from ids that all still mean
    // what they meant before this pass, to ids that all mean what they will mean after it.
    let mut compacted = vec![usize::MAX; merged.len()];
    let mut retained = 0;
    for (index, slot) in compacted.iter_mut().enumerate() {
        if resolve(&merged, index) == index {
            *slot = retained;
            retained += 1;
        }
    }
    let remap = |id: FunctionId| match specialization_index(id, module, first_index) {
        Some(index) => function_id(module, first_index, compacted[resolve(&merged, index)]),
        None => id,
    };

    for slot in functions.iter_mut() {
        if let Some(body) = slot.take() {
            *slot = Some(rewrite(body, &remap));
        }
    }
    specializations
        .into_iter()
        .enumerate()
        .filter(|(index, _)| resolve(&merged, *index) == *index)
        .map(|(_, specialization)| Specialization {
            body: rewrite(specialization.body, &remap),
            ..specialization
        })
        .collect()
}

/// For each specialization, the one it is merged into — itself when it survives.
///
/// Repeated until a round merges nothing, because the identity of a body that calls another
/// specialization depends on the merges already decided. Each round that changes anything strictly
/// reduces the surviving set, so this terminates in at most one round per specialization and in
/// practice in two: one that merges and one that confirms.
fn group(specializations: &[Specialization], module: ModuleId, first_index: usize) -> Vec<usize> {
    let mut merged: Vec<usize> = (0..specializations.len()).collect();
    loop {
        // Digest to at most one bucket of candidates, then let the bodies decide, so a collision
        // costs a sharing and can never merge two bodies that differ.
        let mut buckets: FxHashMap<u64, Vec<usize>> = FxHashMap::default();
        let mut changed = false;
        for index in 0..specializations.len() {
            if merged[index] != index {
                continue;
            }
            let specialization = &specializations[index];
            let digest = structure_digest(
                &specialization.body,
                specialization.original,
                &canonical(&merged, module, first_index, index),
            );
            let bucket = buckets.entry(digest).or_default();
            let survivor = bucket.iter().copied().find(|&other| {
                // Bodies are shared within one original and never across two: a specialization's
                // HIR metadata is answered through its original, so two originals with identical
                // MIR can still declare different parameter passing or return conventions.
                specializations[other].original == specialization.original
                    && structurally_identical(
                        &specialization.body,
                        &canonical(&merged, module, first_index, index),
                        &specializations[other].body,
                        &canonical(&merged, module, first_index, other),
                    )
            });
            match survivor {
                Some(survivor) => {
                    merged[index] = survivor;
                    changed = true;
                }
                None => bucket.push(index),
            }
        }
        if !changed {
            return merged;
        }
    }
}

/// How the body at `own` reads the functions it names, while deciding what body it is.
///
/// A reference to a copy already merged away reads as the copy it was merged into, and a reference
/// to `own` itself reads as the self-reference every copy shares — the two mappings compose, and a
/// survivor maps to itself under the first so the order between them does not matter.
fn canonical(
    merged: &[usize],
    module: ModuleId,
    first_index: usize,
    own: usize,
) -> impl Fn(FunctionId) -> FunctionId {
    let normalize_self = self_reference(function_id(module, first_index, own));
    move |id| {
        let surviving = match specialization_index(id, module, first_index) {
            Some(index) => function_id(module, first_index, resolve(merged, index)),
            None => id,
        };
        normalize_self(surviving)
    }
}

/// The specialization `index` survives as, following the chain when a survivor later merged too.
fn resolve(merged: &[usize], mut index: usize) -> usize {
    while merged[index] != index {
        index = merged[index];
    }
    index
}

/// Which specialization of this module `id` names, if it names one.
///
/// The module check is what makes a bare local index meaningful: another module's ordinary function
/// can hold the same one.
fn specialization_index(id: FunctionId, module: ModuleId, first_index: usize) -> Option<usize> {
    (id.module == module)
        .then(|| id.function.as_index().checked_sub(first_index))
        .flatten()
}

fn function_id(module: ModuleId, first_index: usize, index: usize) -> FunctionId {
    FunctionId {
        module,
        function: LocalFunctionId::from_index(first_index + index),
    }
}

/// Points every function reference in `body` at what it is called after this pass.
///
/// Applied to every body rather than only those that hold a moved reference: compaction moves
/// nearly all of them, and the walk is what decides whether one is held. Rewritten bodies are
/// verified with every other final artifact once this whole-module cleanup completes.
fn rewrite(body: Function, remap: &impl Fn(FunctionId) -> FunctionId) -> Function {
    let mut edit = FunctionEdit::new(body);
    edit.visit_function_ids_mut(|id| *id = remap(*id));
    edit.finish_unverified()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, MirOptimization, module::Path};

    /// The adapter workload is the one that shows this at all: closure-carrying adapter structs are
    /// where the copies that converge under optimization come from, and a module without them
    /// leaves the pass with nothing to do — see measurement lesson 8 in the plan.
    #[test]
    fn no_two_optimized_specializations_of_one_original_are_identical() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        // Builds and installs the optimized stage, which is the only way to ask for it.
        session.emit_mir(
            "iter_pipeline",
            include_str!("../../../tests/modules/iter_pipeline.fer"),
        );
        let (module_id, _) = session
            .modules()
            .get_by_path(&Path::single_str("iter_pipeline"))
            .expect("the module was just compiled");
        let optimized = session
            .mir_artifacts_for(module_id, MirOptimization::Enabled)
            .expect("optimized artifacts were just built");

        let first_index = optimized.bodies().len();
        let specializations = optimized.specializations();
        let id_of = |index: usize| function_id(module_id, first_index, index);

        // Without a repeated original nothing is ever compared, and the assertion below would hold
        // of a module this pass could not possibly help.
        let repeated = specializations.iter().any(|specialization| {
            specializations
                .iter()
                .filter(|other| other.original == specialization.original)
                .count()
                > 1
        });
        assert!(
            repeated,
            "no original was specialized twice, so this test proves nothing"
        );

        for (index, specialization) in specializations.iter().enumerate() {
            for (other, candidate) in specializations.iter().enumerate().take(index) {
                if candidate.original != specialization.original {
                    continue;
                }
                assert!(
                    !structurally_identical(
                        &specialization.body,
                        &self_reference(id_of(index)),
                        &candidate.body,
                        &self_reference(id_of(other)),
                    ),
                    "`{}` and `{}` are the same body and should have been shared",
                    specialization.name,
                    candidate.name
                );
            }
        }
    }
}
