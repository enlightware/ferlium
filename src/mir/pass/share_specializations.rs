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
//! One thing makes this more than a grouping: **the identity has to be read through the merges
//! already decided.** Two bodies that each call a different copy of one callee are equal exactly
//! when those copies merge, and the comparison reads raw operand ids. So the grouping repeats until
//! a round merges nothing — one extra round in the common case, and what closes the mutually
//! recursive one.
//!
//! Renumbering the table afterwards belongs to
//! [`specialization_table`](super::specialization_table), which this shares with
//! [`prune_specializations`](super::prune_specializations).

use rustc_hash::FxHashMap;

use crate::{
    compiler::Specialization,
    mir::Function,
    module::{FunctionId, ModuleId},
};

use super::{
    monomorphize::{self_reference, structurally_identical, structure_digest},
    specialization_table::{self, SpecializationTable},
};

/// Merges every specialization whose optimized body duplicates another's, and compacts the table.
///
/// `functions` is the module's HIR-declared prefix and `specializations` the bodies the optimizer
/// appended past it, which together are every body that can name one.
pub(crate) fn share_identical_specialization_bodies(
    functions: &mut [Option<Function>],
    specializations: Vec<Specialization>,
    module: ModuleId,
) -> Vec<Specialization> {
    let table = SpecializationTable::new(module, functions);
    if specializations.len() < 2 {
        return specializations;
    }
    debug_assert!(
        specializations
            .iter()
            .all(|specialization| table.index_of(specialization.original).is_none()),
        "a specialization of a specialization would need its original remapped too"
    );

    // Chains are resolved here rather than in the rewrite, which cannot tell an entry merged into
    // another from one kept as it is.
    let merged = group(&specializations, table);
    specialization_table::rewrite(functions, specializations, table, |index| {
        Some(resolve(&merged, index))
    })
}

/// For each specialization, the one it is merged into — itself when it survives.
///
/// Repeated until a round merges nothing, because the identity of a body that calls another
/// specialization depends on the merges already decided. Each round that changes anything strictly
/// reduces the surviving set, so this terminates in at most one round per specialization and in
/// practice in two: one that merges and one that confirms.
fn group(specializations: &[Specialization], table: SpecializationTable) -> Vec<usize> {
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
                &canonical(&merged, table, index),
            );
            let bucket = buckets.entry(digest).or_default();
            let survivor = bucket.iter().copied().find(|&other| {
                // Bodies are shared within one original and never across two: a specialization's
                // HIR metadata is answered through its original, so two originals with identical
                // MIR can still declare different parameter passing or return conventions.
                specializations[other].original == specialization.original
                    && structurally_identical(
                        &specialization.body,
                        &canonical(&merged, table, index),
                        &specializations[other].body,
                        &canonical(&merged, table, other),
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
    table: SpecializationTable,
    own: usize,
) -> impl Fn(FunctionId) -> FunctionId {
    let normalize_self = self_reference(table.id_of(own));
    move |id| {
        let surviving = match table.index_of(id) {
            Some(index) => table.id_of(resolve(merged, index)),
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

        let table = SpecializationTable::new(module_id, optimized.bodies());
        let specializations = optimized.specializations();
        let id_of = |index: usize| table.id_of(index);

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
