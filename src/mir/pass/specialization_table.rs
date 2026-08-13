// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Rewriting the specialization table the optimizer appended past a module's declared functions.
//!
//! Two passes decide which bodies that table should hold —
//! [`share_specializations`](super::share_specializations) merges the ones that duplicate each
//! other, [`prune_specializations`](super::prune_specializations) drops the ones nothing calls — and
//! they run on opposite sides of [`owned_arguments`](super::owned_arguments), which both consumes
//! and produces specialization references. What they share is not the decision but what follows it:
//! removing any entry renumbers every later one, and no id may be held across that.
//!
//! [`rewrite`] is therefore the single place a table is renumbered. A pass states only where each
//! index goes, and merging with compaction is composed into one map applied in one walk; there is no
//! intermediate module state in which some ids have moved and others have not.

use crate::{
    compiler::Specialization,
    mir::{Function, edit::FunctionEdit},
    module::{FunctionId, LocalFunctionId, ModuleId, id::Id},
};

/// Where the specializations of one module live in its function table.
///
/// Carried together because neither half is meaningful alone: a bare local index is only a
/// specialization of *this* module, and only past the declared functions it was appended to.
#[derive(Clone, Copy)]
pub(super) struct SpecializationTable {
    module: ModuleId,
    first_index: usize,
}

impl SpecializationTable {
    /// `functions` is the module's HIR-declared prefix, which the specializations follow.
    pub(super) fn new(module: ModuleId, functions: &[Option<Function>]) -> Self {
        Self {
            module,
            first_index: functions.len(),
        }
    }

    /// Which specialization of this module `id` names, if it names one.
    ///
    /// The module check is what makes a bare local index meaningful: another module's ordinary
    /// function can hold the same one.
    pub(super) fn index_of(&self, id: FunctionId) -> Option<usize> {
        (id.module == self.module)
            .then(|| id.function.as_index().checked_sub(self.first_index))
            .flatten()
    }

    pub(super) fn id_of(&self, index: usize) -> FunctionId {
        FunctionId {
            module: self.module,
            function: LocalFunctionId::from_index(self.first_index + index),
        }
    }
}

/// Applies `survives` to the table, renumbering every reference to it in one walk.
///
/// `survives` answers, for each specialization index, the index it is represented by afterwards —
/// itself when it is kept as it is, another entry's when it has been merged away, and `None` when it
/// is removed outright. An index that maps to one which does not itself survive is followed no
/// further: a caller that merges must resolve its own chains before answering here, because this
/// cannot tell "merged into" from "kept".
///
/// Applied to every body rather than only those holding a moved reference: compaction moves nearly
/// all of them, and the walk is what decides whether one is held. Rewritten bodies are verified with
/// every other final artifact once the whole-module cleanup completes.
pub(super) fn rewrite(
    functions: &mut [Option<Function>],
    specializations: Vec<Specialization>,
    table: SpecializationTable,
    survives: impl Fn(usize) -> Option<usize>,
) -> Vec<Specialization> {
    let kept: Vec<Option<usize>> = (0..specializations.len()).map(&survives).collect();
    if kept
        .iter()
        .enumerate()
        .all(|(index, &into)| into == Some(index))
    {
        return specializations;
    }

    // Merging and renumbering in one map: a body is rewritten once, from ids that all still mean
    // what they meant before the pass, to ids that all mean what they will mean after it.
    let mut compacted = vec![usize::MAX; kept.len()];
    let mut retained = 0;
    for (index, slot) in compacted.iter_mut().enumerate() {
        if kept[index] == Some(index) {
            *slot = retained;
            retained += 1;
        }
    }
    let remap = |id: FunctionId| match table.index_of(id) {
        // A reference to a removed body is left naming an index that no longer exists, which
        // verification catches. Passes that remove must show nothing names what they removed.
        Some(index) => match kept[index] {
            Some(into) => table.id_of(compacted[into]),
            None => id,
        },
        None => id,
    };

    for slot in functions.iter_mut() {
        if let Some(body) = slot.take() {
            *slot = Some(rewrite_body(body, &remap));
        }
    }
    specializations
        .into_iter()
        .enumerate()
        .filter(|(index, _)| kept[*index] == Some(*index))
        .map(|(_, specialization)| Specialization {
            body: rewrite_body(specialization.body, &remap),
            ..specialization
        })
        .collect()
}

/// Points every function reference in `body` at what it is called after the rewrite.
fn rewrite_body(body: Function, remap: &impl Fn(FunctionId) -> FunctionId) -> Function {
    let mut edit = FunctionEdit::new(body);
    edit.visit_function_ids_mut(|id| *id = remap(*id));
    edit.finish_unverified()
}
