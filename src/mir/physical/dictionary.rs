// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Relocatable trait-dictionary metadata carried by one physical MIR module.

use crate::{
    hir::dictionary::DictionaryReq,
    module::{
        DictionaryEntryEvidence, FunctionId, LocalImplId, Module, ModuleId, TraitDictionaryEntry,
        TraitDictionaryId, id::Id,
    },
    types::{r#trait::TraitDictionaryEntryIndex, r#type::Type},
};

use super::evidence::PhysicalEvidenceReferences;

/// One entry in a module-owned physical dictionary definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PhysicalDictionaryEntry {
    function: FunctionId,
    capture_mapping: Box<[DictionaryEntryEvidence]>,
}

impl PhysicalDictionaryEntry {
    pub(crate) fn function(&self) -> FunctionId {
        self.function
    }

    pub(crate) fn capture_mapping(&self) -> &[DictionaryEntryEvidence] {
        &self.capture_mapping
    }
}

/// A relocatable dictionary definition owned by one physical MIR module.
///
/// Function and dictionary identities remain module-qualified. Later whole-program assembly may
/// deduplicate definitions without consulting semantic HIR; executors assign target indexes.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct PhysicalDictionaryDefinition {
    id: TraitDictionaryId,
    ty: Type,
    capture_schema: Box<[DictionaryReq]>,
    entries: Box<[PhysicalDictionaryEntry]>,
}

impl PhysicalDictionaryDefinition {
    pub(crate) fn ty(&self) -> Type {
        self.ty
    }

    pub(crate) fn id(&self) -> TraitDictionaryId {
        self.id
    }

    pub(crate) fn capture_schema(&self) -> &[DictionaryReq] {
        &self.capture_schema
    }

    pub(crate) fn entries(&self) -> &[PhysicalDictionaryEntry] {
        &self.entries
    }
}

/// Dictionary definitions and unresolved foreign references for one physical MIR module.
#[derive(Clone, Debug)]
pub(crate) struct PhysicalDictionaryCatalog {
    module: ModuleId,
    definitions: Box<[PhysicalDictionaryDefinition]>,
    imports: Box<[TraitDictionaryId]>,
}

impl PhysicalDictionaryCatalog {
    pub(super) fn from_module(
        module: ModuleId,
        source: &Module,
        references: &PhysicalEvidenceReferences,
    ) -> Self {
        assert_eq!(source.module_id(), module);
        let definitions = (0..source.impl_count())
            .map(|index| {
                let impl_id = LocalImplId::from_index(index);
                let implementation = source
                    .get_impl_data(impl_id)
                    .expect("every implementation index has metadata");
                let dictionary = &implementation.dictionary_value;
                let id = TraitDictionaryId::new(module, impl_id);
                let entries = (0..dictionary.entry_count())
                    .map(|index| {
                        let index = TraitDictionaryEntryIndex::from_index(index);
                        let TraitDictionaryEntry::Function(function) = dictionary.entry(index);
                        PhysicalDictionaryEntry {
                            function: FunctionId::new(module, function),
                            capture_mapping: dictionary
                                .entry_capture_mapping(index)
                                .to_vec()
                                .into_boxed_slice(),
                        }
                    })
                    .collect::<Vec<_>>()
                    .into_boxed_slice();
                PhysicalDictionaryDefinition {
                    id,
                    ty: implementation.dictionary_ty,
                    capture_schema: dictionary.capture_schema().to_vec().into_boxed_slice(),
                    entries,
                }
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();

        let mut imports = references
            .dictionaries()
            .filter(|id| id.module_id != module)
            .collect::<Vec<_>>();
        imports.sort_by_key(|id| (id.module_id.as_index(), id.impl_id.as_index()));

        Self {
            module,
            definitions,
            imports: imports.into_boxed_slice(),
        }
    }

    pub(crate) fn definitions(&self) -> &[PhysicalDictionaryDefinition] {
        &self.definitions
    }

    pub(crate) fn imports(&self) -> &[TraitDictionaryId] {
        &self.imports
    }

    pub(crate) fn definition(
        &self,
        id: TraitDictionaryId,
    ) -> Option<&PhysicalDictionaryDefinition> {
        if id.module_id != self.module {
            return None;
        }
        self.definitions.get(id.impl_id.as_index())
    }

    pub(super) fn contains_reference(&self, id: TraitDictionaryId) -> bool {
        self.definition(id).is_some() || self.imports.contains(&id)
    }
}
