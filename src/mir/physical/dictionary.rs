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
        DictionaryEntryEvidence, FunctionId, LocalImplId, Module, ModuleEnv, ModuleId,
        TraitDictionaryEntry, TraitDictionaryId, id::Id,
    },
    std::{
        core_traits_names::VALUE_TRAIT_NAME,
        value::{VALUE_ALIGN_ASSOC_CONST_INDEX, VALUE_SIZE_ASSOC_CONST_INDEX},
    },
    types::{r#trait::TraitDictionaryEntryIndex, r#type::Type},
};

use super::evidence::PhysicalEvidenceReferences;
use std::{
    alloc::{Layout, LayoutError},
    rc::Rc,
};

/// ABI descriptor/environment pair. Module-qualified symbols are relocated before storage.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct DictionaryReference {
    pub(crate) descriptor: u32,
    pub(crate) environment: usize,
}

/// Ordered physical capture fields, following a pointer-sized reference count (zero for static data).
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct EvidenceEnvironmentLayout {
    pub(crate) allocation: Layout,
    pub(crate) fields: Rc<[EvidenceCaptureField]>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct EvidenceCaptureField {
    pub(crate) offset: usize,
    /// A one-byte variant-storage choice; other captures use the descriptor/environment pair.
    pub(crate) is_storage_flag: bool,
}

impl EvidenceEnvironmentLayout {
    pub(crate) fn new(storage_flags: impl IntoIterator<Item = bool>) -> Result<Self, LayoutError> {
        let mut allocation = Layout::new::<usize>();
        let mut fields = Vec::new();
        for storage in storage_flags {
            let field = if storage {
                Layout::new::<bool>()
            } else {
                Layout::new::<DictionaryReference>()
            };
            let (layout, offset) = allocation.extend(field)?;
            allocation = layout;
            fields.push(EvidenceCaptureField {
                offset,
                is_storage_flag: storage,
            });
        }
        Ok(Self {
            allocation: allocation.pad_to_align(),
            fields: fields.into(),
        })
    }
}

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
/// deduplicate definitions and assign descriptor indexes without consulting semantic HIR.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct PhysicalDictionaryDefinition {
    id: TraitDictionaryId,
    ty: Type,
    capture_schema: Box<[DictionaryReq]>,
    capture_types: Box<[Type]>,
    environment: EvidenceEnvironmentLayout,
    layout_entries: Option<[usize; 2]>,
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

    pub(crate) fn capture_types(&self) -> &[Type] {
        &self.capture_types
    }

    pub(crate) fn environment(&self) -> &EvidenceEnvironmentLayout {
        &self.environment
    }

    pub(crate) fn layout_entries(&self) -> Option<[usize; 2]> {
        self.layout_entries
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
        env: ModuleEnv<'_>,
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
                    capture_types: dictionary
                        .capture_schema()
                        .iter()
                        .map(|r| r.to_dict_type_in_env(&env))
                        .collect(),
                    environment: EvidenceEnvironmentLayout::new(
                        dictionary
                            .capture_schema()
                            .iter()
                            .map(|r| matches!(r, DictionaryReq::VariantPayloadIndirection { .. })),
                    )
                    .expect("dictionary environment layout fits the target"),
                    layout_entries: (implementation.trait_id
                        == env.expect_std_trait_id(VALUE_TRAIT_NAME))
                    .then(|| {
                        let definition = env.trait_def(implementation.trait_id);
                        [VALUE_SIZE_ASSOC_CONST_INDEX, VALUE_ALIGN_ASSOC_CONST_INDEX].map(|index| {
                            definition
                                .dictionary_associated_const_index(index)
                                .as_index()
                        })
                    }),
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
