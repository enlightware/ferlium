// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Relocatable trait-dictionary metadata carried by one physical MIR module.

use crate::{
    emit_mir::lower_static_evidence,
    hir::dictionary::DictionaryReq,
    mir::value::StaticEvidence,
    module::{
        DictionaryCaptureIndex, DictionaryEntryEvidence, FunctionId, LocalImplId, Module,
        ModuleEnv, ModuleId, ParentAccessor, TraitDictionaryEntry, TraitDictionaryId, TraitId,
        id::Id,
    },
    std::{
        core_traits_names::VALUE_TRAIT_NAME,
        value::{VALUE_ALIGN_ASSOC_CONST_INDEX, VALUE_SIZE_ASSOC_CONST_INDEX},
    },
    types::{r#trait::TraitDictionaryEntryIndex, r#type::Type},
};

use super::{
    evidence::{PhysicalEvidenceReferences, try_for_each_static_evidence},
    program::ProgramDescriptorId,
};
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

impl DictionaryReference {
    pub(crate) fn new(descriptor: ProgramDescriptorId, environment: usize) -> Self {
        Self {
            descriptor: descriptor.as_u32(),
            environment,
        }
    }

    /// The descriptor this reference names, or `None` for a word no descriptor index can hold.
    pub(crate) fn descriptor_id(self) -> Option<ProgramDescriptorId> {
        ProgramDescriptorId::try_from(self.descriptor as usize).ok()
    }
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

/// How a physical dictionary gives the dictionary of one of its trait's parent slots.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum PhysicalParentAccessor {
    /// This capture of the dictionary.
    Capture(DictionaryCaptureIndex),
    /// A static dictionary, which the program interns with its other static evidence.
    Static(StaticEvidence),
}

/// A relocatable dictionary definition owned by one physical MIR module.
///
/// Function and dictionary identities remain module-qualified. Later whole-program assembly may
/// deduplicate definitions and assign descriptor indexes.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct PhysicalDictionaryDefinition {
    id: TraitDictionaryId,
    trait_id: TraitId,
    ty: Type,
    capture_schema: Box<[DictionaryReq]>,
    capture_types: Box<[Type]>,
    environment: EvidenceEnvironmentLayout,
    layout_entries: Option<[usize; 2]>,
    entries: Box<[PhysicalDictionaryEntry]>,
    parents: Box<[PhysicalParentAccessor]>,
}

impl PhysicalDictionaryDefinition {
    pub(crate) fn trait_id(&self) -> TraitId {
        self.trait_id
    }

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

    /// The accessors of the parent slots of this dictionary's trait.
    pub(crate) fn parents(&self) -> &[PhysicalParentAccessor] {
        &self.parents
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
                    trait_id: implementation.trait_id,
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
                    parents: dictionary
                        .parents()
                        .iter()
                        .map(|parent| match parent {
                            ParentAccessor::Capture(index) => {
                                PhysicalParentAccessor::Capture(*index)
                            }
                            ParentAccessor::Pending(_) | ParentAccessor::Static(_) => {
                                PhysicalParentAccessor::Static(lower_static_evidence(
                                    parent.static_evidence().expect("a static parent accessor"),
                                ))
                            }
                        })
                        .collect(),
                }
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();

        // The static parents of a definition are references of its module too.
        let mut parent_dictionaries = Vec::new();
        for definition in &definitions {
            for parent in definition.parents() {
                if let PhysicalParentAccessor::Static(evidence) = parent {
                    let _ = try_for_each_static_evidence(evidence, &mut |evidence| {
                        if let StaticEvidence::Dictionary { definition, .. } = evidence {
                            parent_dictionaries.push(*definition);
                        }
                        Ok::<_, ()>(())
                    });
                }
            }
        }
        let mut imports = references
            .dictionaries()
            .chain(parent_dictionaries)
            .filter(|id| id.module_id != module)
            .collect::<Vec<_>>();
        imports.sort_by_key(|id| (id.module_id.as_index(), id.impl_id.as_index()));
        imports.dedup();

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
