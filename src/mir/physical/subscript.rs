// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Relocatable first-class subscript metadata carried by one physical MIR module.

use crate::{
    hir::dictionary::DictionaryReq,
    module::{
        FunctionId, LocalSubscriptId, Module, ModuleEnv, ModuleId, SubscriptId, SubscriptMember,
        YieldProvenance, id::Id,
    },
};

use super::evidence::PhysicalEvidenceReferences;

/// One callable member of a physical subscript definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PhysicalSubscriptMember {
    function: FunctionId,
    provenance: YieldProvenance,
}

impl PhysicalSubscriptMember {
    pub(crate) fn function(self) -> FunctionId {
        self.function
    }

    pub(crate) fn provenance(self) -> YieldProvenance {
        self.provenance
    }
}

/// A relocatable first-class subscript definition owned by one physical module.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct PhysicalSubscriptDefinition {
    id: SubscriptId,
    capture_schema: Box<[DictionaryReq]>,
    ref_member: Option<PhysicalSubscriptMember>,
    mut_member: Option<PhysicalSubscriptMember>,
}

impl PhysicalSubscriptDefinition {
    pub(crate) fn id(&self) -> SubscriptId {
        self.id
    }

    pub(crate) fn capture_schema(&self) -> &[DictionaryReq] {
        &self.capture_schema
    }

    pub(crate) fn member(&self, mut_member: bool) -> Option<PhysicalSubscriptMember> {
        if mut_member {
            self.mut_member
        } else {
            self.ref_member
        }
    }
}

/// Subscript definitions and unresolved foreign references for one physical MIR module.
#[derive(Clone, Debug)]
pub(super) struct PhysicalSubscriptCatalog {
    module: ModuleId,
    definitions: Box<[PhysicalSubscriptDefinition]>,
    imports: Box<[SubscriptId]>,
}

impl PhysicalSubscriptCatalog {
    pub(super) fn from_module(
        module: ModuleId,
        source: &Module,
        env: ModuleEnv<'_>,
        references: &PhysicalEvidenceReferences,
    ) -> Self {
        assert_eq!(source.module_id(), module);
        let definitions = (0..source.subscript_count())
            .map(|index| {
                let local = LocalSubscriptId::from_index(index);
                let definition = source
                    .get_subscript_by_id(local)
                    .expect("every subscript index has metadata");
                let capture_schema = definition
                    .type_scheme(source)
                    .expect("physical lowering requires a resolved subscript signature")
                    .extra_parameters(env)
                    .requirements
                    .into_boxed_slice();
                PhysicalSubscriptDefinition {
                    id: SubscriptId::new(module, local),
                    capture_schema,
                    ref_member: definition
                        .ref_member
                        .as_ref()
                        .map(|member| physical_member(module, member)),
                    mut_member: definition
                        .mut_member
                        .as_ref()
                        .map(|member| physical_member(module, member)),
                }
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();

        let mut imports = references
            .subscripts()
            .filter(|id| id.module != module)
            .collect::<Vec<_>>();
        imports.sort_by_key(|id| (id.module.as_index(), id.subscript.as_index()));

        Self {
            module,
            definitions,
            imports: imports.into_boxed_slice(),
        }
    }

    pub(crate) fn definitions(&self) -> &[PhysicalSubscriptDefinition] {
        &self.definitions
    }

    pub(crate) fn imports(&self) -> &[SubscriptId] {
        &self.imports
    }

    pub(crate) fn definition(&self, id: SubscriptId) -> Option<&PhysicalSubscriptDefinition> {
        if id.module != self.module {
            return None;
        }
        self.definitions.get(id.subscript.as_index())
    }

    pub(super) fn contains_reference(&self, id: SubscriptId) -> bool {
        self.definition(id).is_some() || self.imports.contains(&id)
    }
}

fn physical_member(module: ModuleId, member: &SubscriptMember) -> PhysicalSubscriptMember {
    PhysicalSubscriptMember {
        function: FunctionId::new(module, member.function),
        provenance: member.provenance,
    }
}
