// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ustr::{Ustr, ustr};

use crate::{
    FxHashMap,
    hir::function::{CallableDefinition, StructuralFieldAddressor},
    module::{
        LocalSubscriptId, Module, ModuleFunction, ProjectionOrigin, SubscriptDefinition,
        SubscriptId, SubscriptMember, SubscriptSignature, TypeDefId, Visibility, YieldProvenance,
        id::Id,
    },
    types::{
        effects::no_effects,
        r#type::{CallResultConvention, FnArgType, FnType, Type, TypeKind},
        type_scheme::TypeScheme,
    },
};

/// Projection receiver lookup key.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProjectionReceiverKey {
    /// Compiler-generated structural projection for an exact receiver type.
    Structural(Type),
    /// Source-declared projection attached to a nominal type family.
    Nominal(TypeDefId),
}

/// Projection implementation lookup key.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProjectionKey {
    pub receiver: ProjectionReceiverKey,
    pub field: Ustr,
}

impl ProjectionKey {
    pub fn structural(receiver_ty: Type, field: Ustr) -> Self {
        Self {
            receiver: ProjectionReceiverKey::Structural(receiver_ty),
            field,
        }
    }

    pub fn nominal(receiver: TypeDefId, field: Ustr) -> Self {
        Self {
            receiver: ProjectionReceiverKey::Nominal(receiver),
            field,
        }
    }

    pub fn nominal_for_receiver_ty(receiver_ty: Type, field: Ustr) -> Option<Self> {
        let TypeKind::Named(named) = &*receiver_ty.data() else {
            return None;
        };
        Some(Self::nominal(named.def, field))
    }

    pub fn structural_receiver_ty(self) -> Type {
        match self.receiver {
            ProjectionReceiverKey::Structural(receiver_ty) => receiver_ty,
            ProjectionReceiverKey::Nominal(_) => {
                panic!(
                    "generated structural projection key should carry a structural receiver type"
                )
            }
        }
    }
}

/// Compiler-generated structural projection subscript generation recipe.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GeneratedStructuralProjectionSpec {
    pub key: ProjectionKey,
    pub index: usize,
    pub field_ty: Type,
}

/// Pending generated structural projection subscripts for one elaboration pass.
#[derive(Debug, Clone)]
pub(crate) struct PendingGeneratedStructuralProjectionSubscripts {
    module_id: crate::module::ModuleId,
    base_subscript: usize,
    known: FxHashMap<ProjectionKey, LocalSubscriptId>,
    pending: Vec<GeneratedStructuralProjectionSpec>,
}

impl PendingGeneratedStructuralProjectionSubscripts {
    pub(crate) fn new(module: &Module) -> Self {
        Self {
            module_id: module.module_id(),
            base_subscript: module.subscripts.len(),
            known: module
                .projection_subscripts
                .iter()
                .map(|(key, entry)| (*key, entry.subscript))
                .collect(),
            pending: Vec::new(),
        }
    }

    pub(crate) fn get_or_create(&mut self, spec: GeneratedStructuralProjectionSpec) -> SubscriptId {
        if let Some(id) = self.known.get(&spec.key).copied() {
            return SubscriptId::new(self.module_id, id);
        }
        let id = LocalSubscriptId::from_index(self.base_subscript + self.pending.len());
        self.pending.push(spec);
        self.known.insert(spec.key, id);
        SubscriptId::new(self.module_id, id)
    }

    pub(crate) fn get_existing(&self, key: ProjectionKey) -> Option<SubscriptId> {
        self.known
            .get(&key)
            .copied()
            .map(|id| SubscriptId::new(self.module_id, id))
    }

    pub(crate) fn commit(self, module: &mut Module) {
        assert_eq!(
            module.subscripts.len(),
            self.base_subscript,
            "generated structural projection subscript ids were reserved before another subscript was added"
        );
        for spec in self.pending {
            let id = module.get_or_add_generated_structural_projection_subscript(spec);
            debug_assert_eq!(self.known[&spec.key], id);
        }
    }
}

impl Module {
    /// Return a compiler-generated structural projection subscript for `spec`.
    ///
    /// The generated subscript is stored in this module artifact but is not
    /// entered in `def_table`, so it is not source-visible.
    pub(crate) fn get_or_add_generated_structural_projection_subscript(
        &mut self,
        spec: GeneratedStructuralProjectionSpec,
    ) -> LocalSubscriptId {
        let key = spec.key;
        let receiver_ty = key.structural_receiver_ty();
        if let Some(entry) = self.get_projection_subscript(key) {
            return entry.subscript;
        }

        let function = self.add_function_anonymous(ModuleFunction::new(
            CallableDefinition::new(
                TypeScheme::new_just_type(FnType::new(
                    vec![FnArgType::new_by_val(receiver_ty)],
                    spec.field_ty,
                    no_effects(),
                )),
                vec![ustr("receiver")],
                Some(format!(
                    "Compiler-generated projection addressor for field {}.",
                    key.field
                )),
            )
            .with_result_convention(CallResultConvention::ADDRESSOR_PLACE),
            Box::new(StructuralFieldAddressor::new(spec.index)),
            None,
            Vec::new(),
        ));
        let member = SubscriptMember {
            function,
            provenance: YieldProvenance::AddressorPlace,
        };
        let id = LocalSubscriptId::from_index(self.subscripts.len());
        self.subscripts.push(SubscriptDefinition {
            signature: SubscriptSignature {
                args: vec![FnArgType::new_by_val(receiver_ty)],
                ret: spec.field_ty,
                generic_params: Vec::new(),
                generic_effect_params: Vec::new(),
                arg_names: vec![ustr("receiver")],
                constraints: Vec::new(),
                doc: Some(format!(
                    "Compiler-generated projection subscript for field {}.",
                    key.field
                )),
            },
            ref_member: Some(member.clone()),
            mut_member: Some(member),
        });
        self.add_projection_subscript(
            key,
            id,
            Visibility::Module,
            ProjectionOrigin::GeneratedStructural,
        );
        id
    }
}
