// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ustr::Ustr;

use crate::{
    FxHashMap, Location, Modules,
    hir::dictionary::DictionaryReq,
    hir::function::CallableDefinition,
    module::{
        LocalSubscriptId, Module, ModuleEnv, ModuleFunction, ProjectionIndex, ProjectionOrigin,
        QualifiedNameEnv, SubscriptDefinition, SubscriptId, SubscriptMember,
        SubscriptMemberFunctionKind, SubscriptSignature, TypeDefId, Visibility, YieldProvenance,
        id::Id,
    },
    std::value::{TypeLayoutEnv, dynamic_product_member_layouts},
    types::{
        effects::EffType,
        r#type::{CallResultConvention, FnArgType, FnType, Type, TypeKind},
        type_scheme::PubTypeConstraint,
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
    pub index: ProjectionIndex,
    pub field_ty: Type,
}

/// Build the callable surface and hidden layout requirements shared by a generated structural
/// addressor's module definition and every use-site closure over it.
pub(crate) fn generated_structural_projection_definition(
    spec: GeneratedStructuralProjectionSpec,
    value_trait_id: crate::module::TraitId,
    env: &impl TypeLayoutEnv,
) -> (CallableDefinition, Vec<DictionaryReq>) {
    let receiver_ty = spec.key.structural_receiver_ty();
    let span = Location::new_synthesized();
    let member_tys = dynamic_product_member_layouts(receiver_ty, span, env);
    let requirements = member_tys
        .iter()
        .copied()
        .map(|member_ty| {
            DictionaryReq::new_trait_impl(value_trait_id, vec![member_ty], vec![], vec![])
        })
        .collect::<Vec<_>>();
    let constraints = member_tys
        .iter()
        .map(|member_ty| {
            PubTypeConstraint::new_have_trait(
                value_trait_id,
                vec![*member_ty],
                vec![],
                vec![],
                span,
            )
        })
        .collect::<Vec<_>>();
    let definition = CallableDefinition::new_infer_quantifiers_with_constraints(
        FnType::new(
            vec![FnArgType::new_by_val(receiver_ty)],
            spec.field_ty,
            EffType::empty(),
        ),
        constraints,
        ["receiver"],
        "Compiler-generated structural field addressor.",
    )
    .with_result_convention(CallResultConvention::ADDRESSOR_PLACE);
    (definition, requirements)
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

    pub(crate) fn commit(self, module: &mut Module, modules: &Modules) {
        assert_eq!(
            module.subscripts.len(),
            self.base_subscript,
            "generated structural projection subscript ids were reserved before another subscript was added"
        );
        for spec in self.pending {
            let id = module.get_or_add_generated_structural_projection_subscript(spec, modules);
            debug_assert_eq!(self.known[&spec.key], id);
        }
    }
}

impl Module {
    /// Return a compiler-generated structural projection subscript for `spec`.
    ///
    /// The generated subscript is stored in this module artifact but is not
    /// source-visible. Its backing function is named separately for debugging.
    pub(crate) fn get_or_add_generated_structural_projection_subscript(
        &mut self,
        spec: GeneratedStructuralProjectionSpec,
        modules: &Modules,
    ) -> LocalSubscriptId {
        let key = spec.key;
        if let Some(entry) = self.get_projection_subscript(key) {
            return entry.subscript;
        }

        let env = ModuleEnv::new(self, modules);
        let value_trait_id =
            env.expect_std_trait_id(crate::std::core_traits_names::VALUE_TRAIT_NAME);
        let (mut definition, requirements) =
            generated_structural_projection_definition(spec, value_trait_id, &env);
        definition.doc = Some(format!(
            "Compiler-generated projection subscript for field {}.",
            key.field
        ));
        let signature = SubscriptSignature::from_callable_definition(&definition);
        let function_name = {
            let qualified_name_env = QualifiedNameEnv::new_from_module(self, modules);
            let readable_subscript_name =
                qualified_name_env.qualified_projection_subscript_name(key);
            qualified_name_env.disambiguated_subscript_member_name(
                &readable_subscript_name,
                SubscriptMemberFunctionKind::RefMut,
                &definition,
                YieldProvenance::AddressorPlace,
            )
        };
        let function = self.add_function_anonymous(ModuleFunction::new_structural_field_addressor(
            definition,
            spec.index,
            requirements.len(),
        ));
        self.name_function_with_visibility(function, function_name.into(), Visibility::Module);
        let member = SubscriptMember {
            function,
            provenance: YieldProvenance::AddressorPlace,
        };
        let id = LocalSubscriptId::from_index(self.subscripts.len());
        let mut subscript = SubscriptDefinition::resolved(signature);
        subscript.ref_member = Some(member.clone());
        subscript.mut_member = Some(member);
        self.subscripts.push(subscript);
        self.add_projection_subscript(
            key,
            id,
            Visibility::Module,
            ProjectionOrigin::GeneratedStructural,
        );
        id
    }
}
