// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    Location,
    compiler::error::InternalCompilationError,
    containers::b,
    hir::{
        self, NodeArena, NodeId, function::FunctionDefinition,
        value_dispatch::static_apply_generated_with_locals,
    },
    module::{Module, PendingFunctionBody, TraitId, TraitImplId},
    std::product_value_deriver::ProductValueDeriver,
    types::effects::EffType,
    types::r#trait::{Deriver, Trait, TraitMethodIndex},
    types::trait_solver::TraitSolver,
    types::r#type::{FnType, Type, TypeKind},
    types::type_like::TypeLike,
};

use FunctionDefinition as Def;

#[derive(Debug, Clone)]
struct EnumDefaultDeriver;

impl Deriver for EnumDefaultDeriver {
    fn derive_impl(
        &self,
        trait_id: TraitId,
        input_types: &[Type],
        span: Location,
        _arena: &mut NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        use hir::hir_syn::*;

        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

        let ty_data = ty.data();
        let TypeKind::Named(named) = &*ty_data else {
            return Ok(None);
        };
        let named = named.clone();
        drop(ty_data);
        let type_def = solver.type_def(named.def);
        let Some(default_variant) = type_def.default_variant else {
            return Ok(None);
        };

        let shape = type_def.instantiated_shape_with_effects(&named.params, &named.effect_params);
        let shape_data = shape.data();
        let payload_ty = shape_data
            .as_variant()
            .and_then(|variants| {
                variants.iter().find_map(|(name, payload_ty)| {
                    (*name == default_variant).then_some(*payload_ty)
                })
            })
            .expect("default variant must exist on enum type definitions");
        drop(shape_data);

        let mut body_arena = NodeArena::default();
        let mut locals = Vec::new();
        let n = |arena: &mut NodeArena, kind: hir::NodeKind, ty: Type| -> NodeId {
            arena.alloc(hir::Node::new(
                kind,
                ty,
                EffType::empty(),
                Location::new_synthesized(),
            ))
        };

        let root = if payload_ty == Type::unit() {
            let payload = n(&mut body_arena, native(()), Type::unit());
            n(&mut body_arena, variant(default_variant, payload), ty)
        } else {
            let function = solver.solve_impl_method(
                trait_id,
                &[payload_ty],
                TraitMethodIndex(0),
                span,
                &mut body_arena,
            )?;
            let payload = static_apply_generated_with_locals(
                &mut body_arena,
                &mut locals,
                solver,
                function,
                std::iter::empty(),
                payload_ty,
                span,
            )?;
            n(&mut body_arena, variant(default_variant, payload), ty)
        };

        let impl_id = solver.add_concrete_impl_from_code(
            PendingFunctionBody::new(body_arena, root),
            locals,
            trait_id,
            input_types,
            [],
        );
        Ok(Some(TraitImplId::new(
            solver.current_type_items.module.id,
            impl_id,
        )))
    }
}

pub fn default_trait() -> Trait {
    let var_ty = Type::variable_id(0);
    Trait::new_with_self_input_type(
        "Default",
        "A type with a default value.",
        [],
        [(
            "default",
            Def::new_infer_quantifiers(
                FnType::new_by_val([], var_ty, EffType::empty()),
                [],
                "Returns the default value for this type.",
            ),
        )],
    )
    .with_derivers(vec![
        b(EnumDefaultDeriver) as Box<dyn Deriver>,
        b(ProductValueDeriver) as Box<dyn Deriver>,
    ])
}

pub fn add_to_module(to: &mut Module) {
    to.add_trait(default_trait());
}
