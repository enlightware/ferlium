// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::sync::{Arc, LazyLock};

use crate::{
    Location,
    effects::EffType,
    error::InternalCompilationError,
    function::FunctionDefinition,
    ir::{self, NodeArena, NodeId},
    ir_syn,
    module::{Module, TraitImplId},
    std::product_value_deriver::add_product_value_deriver,
    r#trait::{Deriver, TraitRef},
    trait_solver::TraitSolver,
    r#type::{FnType, Type, TypeKind},
    type_like::TypeLike,
};

use FunctionDefinition as Def;

fn add_enum_default_deriver(trait_ref: &mut TraitRef) {
    Arc::get_mut(&mut trait_ref.0)
        .unwrap()
        .derives
        .push(Box::new(EnumDefaultDeriver));
}

#[derive(Debug, Clone)]
struct EnumDefaultDeriver;

impl Deriver for EnumDefaultDeriver {
    fn derive_impl(
        &self,
        trait_ref: &TraitRef,
        input_types: &[Type],
        span: Location,
        arena: &mut NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        use ir_syn::*;

        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

        let ty_data = ty.data();
        let TypeKind::Named(named) = &*ty_data else {
            return Ok(None);
        };
        let named = named.clone();
        drop(ty_data);
        let Some(default_variant) = named.def.default_variant else {
            return Ok(None);
        };

        let shape = named.instantiated_shape();
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

        let n = |arena: &mut NodeArena, kind: ir::NodeKind, ty: Type| -> NodeId {
            arena.alloc(ir::Node::new(
                kind,
                ty,
                EffType::empty(),
                Location::new_synthesized(),
            ))
        };

        let root = if payload_ty == Type::unit() {
            n(arena, unit_variant(default_variant), ty)
        } else {
            let function = solver.solve_impl_method(trait_ref, &[payload_ty], 0, span, arena)?;
            let payload = n(
                arena,
                static_apply_pure(function, std::iter::empty(), payload_ty, span),
                payload_ty,
            );
            n(arena, variant(default_variant, payload), ty)
        };

        Ok(Some(TraitImplId::Local(
            solver.add_concrete_impl_from_code(root, vec![], trait_ref, input_types, []),
        )))
    }
}

pub static DEFAULT_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    let var_ty = Type::variable_id(0);
    let mut trait_ref = TraitRef::new_with_self_input_type(
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
    );
    add_enum_default_deriver(&mut trait_ref);
    add_product_value_deriver(&mut trait_ref);
    trait_ref
});

pub fn add_to_module(to: &mut Module) {
    to.add_trait(DEFAULT_TRAIT.clone());
}
