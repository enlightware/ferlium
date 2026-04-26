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
    containers::SVec2,
    hir::{self, NodeArena, NodeId},
    module::TraitImplId,
    types::effects::EffType,
    types::r#trait::{Deriver, TraitRef},
    types::trait_solver::TraitSolver,
    types::r#type::{Type, TypeKind},
    types::type_like::TypeLike,
};

/// A deriver for traits with a single input type, no output type,
/// and a single constructor method that returns an instance of the input type.
/// Calls recursively the method of each member of a product type and combines the results using the same constructor.
/// Useful for traits like `Default` and `Empty`.
#[derive(Debug, Clone)]
pub(crate) struct ProductValueDeriver;

impl Deriver for ProductValueDeriver {
    fn derive_impl(
        &self,
        trait_ref: &TraitRef,
        input_types: &[Type],
        span: Location,
        arena: &mut NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        use hir::hir_syn::*;

        // Validate the trait shape.
        assert!(trait_ref.input_type_count() == 1);
        assert!(trait_ref.output_type_count() == 0);
        assert!(trait_ref.constraints.is_empty());
        assert!(trait_ref.functions.len() == 1);
        let constructor = &trait_ref.functions[0].1;
        assert!(constructor.ty_scheme.constraints.is_empty());
        assert!(constructor.ty_scheme.ty.args.is_empty());
        assert!(constructor.ty_scheme.ty.ret == Type::variable_id(0));
        assert!(constructor.ty_scheme.ty.effects.is_empty());

        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

        let n = |arena: &mut NodeArena, kind: hir::NodeKind, ty: Type| -> NodeId {
            arena.alloc(hir::Node::new(
                kind,
                ty,
                EffType::empty(),
                Location::new_synthesized(),
            ))
        };

        let mut build_member_value = |arena: &mut NodeArena, member_ty| {
            let function = solver.solve_impl_method(trait_ref, &[member_ty], 0, span, arena)?;
            Ok(n(
                arena,
                static_apply_pure(function, std::iter::empty(), member_ty, span),
                member_ty,
            ))
        };

        let ty_data = ty.data();
        use TypeKind::*;
        let root = match &*ty_data {
            Tuple(member_tys) => {
                let member_tys = member_tys.clone();
                drop(ty_data);
                let members = member_tys
                    .into_iter()
                    .map(|member_ty| build_member_value(arena, member_ty))
                    .collect::<Result<SVec2<_>, _>>()?;
                Some(n(arena, tuple(members), ty))
            }
            Record(fields) => {
                let fields = fields.clone();
                drop(ty_data);
                let members = fields
                    .into_iter()
                    .map(|(_, member_ty)| build_member_value(arena, member_ty))
                    .collect::<Result<SVec2<_>, _>>()?;
                Some(n(arena, record(members), ty))
            }
            Named(named) => {
                let named = named.clone();
                drop(ty_data);
                return Ok(Some(solver.solve_impl(
                    trait_ref,
                    &[named.instantiated_shape()],
                    span,
                    arena,
                )?));
            }
            _ => {
                drop(ty_data);
                None
            }
        };

        Ok(root.map(|root| {
            TraitImplId::Local(solver.add_concrete_impl_from_code(
                root,
                vec![],
                trait_ref,
                input_types,
                [],
            ))
        }))
    }
}
