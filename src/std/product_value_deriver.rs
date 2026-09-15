// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use crate::{
    Location,
    compiler::error::InternalCompilationError,
    containers::SVec2,
    hir::{self, NodeArena, NodeId, value_dispatch::trait_apply_generated_with_locals},
    module::{LocalDecl, PendingFunctionBody, TraitId, TraitImplId},
    types::effects::EffType,
    types::r#trait::{Deriver, TraitMethodIndex},
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
        trait_id: TraitId,
        input_types: &[Type],
        span: Location,
        arena: &mut NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        use hir::hir_syn::*;

        // Validate the trait shape.
        let trait_def = solver.trait_def(trait_id);
        assert!(trait_def.input_type_count() == 1);
        assert!(trait_def.output_type_count() == 0);
        assert!(trait_def.constraints.is_empty());
        assert!(trait_def.methods.len() == 1);
        let constructor = &trait_def.methods[0].1;
        assert!(constructor.ty_scheme.constraints.is_empty());
        assert!(constructor.ty_scheme.ty.args.is_empty());
        assert!(constructor.ty_scheme.ty.ret == Type::variable_id(0));
        assert!(constructor.ty_scheme.ty.effects.is_empty());

        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

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

        let mut build_member_value =
            |arena: &mut NodeArena, locals: &mut Vec<LocalDecl>, member_ty| {
                solver.solve_impl_method(
                    trait_id,
                    &[member_ty],
                    TraitMethodIndex::new(0),
                    span,
                    arena,
                )?;
                trait_apply_generated_with_locals(
                    arena,
                    locals,
                    solver,
                    trait_id,
                    vec![member_ty],
                    TraitMethodIndex::new(0),
                    std::iter::empty(),
                    span,
                )
            };

        let ty_data = ty.data();
        use TypeKind::*;
        let root = match &*ty_data {
            Tuple(member_tys) => {
                let member_tys = member_tys.clone();
                drop(ty_data);
                let members = member_tys
                    .into_iter()
                    .map(|member_ty| build_member_value(&mut body_arena, &mut locals, member_ty))
                    .collect::<Result<SVec2<_>, _>>()?;
                Some(n(&mut body_arena, tuple(members), ty))
            }
            Record(fields) => {
                let fields = fields.clone();
                drop(ty_data);
                let members = fields
                    .into_iter()
                    .map(|(_, member_ty)| {
                        build_member_value(&mut body_arena, &mut locals, member_ty)
                    })
                    .collect::<Result<SVec2<_>, _>>()?;
                Some(n(&mut body_arena, record(members), ty))
            }
            Named(named) => {
                let named = named.clone();
                drop(ty_data);
                return Ok(Some(
                    solver.solve_impl(
                        trait_id,
                        &[solver
                            .type_def(named.def)
                            .instantiated_shape_with_effects(&named.params, &named.effect_params)],
                        span,
                        arena,
                    )?,
                ));
            }
            _ => {
                drop(ty_data);
                None
            }
        };

        Ok(root.map(|root| {
            let impl_id = solver.add_concrete_impl_from_code(
                PendingFunctionBody::new(body_arena, root),
                locals,
                trait_id,
                input_types,
                [],
            );
            TraitImplId::new(solver.current_type_items.module.id, impl_id)
        }))
    }
}
