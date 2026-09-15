// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use crate::{
    Location,
    compiler::error::InternalCompilationError,
    hir,
    hir::function::CallableDefinition,
    module::{
        LocalDeclId, Module, PendingFunctionBody, PendingLocalClone, TraitId, TraitImplId, id::Id,
    },
    types::effects::{EffType, PrimitiveEffect},
    types::r#trait::{Deriver, Trait},
    types::trait_solver::TraitSolver,
    types::r#type::{FnType, Type},
    types::type_like::TypeLike,
};
use ustr::ustr;

use CallableDefinition as Def;

#[derive(Debug, Clone)]
struct SelfCastDeriver;
impl Deriver for SelfCastDeriver {
    fn derive_impl(
        &self,
        trait_id: TraitId,
        input_types: &[Type],
        span: Location,
        _arena: &mut hir::NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        use hir::hir_syn::*;
        let from_ty = input_types[0];
        let to_ty = input_types[1];
        if from_ty != to_ty {
            return Ok(None);
        }
        if !from_ty.is_constant() {
            return Ok(None);
        }

        // Identity implementation: clone from borrowed argument storage into
        // the returned value.
        let mut body_arena = hir::NodeArena::default();
        let locals = vec![local("value", from_ty)];
        let id = LocalDeclId::from_index(0);
        let source_id = body_arena.alloc(hir::Node::new(
            load_local(id),
            from_ty,
            EffType::empty(),
            span,
        ));
        let code_id = body_arena.alloc(hir::Node::new(
            hir::NodeKind::CloneValue(hir::CloneValue {
                source: source_id,
                clone: PendingLocalClone::Unknown,
            }),
            from_ty,
            EffType::empty(),
            span,
        ));
        let local_impl_id = solver.add_concrete_impl_from_code(
            PendingFunctionBody::new(body_arena, code_id),
            locals,
            trait_id,
            input_types,
            [],
        );
        Ok(Some(TraitImplId::new(
            solver.current_type_items.module.id,
            local_impl_id,
        )))

        // TODO: optimize away the cast entirely in the compiler
        // TODO: add same-code optimization passes in module building to reduce duplications generated here
    }
}

pub fn cast_trait() -> Trait {
    let var0_ty = Type::variable_id(0);
    let var1_ty = Type::variable_id(1);
    let unary_fn_ty = FnType::new_by_val(
        [var0_ty],
        var1_ty,
        EffType::single_primitive(PrimitiveEffect::Fallible),
    );
    Trait::new(
        "Cast",
        "Conversion of a value from one type to another.",
        ["From", "To"],
        [],
        [(
            "cast",
            Def::new_infer_quantifiers(
                unary_fn_ty,
                ["value"],
                "Casts `value` to the type of `To`.",
            ),
        )],
    )
    .with_deriver(SelfCastDeriver)
}

pub fn add_to_module(to: &mut Module) {
    // Traits
    let id = to.add_trait(cast_trait());
    debug_assert_eq!(to.get_trait_id(ustr("Cast")).unwrap().index, id);
}
