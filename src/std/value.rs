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
    module::{LocalDeclId, Module, TraitImplId, id::Id},
    std::{STD_MODULE_ID, logic::bool_type, math::int_type},
    r#trait::{Deriver, TraitRef},
    trait_solver::TraitSolver,
    r#type::{FnType, Type, TypeKind},
    type_like::TypeLike,
    value::{LiteralValue, ustr_to_isize},
};

pub(crate) fn equal<T>(lhs: T, rhs: T) -> bool
where
    T: std::cmp::Eq,
{
    lhs == rhs
}

use FunctionDefinition as Def;

fn add_value_eq_deriver(trait_ref: &mut TraitRef) {
    Arc::get_mut(&mut trait_ref.0)
        .unwrap()
        .derives
        .push(Box::new(ValueEqDeriver));
}

/// A deriver for the `Value` trait that auto-derives `eq` for algebraic types.
/// Handles product types (Tuple, Record) by pairwise element comparison,
/// and sum types (Variant) by matching on the tag then comparing payloads.
#[derive(Debug, Clone)]
struct ValueEqDeriver;

impl Deriver for ValueEqDeriver {
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

        let n = |arena: &mut NodeArena, kind: ir::NodeKind, ty: Type| -> NodeId {
            arena.alloc(ir::Node::new(
                kind,
                ty,
                EffType::empty(),
                Location::new_synthesized(),
            ))
        };

        let bool_ty = bool_type();
        let locals = vec![local("left", ty), local("right", ty)];
        let l_left_id = LocalDeclId::from_index(0);
        let l_right_id = LocalDeclId::from_index(1);

        // Build pairwise element eq AND-chain for product types.
        let build_product_eq = |arena: &mut NodeArena,
                                solver: &mut TraitSolver,
                                member_tys: Vec<Type>|
         -> Result<NodeId, InternalCompilationError> {
            let mut eq_pairs: Vec<NodeId> = Vec::new();
            for (i, ty_i) in member_tys.into_iter().enumerate() {
                let load_left_i = n(arena, load(0, l_left_id), ty);
                let left_i = n(arena, project(load_left_i, i), ty_i);
                let load_right_i = n(arena, load(1, l_right_id), ty);
                let right_i = n(arena, project(load_right_i, i), ty_i);
                let fn_id = solver.solve_impl_method(trait_ref, &[ty_i], 0, span, arena)?;
                let eq_i = n(
                    arena,
                    static_apply_pure(fn_id, [(left_i, ty_i), (right_i, ty_i)], bool_ty, span),
                    bool_ty,
                );
                eq_pairs.push(eq_i);
            }
            let mut root = n(arena, native(true), bool_ty);
            for eq_i in eq_pairs.into_iter().rev() {
                let false_n = n(arena, native(false), bool_ty);
                root = n(
                    arena,
                    case(eq_i, vec![(LiteralValue::new_native(true), root)], false_n),
                    bool_ty,
                );
            }
            Ok(root)
        };

        let ty_data = ty.data();
        use TypeKind::*;
        let root = match &*ty_data {
            Tuple(member_tys) => {
                let member_tys = member_tys.clone();
                drop(ty_data);
                Some(build_product_eq(arena, solver, member_tys)?)
            }
            Record(fields) => {
                let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
                drop(ty_data);
                Some(build_product_eq(arena, solver, member_tys)?)
            }
            Variant(variants) => {
                let variants = variants.clone();
                drop(ty_data);

                // For each left-tag branch: check if right has same tag, then compare payloads.
                let mut alternatives: Vec<(LiteralValue, NodeId)> = Vec::new();
                for (tag, payload_ty) in variants {
                    let tag_val = LiteralValue::new_native(ustr_to_isize(tag));
                    // Extract right tag for inner check
                    let load_right_outer = n(arena, load(1, l_right_id), ty);
                    let right_tag = n(arena, extract_tag(load_right_outer), int_type());
                    let inner_body = if payload_ty == Type::unit() {
                        // Unit payload: tags matching is sufficient
                        n(arena, native(true), bool_ty)
                    } else {
                        // Non-unit payload: compare payloads after confirming same tag
                        let load_left_v = n(arena, load(0, l_left_id), ty);
                        let left_payload = n(arena, project(load_left_v, 0), payload_ty);
                        let load_right_v = n(arena, load(1, l_right_id), ty);
                        let right_payload = n(arena, project(load_right_v, 0), payload_ty);
                        let fn_id =
                            solver.solve_impl_method(trait_ref, &[payload_ty], 0, span, arena)?;
                        n(
                            arena,
                            static_apply_pure(
                                fn_id,
                                [(left_payload, payload_ty), (right_payload, payload_ty)],
                                bool_ty,
                                span,
                            ),
                            bool_ty,
                        )
                    };
                    let false_imm = n(arena, native(false), bool_ty);
                    let inner_case = n(
                        arena,
                        case(right_tag, vec![(tag_val.clone(), inner_body)], false_imm),
                        bool_ty,
                    );
                    alternatives.push((tag_val, inner_case));
                }
                // Outer: dispatch on left tag
                let load_left_outer = n(arena, load(0, l_left_id), ty);
                let left_tag = n(arena, extract_tag(load_left_outer), int_type());
                let false_default = n(arena, native(false), bool_ty);
                Some(n(
                    arena,
                    case(left_tag, alternatives, false_default),
                    bool_ty,
                ))
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
                locals,
                trait_ref,
                input_types,
                [],
            ))
        }))
    }
}

pub static VALUE_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    let var_ty = Type::variable_id(0);
    let binary_fn_ty = FnType::new_by_val([var_ty, var_ty], bool_type(), EffType::empty());
    let mut trait_ref = TraitRef::new_with_self_input_type(
        "Value",
        "A type that is Equatable (and later Clonable).",
        [],
        [(
            "eq",
            Def::new_infer_quantifiers(
                binary_fn_ty,
                ["left", "right"],
                "Returns whether `left` equals `right`.",
            ),
        )],
    );
    add_value_eq_deriver(&mut trait_ref);
    trait_ref.with_module_id(STD_MODULE_ID)
});

pub fn add_to_module(to: &mut Module) {
    to.add_trait(VALUE_TRAIT.clone());
}
