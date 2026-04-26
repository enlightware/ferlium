// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::sync::LazyLock;

use crate::{
    Location,
    compiler::error::InternalCompilationError,
    hir::function::FunctionDefinition,
    hir::value::{LiteralValue, ustr_to_isize},
    hir::{self, NodeArena, NodeId},
    module::{self, LocalDecl, LocalDeclId, Module, TraitImplId, id::Id},
    std::{
        STD_MODULE_ID, hash::hasher_type, logic::bool_type, math::int_type, string::string_type,
    },
    types::effects::EffType,
    types::mutability::{MutType, MutVal},
    types::r#trait::{Deriver, TraitRef},
    types::trait_solver::TraitSolver,
    types::r#type::{FnArgType, FnType, Type, TypeKind},
    types::type_like::TypeLike,
};

pub(crate) fn equal<T>(lhs: T, rhs: T) -> bool
where
    T: std::cmp::Eq,
{
    lhs == rhs
}

const VALUE_EQ_METHOD_INDEX: usize = 0;
const VALUE_TO_STRING_METHOD_INDEX: usize = 1;
const VALUE_HASH_METHOD_INDEX: usize = 2;

use FunctionDefinition as Def;

fn derive_value_to_string_body(
    trait_ref: &TraitRef,
    input_types: &[Type],
    span: Location,
    arena: &mut NodeArena,
    solver: &mut TraitSolver,
) -> Result<Option<(NodeId, Vec<crate::module::LocalDecl>)>, InternalCompilationError> {
    use hir::hir_syn::*;

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

    let string_push_str = solver.get_local_or_import_function(
        span,
        &module::Path::single_str("std"),
        crate::ustr("string_push_str"),
    )?;

    let string_lit = |arena: &mut NodeArena, text: &str| n(arena, native_str(text), string_type());
    let string_push_str_ty = FnType::new(
        vec![
            FnArgType::new(string_type(), MutType::mutable()),
            FnArgType::new_by_val(string_type()),
        ],
        Type::unit(),
        EffType::empty(),
    );
    let mut build_to_string = |arena: &mut NodeArena, value: NodeId, value_ty: Type| {
        let function = solver.solve_impl_method(
            trait_ref,
            &[value_ty],
            VALUE_TO_STRING_METHOD_INDEX,
            span,
            arena,
        )?;
        Ok(n(
            arena,
            static_apply_pure(function, [(value, value_ty)], string_type(), span),
            string_type(),
        ))
    };
    let build_string_block = |arena: &mut NodeArena,
                              locals: &mut Vec<crate::module::LocalDecl>,
                              initial: &str,
                              mut pieces: Vec<NodeId>| {
        let initial_value = string_lit(arena, initial);
        let next_local = locals.len();
        let (store_rendered, l_rendered_id) = store_new(
            initial_value,
            next_local,
            "rendered",
            MutVal::mutable(),
            string_type(),
            locals,
        );
        let mut statements = Vec::with_capacity(pieces.len() + 2);
        statements.push(n(arena, store_rendered, Type::unit()));
        for piece in pieces.drain(..) {
            let target = n(
                arena,
                load(l_rendered_id.as_index(), l_rendered_id),
                string_type(),
            );
            statements.push(n(
                arena,
                static_apply(
                    string_push_str,
                    string_push_str_ty.clone(),
                    [target, piece],
                    span,
                ),
                Type::unit(),
            ));
        }
        let rendered = n(
            arena,
            load(l_rendered_id.as_index(), l_rendered_id),
            string_type(),
        );
        statements.push(rendered);
        n(arena, block(statements), string_type())
    };

    let locals = vec![local("self", ty)];
    let l_self_id = LocalDeclId::from_index(0);

    let ty_data = ty.data();
    use TypeKind::*;
    let root = match &*ty_data {
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            let load_self = n(arena, load(0, l_self_id), ty);
            let mut locals = locals;
            let mut pieces = Vec::with_capacity(member_tys.len() * 2 + 1);
            for (index, member_ty) in member_tys.into_iter().enumerate() {
                if index > 0 {
                    pieces.push(string_lit(arena, ", "));
                }
                let member = n(arena, project(load_self, index), member_ty);
                let member_str = build_to_string(arena, member, member_ty)?;
                pieces.push(member_str);
            }
            pieces.push(string_lit(arena, ")"));
            Some((build_string_block(arena, &mut locals, "(", pieces), locals))
        }
        Record(fields) => {
            let fields = fields.clone();
            drop(ty_data);
            let load_self = n(arena, load(0, l_self_id), ty);
            let mut locals = locals;
            let mut pieces = Vec::with_capacity(fields.len() * 4 + 1);
            for (index, (name, member_ty)) in fields.into_iter().enumerate() {
                if index > 0 {
                    pieces.push(string_lit(arena, ", "));
                }
                pieces.push(string_lit(arena, name.as_str()));
                pieces.push(string_lit(arena, ": "));
                let member = n(arena, project(load_self, index), member_ty);
                let member_str = build_to_string(arena, member, member_ty)?;
                pieces.push(member_str);
            }
            pieces.push(string_lit(arena, " }"));
            Some((build_string_block(arena, &mut locals, "{ ", pieces), locals))
        }
        Variant(variants) => {
            let variants = variants.clone();
            drop(ty_data);
            let self_value = n(arena, load(0, l_self_id), ty);
            let self_tag = n(arena, extract_tag(self_value), int_type());
            let mut locals = locals;
            let mut alternatives = Vec::with_capacity(variants.len());
            for (tag, payload_ty) in variants {
                let tag_val = LiteralValue::new_native(ustr_to_isize(tag));
                let rendered = if payload_ty == Type::unit() {
                    string_lit(arena, tag.as_str())
                } else {
                    let self_value = n(arena, load(0, l_self_id), ty);
                    let payload = n(arena, project(self_value, 0), payload_ty);
                    let payload_str = build_to_string(arena, payload, payload_ty)?;
                    if payload_ty.data().is_tuple() {
                        build_string_block(
                            arena,
                            &mut locals,
                            &format!("{} ", tag),
                            vec![payload_str],
                        )
                    } else {
                        let close = string_lit(arena, ")");
                        build_string_block(
                            arena,
                            &mut locals,
                            &format!("{}(", tag),
                            vec![payload_str, close],
                        )
                    }
                };
                alternatives.push((tag_val, rendered));
            }
            let default = string_lit(arena, "");
            Some((
                n(arena, case(self_tag, alternatives, default), string_type()),
                locals,
            ))
        }
        Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let shape_ty = named.instantiated_shape();
            let load_self = n(arena, load(0, l_self_id), shape_ty);
            let payload_str = build_to_string(arena, load_self, shape_ty)?;
            let mut locals = locals;
            let separator = if named.def.is_enum() { "::" } else { " " };
            Some((
                build_string_block(
                    arena,
                    &mut locals,
                    &format!("{}{}", named.def.name, separator),
                    vec![payload_str],
                ),
                locals,
            ))
        }
        _ => {
            drop(ty_data);
            None
        }
    };

    Ok(root)
}

fn derive_value_eq_body(
    trait_ref: &TraitRef,
    input_types: &[Type],
    span: Location,
    arena: &mut NodeArena,
    solver: &mut TraitSolver,
) -> Result<Option<(NodeId, Vec<crate::module::LocalDecl>)>, InternalCompilationError> {
    use hir::hir_syn::*;

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

    let bool_ty = bool_type();
    let locals = vec![local("left", ty), local("right", ty)];
    let l_left_id = LocalDeclId::from_index(0);
    let l_right_id = LocalDeclId::from_index(1);

    let build_product_eq = |arena: &mut NodeArena,
                            solver: &mut TraitSolver,
                            member_tys: Vec<Type>|
     -> Result<NodeId, InternalCompilationError> {
        let mut eq_pairs: Vec<NodeId> = Vec::new();
        for (index, member_ty) in member_tys.into_iter().enumerate() {
            let load_left_i = n(arena, load(0, l_left_id), ty);
            let left_i = n(arena, project(load_left_i, index), member_ty);
            let load_right_i = n(arena, load(1, l_right_id), ty);
            let right_i = n(arena, project(load_right_i, index), member_ty);
            let function = solver.solve_impl_method(
                trait_ref,
                &[member_ty],
                VALUE_EQ_METHOD_INDEX,
                span,
                arena,
            )?;
            let eq_i = n(
                arena,
                static_apply_pure(
                    function,
                    [(left_i, member_ty), (right_i, member_ty)],
                    bool_ty,
                    span,
                ),
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

            let mut alternatives: Vec<(LiteralValue, NodeId)> = Vec::new();
            for (tag, payload_ty) in variants {
                let tag_val = LiteralValue::new_native(ustr_to_isize(tag));
                let load_right_outer = n(arena, load(1, l_right_id), ty);
                let right_tag = n(arena, extract_tag(load_right_outer), int_type());
                let inner_body = if payload_ty == Type::unit() {
                    n(arena, native(true), bool_ty)
                } else {
                    let load_left_v = n(arena, load(0, l_left_id), ty);
                    let left_payload = n(arena, project(load_left_v, 0), payload_ty);
                    let load_right_v = n(arena, load(1, l_right_id), ty);
                    let right_payload = n(arena, project(load_right_v, 0), payload_ty);
                    let function = solver.solve_impl_method(
                        trait_ref,
                        &[payload_ty],
                        VALUE_EQ_METHOD_INDEX,
                        span,
                        arena,
                    )?;
                    n(
                        arena,
                        static_apply_pure(
                            function,
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
            let shape_ty = named.instantiated_shape();
            let load_left = n(arena, load(0, l_left_id), shape_ty);
            let load_right = n(arena, load(1, l_right_id), shape_ty);
            let function = solver.solve_impl_method(
                trait_ref,
                &[shape_ty],
                VALUE_EQ_METHOD_INDEX,
                span,
                arena,
            )?;
            Some(n(
                arena,
                static_apply_pure(
                    function,
                    [(load_left, shape_ty), (load_right, shape_ty)],
                    bool_ty,
                    span,
                ),
                bool_ty,
            ))
        }
        _ => {
            drop(ty_data);
            None
        }
    };

    Ok(root.map(|root| (root, locals)))
}

fn derive_value_hash_body(
    trait_ref: &TraitRef,
    input_types: &[Type],
    span: Location,
    arena: &mut NodeArena,
    solver: &mut TraitSolver,
) -> Result<Option<(NodeId, Vec<LocalDecl>)>, InternalCompilationError> {
    use hir::hir_syn::*;

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

    let unit_ty = Type::unit();
    let hasher_ty = hasher_type();
    let hasher_write_string = solver.get_local_or_import_function(
        span,
        &module::Path::single_str("std"),
        crate::ustr("hasher_write_string"),
    )?;

    let locals = vec![
        local("self", ty),
        LocalDecl::new(
            (crate::ustr("state"), Location::new_synthesized()),
            MutType::mutable(),
            hasher_ty,
            None,
            Location::new_synthesized(),
        ),
    ];
    let l_self_id = LocalDeclId::from_index(0);
    let l_state_id = LocalDeclId::from_index(1);

    let value_hash_fn_ty = |value_ty| {
        FnType::new(
            vec![
                FnArgType::new_by_val(value_ty),
                FnArgType::new(hasher_ty, MutType::mutable()),
            ],
            unit_ty,
            EffType::empty(),
        )
    };
    let hasher_write_string_ty = FnType::new(
        vec![
            FnArgType::new(hasher_ty, MutType::mutable()),
            FnArgType::new_by_val(string_type()),
        ],
        unit_ty,
        EffType::empty(),
    );

    let build_write_string = |arena: &mut NodeArena, value: &str| {
        let state = n(arena, load(1, l_state_id), hasher_ty);
        let value = n(arena, native_str(value), string_type());
        n(
            arena,
            static_apply(
                hasher_write_string,
                hasher_write_string_ty.clone(),
                [state, value],
                span,
            ),
            unit_ty,
        )
    };
    let mut build_hash_value = |arena: &mut NodeArena,
                                value: NodeId,
                                value_ty: Type|
     -> Result<NodeId, InternalCompilationError> {
        let function = solver.solve_impl_method(
            trait_ref,
            &[value_ty],
            VALUE_HASH_METHOD_INDEX,
            span,
            arena,
        )?;
        let state = n(arena, load(1, l_state_id), hasher_ty);
        Ok(n(
            arena,
            static_apply(function, value_hash_fn_ty(value_ty), [value, state], span),
            unit_ty,
        ))
    };

    let ty_data = ty.data();
    use TypeKind::*;
    let root = match &*ty_data {
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            let load_self = n(arena, load(0, l_self_id), ty);
            let mut statements = Vec::with_capacity(member_tys.len() + 1);
            for (index, member_ty) in member_tys.into_iter().enumerate() {
                let member = n(arena, project(load_self, index), member_ty);
                statements.push(build_hash_value(arena, member, member_ty)?);
            }
            statements.push(n(arena, native(()), unit_ty));
            Some((n(arena, block(statements), unit_ty), locals))
        }
        Record(fields) => {
            let fields = fields.clone();
            drop(ty_data);
            let load_self = n(arena, load(0, l_self_id), ty);
            let mut statements = Vec::with_capacity(fields.len() + 1);
            for (index, (_, member_ty)) in fields.into_iter().enumerate() {
                let member = n(arena, project(load_self, index), member_ty);
                statements.push(build_hash_value(arena, member, member_ty)?);
            }
            statements.push(n(arena, native(()), unit_ty));
            Some((n(arena, block(statements), unit_ty), locals))
        }
        Variant(variants) => {
            let variants = variants.clone();
            drop(ty_data);

            let self_value = n(arena, load(0, l_self_id), ty);
            let self_tag = n(arena, extract_tag(self_value), int_type());
            let mut alternatives = Vec::with_capacity(variants.len());

            for (tag, payload_ty) in variants.into_iter() {
                let tag_val = LiteralValue::new_native(ustr_to_isize(tag));
                let mut statements = vec![build_write_string(arena, tag.as_str())];
                if payload_ty != Type::unit() {
                    let self_value = n(arena, load(0, l_self_id), ty);
                    let payload = n(arena, project(self_value, 0), payload_ty);
                    statements.push(build_hash_value(arena, payload, payload_ty)?);
                }
                statements.push(n(arena, native(()), unit_ty));
                let branch = n(arena, block(statements), unit_ty);
                alternatives.push((tag_val, branch));
            }

            let default = n(arena, native(()), unit_ty);
            Some((
                n(arena, case(self_tag, alternatives, default), unit_ty),
                locals,
            ))
        }
        Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let shape_ty = named.instantiated_shape();
            let load_self = n(arena, load(0, l_self_id), shape_ty);
            Some((build_hash_value(arena, load_self, shape_ty)?, locals))
        }
        _ => {
            drop(ty_data);
            None
        }
    };

    Ok(root)
}

fn derive_structural_value_impl(
    trait_ref: &TraitRef,
    input_types: &[Type],
    span: Location,
    arena: &mut NodeArena,
    solver: &mut TraitSolver,
) -> Result<Option<TraitImplId>, InternalCompilationError> {
    let Some((eq_root, eq_locals)) =
        derive_value_eq_body(trait_ref, input_types, span, arena, solver)?
    else {
        return Ok(None);
    };
    let Some((to_string_root, to_string_locals)) =
        derive_value_to_string_body(trait_ref, input_types, span, arena, solver)?
    else {
        return Ok(None);
    };
    let Some((hash_root, hash_locals)) =
        derive_value_hash_body(trait_ref, input_types, span, arena, solver)?
    else {
        return Ok(None);
    };
    Ok(Some(TraitImplId::Local(
        solver.add_concrete_impl_from_code_entries(
            [
                (eq_root, eq_locals),
                (to_string_root, to_string_locals),
                (hash_root, hash_locals),
            ],
            trait_ref,
            input_types,
            [],
        ),
    )))
}

/// A deriver for the `Value` trait that auto-derives the full impl for algebraic types.
#[derive(Debug, Clone)]
struct ValueDeriver;

impl Deriver for ValueDeriver {
    fn derive_impl(
        &self,
        trait_ref: &TraitRef,
        input_types: &[Type],
        span: Location,
        arena: &mut NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

        derive_structural_value_impl(trait_ref, input_types, span, arena, solver)
    }
}

pub static VALUE_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    let var_ty = Type::variable_id(0);
    let binary_fn_ty = FnType::new_by_val([var_ty, var_ty], bool_type(), EffType::empty());
    let unary_to_string_ty = FnType::new_by_val([var_ty], string_type(), EffType::empty());
    let binary_hash_ty = FnType::new(
        vec![
            FnArgType::new_by_val(var_ty),
            FnArgType::new(hasher_type(), MutType::mutable()),
        ],
        Type::unit(),
        EffType::empty(),
    );
    let trait_ref = TraitRef::new_with_self_input_type(
        "Value",
        "A type that supports semantic equality, string conversion, and hashing.",
        [],
        [
            (
                "eq",
                Def::new_infer_quantifiers(
                    binary_fn_ty,
                    ["left", "right"],
                    "Returns whether `left` equals `right`.",
                ),
            ),
            (
                "to_string",
                Def::new_infer_quantifiers(
                    unary_to_string_ty,
                    ["value"],
                    "Returns the string representation of `value`.",
                ),
            ),
            (
                "hash",
                Def::new_infer_quantifiers(
                    binary_hash_ty,
                    ["value", "state"],
                    "Writes the hash of `value` into `state`.",
                ),
            ),
        ],
    );
    trait_ref.with_module_id_and_deriver(STD_MODULE_ID, ValueDeriver)
});

pub fn add_to_module(to: &mut Module) {
    to.add_trait(VALUE_TRAIT.clone());
}
