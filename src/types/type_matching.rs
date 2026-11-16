// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! One-way matching of types without effects, as identifies dictionaries and their applications.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::types::{
    effects::EffType,
    mutability::MutType,
    r#type::{Type, TypeKind, TypeVar},
    type_like::TypeLike,
    type_mapper::TypeMapper,
};

/// `ty` with every effect erased, the form in which types identify dictionaries: effects never
/// select an implementation.
pub(crate) fn erase_type_effects(ty: Type) -> Type {
    ty.map(&mut EraseEffectsMapper)
}

struct EraseEffectsMapper;

impl TypeMapper for EraseEffectsMapper {
    fn map_type(&mut self, ty: Type) -> Type {
        ty
    }

    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
        mut_ty
    }

    fn map_effect_type(&mut self, _eff_ty: &EffType) -> EffType {
        EffType::empty()
    }
}

/// Binds the type variables of `pattern` so that it becomes `ty`, if it can. Both are without
/// effects, so function types match by their arguments and result. A variable already bound must
/// be bound to `ty` again.
pub(crate) fn match_erased_type(
    pattern: Type,
    ty: Type,
    bindings: &mut FxHashMap<TypeVar, Type>,
) -> bool {
    match_from(pattern, ty, bindings, &mut FxHashSet::default())
}

/// `visited` holds the pairs already entered: a recursive type leads back to them, and they bind
/// nothing more the second time.
fn match_from(
    pattern: Type,
    ty: Type,
    bindings: &mut FxHashMap<TypeVar, Type>,
    visited: &mut FxHashSet<(Type, Type)>,
) -> bool {
    if pattern == ty || !visited.insert((pattern, ty)) {
        return true;
    }
    let pairs: Vec<(Type, Type)> = match (&*pattern.data(), &*ty.data()) {
        (TypeKind::Variable(variable), _) => {
            return *bindings.entry(*variable).or_insert(ty) == ty;
        }
        (TypeKind::Native(pattern), TypeKind::Native(native))
            if pattern.bare_ty == native.bare_ty
                && pattern.arguments.len() == native.arguments.len() =>
        {
            zip(&pattern.arguments, &native.arguments)
        }
        (TypeKind::Tuple(patterns), TypeKind::Tuple(tys)) if patterns.len() == tys.len() => {
            zip(patterns, tys)
        }
        (TypeKind::Record(patterns), TypeKind::Record(tys))
        | (TypeKind::Variant(patterns), TypeKind::Variant(tys))
            if patterns.len() == tys.len()
                && patterns
                    .iter()
                    .zip(tys)
                    .all(|(pattern, ty)| pattern.0 == ty.0) =>
        {
            patterns
                .iter()
                .zip(tys)
                .map(|(pattern, ty)| (pattern.1, ty.1))
                .collect()
        }
        (TypeKind::Function(pattern), TypeKind::Function(function))
            if pattern.args.len() == function.args.len() =>
        {
            pattern
                .args
                .iter()
                .zip(&function.args)
                .map(|(pattern, arg)| (pattern.ty, arg.ty))
                .chain([(pattern.ret, function.ret)])
                .collect()
        }
        (TypeKind::Named(pattern), TypeKind::Named(named))
            if pattern.def == named.def && pattern.params.len() == named.params.len() =>
        {
            zip(&pattern.params, &named.params)
        }
        _ => return false,
    };
    pairs
        .into_iter()
        .all(|(pattern, ty)| match_from(pattern, ty, bindings, visited))
}

fn zip(patterns: &[Type], tys: &[Type]) -> Vec<(Type, Type)> {
    patterns.iter().copied().zip(tys.iter().copied()).collect()
}
