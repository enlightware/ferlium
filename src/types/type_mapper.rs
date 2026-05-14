// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use derive_new::new;

use crate::types::{
    effects::{EffType, EffectVar},
    mutability::MutType,
    r#type::{Type, TypeVar},
    type_inference::substitution::InstSubst,
    var_set::KindVarSet,
};

/// Leaf-rewrite policy used by `TypeLike::map`.
///
/// `TypeMapper` is for instantiation-style rewrites of values that already know
/// how to traverse themselves. The `TypeLike` implementation owns traversal and
/// reconstruction; this trait only decides how each encountered type,
/// mutability, and effect leaf is rewritten.
///
/// This is separate from `TypeSubstituer`: it does not batch interning, track
/// local type ids, or rebuild interned type graphs explicitly.
pub trait TypeMapper {
    fn map_type(&mut self, ty: Type) -> Type;
    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType;
    fn map_effect_type(&mut self, eff_ty: &EffType) -> EffType;

    /// Returns `false` when `TypeLike::map` can return this `Type` unchanged without walking or rebuilding it.
    fn affects_type(&mut self, _ty: Type) -> bool {
        true
    }
}

/// Map a type using the given (ty_var, eff_var) instantiation substitution.
///
/// Cheap to construct (just stores a pointer), suited for one-shot calls on
/// leaf-like types (single `TypeVar`, primitive) where the mapper is queried
/// only a handful of times. For anything that walks a tree (function types,
/// constraints, instantiation across many slices) prefer
/// [`BitmapInstantiationMapper`].
#[derive(new)]
pub(crate) struct SimpleInstantiationMapper<'a> {
    pub(crate) subst: &'a InstSubst,
}

impl TypeMapper for SimpleInstantiationMapper<'_> {
    fn map_type(&mut self, ty: Type) -> Type {
        map_type_via_subst(self.subst, ty)
    }
    fn map_mut_type(&mut self, ty: MutType) -> MutType {
        ty
    }
    fn map_effect_type(&mut self, effects: &EffType) -> EffType {
        effects.instantiate(&self.subst.1)
    }
    fn affects_type(&mut self, ty: Type) -> bool {
        let summary = ty.summary();
        self.subst
            .0
            .keys()
            .any(|v| summary.free_ty_vars.contains(*v))
            || self
                .subst
                .1
                .keys()
                .any(|v| summary.free_eff_vars.contains(*v))
    }
}

/// Map a type using the given (ty_var, eff_var) instantiation substitution,
/// with pre-computed bitmaps of the substitution's domain.
///
/// The bitmaps make `affects_type` constant-time regardless of substitution
/// size, which pays off when the mapper is reused across many types (e.g.
/// HIR tree walks via `instantiate_node_in_place`). For one-shot or small-fanout
/// uses prefer [`SimpleInstantiationMapper`] to skip the construction cost.
pub(crate) struct BitmapInstantiationMapper<'a> {
    pub(crate) subst: &'a InstSubst,
    ty_var_domain: KindVarSet<TypeVar>,
    eff_var_domain: KindVarSet<EffectVar>,
}

impl<'a> BitmapInstantiationMapper<'a> {
    pub(crate) fn new(subst: &'a InstSubst) -> Self {
        Self {
            subst,
            ty_var_domain: KindVarSet::from_iterator(subst.0.keys().copied()),
            eff_var_domain: KindVarSet::from_iterator(subst.1.keys().copied()),
        }
    }
}

impl TypeMapper for BitmapInstantiationMapper<'_> {
    fn map_type(&mut self, ty: Type) -> Type {
        map_type_via_subst(self.subst, ty)
    }
    fn map_mut_type(&mut self, ty: MutType) -> MutType {
        ty
    }
    fn map_effect_type(&mut self, effects: &EffType) -> EffType {
        effects.instantiate(&self.subst.1)
    }
    fn affects_type(&mut self, ty: Type) -> bool {
        let summary = ty.summary();
        self.ty_var_domain.intersects(&summary.free_ty_vars)
            || self.eff_var_domain.intersects(&summary.free_eff_vars)
    }
}

#[inline]
fn map_type_via_subst(subst: &InstSubst, ty: Type) -> Type {
    if ty.data().is_variable() {
        let var = *ty.data().as_variable().unwrap();
        match subst.0.get(&var) {
            Some(ty) => {
                // FIXME: This should work but break existing code, probably due to the way
                // we generate substitutions post-unification.
                // ty.map(self)
                *ty
            }
            None => Type::variable(var),
        }
    } else {
        ty
    }
}
