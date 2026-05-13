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
    type_inference::substitution::InstSubstitution,
    var_set::KindVarSet,
};

/// A struct that can map a type and its effects to another type and effects
pub trait TypeMapper {
    fn map_type(&mut self, ty: Type) -> Type;
    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType;
    fn map_effect_type(&mut self, eff_ty: &EffType) -> EffType;

    /// Hot-path predicate: returns `false` when the mapper cannot affect `ty`,
    /// allowing `Type::map` to skip the slow clone-walk-intern path.
    /// Default is conservative `true`.
    fn affects_type(&mut self, _ty: Type) -> bool {
        true
    }
}

/// Map a type using the given (ty_var, eff_var) substitution.
///
/// Cheap to construct (just stores a pointer), suited for one-shot calls on
/// leaf-like types (single `TypeVar`, primitive) where the mapper is queried
/// only a handful of times. For anything that walks a tree (function types,
/// constraints, instantiation across many slices) prefer
/// [`BitmapSubstitutionTypeMapper`].
#[derive(new)]
pub(crate) struct SimpleSubstitutionTypeMapper<'a> {
    pub(crate) subst: &'a InstSubstitution,
}

impl TypeMapper for SimpleSubstitutionTypeMapper<'_> {
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

/// Map a type using the given (ty_var, eff_var) substitution, with
/// pre-computed bitmaps of the substitution's domain.
///
/// The bitmaps make `affects_type` constant-time regardless of substitution
/// size, which pays off when the mapper is reused across many types (e.g.
/// HIR tree walks via `instantiate_node_with`). For one-shot or small-fanout
/// uses prefer [`SimpleSubstitutionTypeMapper`] to skip the construction cost.
pub(crate) struct BitmapSubstitutionTypeMapper<'a> {
    pub(crate) subst: &'a InstSubstitution,
    ty_var_domain: KindVarSet<TypeVar>,
    eff_var_domain: KindVarSet<EffectVar>,
}

impl<'a> BitmapSubstitutionTypeMapper<'a> {
    pub(crate) fn new(subst: &'a InstSubstitution) -> Self {
        Self {
            subst,
            ty_var_domain: KindVarSet::from_iterator(subst.0.keys().copied()),
            eff_var_domain: KindVarSet::from_iterator(subst.1.keys().copied()),
        }
    }
}

impl TypeMapper for BitmapSubstitutionTypeMapper<'_> {
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
fn map_type_via_subst(subst: &InstSubstitution, ty: Type) -> Type {
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
