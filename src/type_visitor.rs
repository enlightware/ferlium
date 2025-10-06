// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use itertools::Itertools;

use crate::{
    effects::{EffType, EffectVar},
    mutability::{MutType, MutVar},
    r#type::{TypeKind, TypeVar},
    type_like::TypeLike,
};

/// Allow for multiple TypeKind traversal strategies
pub trait TypeInnerVisitor {
    fn visit_ty_kind_start(&mut self, _ty: &TypeKind) {}
    fn visit_ty_kind_end(&mut self, _ty: &TypeKind) {}
    fn visit_mut_ty(&mut self, _mut_ty: MutType) {}
    fn visit_eff_ty(&mut self, _ef_ty: &EffType) {}
}

/// Collect inner type variables from a type
pub(crate) struct TyVarsCollector<'a, C: Extend<TypeVar>>(pub(crate) &'a mut C);
impl<C: Extend<TypeVar>> TypeInnerVisitor for TyVarsCollector<'_, C> {
    fn visit_ty_kind_end(&mut self, ty: &TypeKind) {
        if let Some(var) = ty.as_variable() {
            self.0.extend(std::iter::once(*var));
        }
    }
}

/// Collect all type variables from a list of types
pub fn collect_ty_vars(tys: &[impl TypeLike]) -> Vec<TypeVar> {
    let mut vars = Vec::new();
    let mut collector = TyVarsCollector(&mut vars);
    for ty in tys {
        ty.visit(&mut collector);
    }
    vars.into_iter().unique().collect()
}

/// Collect inner mutability variables from a type
pub(crate) struct MutVarsCollector<'a, C: Extend<MutVar>>(pub(crate) &'a mut C);
impl<C: Extend<MutVar>> TypeInnerVisitor for MutVarsCollector<'_, C> {
    fn visit_mut_ty(&mut self, mut_ty: MutType) {
        if let Some(var) = mut_ty.as_variable() {
            self.0.extend(std::iter::once(*var));
        }
    }
}

/// Collect all mutability variables from a list of types
#[allow(dead_code)]
pub fn collect_mut_vars(tys: &[impl TypeLike]) -> Vec<MutVar> {
    let mut vars = Vec::new();
    let mut collector = MutVarsCollector(&mut vars);
    for ty in tys {
        ty.visit(&mut collector);
    }
    vars.into_iter().unique().collect()
}

/// Collect inner effect variables from a type
pub(crate) struct EffectVarsCollector<'a, C: Extend<EffectVar>>(pub(crate) &'a mut C);
impl<C: Extend<EffectVar>> TypeInnerVisitor for EffectVarsCollector<'_, C> {
    fn visit_eff_ty(&mut self, ty: &EffType) {
        self.0
            .extend(ty.iter().filter_map(|effect| effect.as_variable()).copied());
    }
}

/// Collect all effect variables from a list of types
#[allow(dead_code)]
pub fn collect_effect_vars(tys: &[impl TypeLike]) -> Vec<EffectVar> {
    let mut vars = Vec::new();
    let mut collector = EffectVarsCollector(&mut vars);
    for ty in tys {
        ty.visit(&mut collector);
    }
    vars.into_iter().unique().collect()
}

/// Collect all type, mutability, and effect variables from a type
#[allow(dead_code)]
pub(crate) struct AllVarsCollector<'a, CT, CM, CE>
where
    CT: Extend<TypeVar>,
    CM: Extend<MutVar>,
    CE: Extend<EffectVar>,
{
    pub(crate) ty_vars: &'a mut CT,
    pub(crate) mut_vars: &'a mut CM,
    pub(crate) effect_vars: &'a mut CE,
}
impl<CT, CM, CE> TypeInnerVisitor for AllVarsCollector<'_, CT, CM, CE>
where
    CT: Extend<TypeVar>,
    CM: Extend<MutVar>,
    CE: Extend<EffectVar>,
{
    fn visit_ty_kind_end(&mut self, ty: &TypeKind) {
        if let Some(var) = ty.as_variable() {
            self.ty_vars.extend(std::iter::once(*var));
        }
    }
    fn visit_mut_ty(&mut self, mut_ty: MutType) {
        if let Some(var) = mut_ty.as_variable() {
            self.mut_vars.extend(std::iter::once(*var));
        }
    }
    fn visit_eff_ty(&mut self, ty: &EffType) {
        self.effect_vars
            .extend(ty.iter().filter_map(|effect| effect.as_variable()).copied());
    }
}

/// Returns whether the type contains any of the given type variables
pub(crate) struct ContainsAnyTyVars<'a> {
    pub(crate) vars: &'a [TypeVar],
    pub(crate) found: bool,
}
impl TypeInnerVisitor for ContainsAnyTyVars<'_> {
    fn visit_ty_kind_end(&mut self, ty: &TypeKind) {
        if self.found {
            // already found, do nothing
        } else if let Some(var) = ty.as_variable() {
            self.found |= self.vars.contains(var);
        }
    }
}

/// Returns whether all type variables in the type are in the given list
pub(crate) struct ContainsOnlyTyVars<'a> {
    pub(crate) vars: &'a [TypeVar],
    pub(crate) all_in: bool,
}
impl TypeInnerVisitor for ContainsOnlyTyVars<'_> {
    fn visit_ty_kind_end(&mut self, ty: &TypeKind) {
        if let Some(var) = ty.as_variable() {
            self.all_in &= self.vars.contains(var);
        }
    }
}
