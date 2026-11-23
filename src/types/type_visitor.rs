// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::iter::once;

use itertools::Itertools;

use crate::{
    FxHashSet,
    types::{
        effects::{EffType, EffectVar},
        mutability::{MutType, MutVar},
        r#type::{Type, TypeKind, TypeVar},
        type_like::TypeLike,
    },
};

/// Allow for multiple TypeKind traversal strategies
pub trait TypeInnerVisitor {
    /// Called on each type that the walk reaches, which goes into the type only if this returns
    /// true. A walk that only stops at cycles goes through a member of a recursive type once per
    /// path to it, and these paths can be exponentially many: see `OncePerType`, and a visitor
    /// that needs only whether some variables occur reads them from the type's summary.
    fn enter_type(&mut self, _ty: Type) -> bool {
        true
    }
    fn visit_ty_kind_start(&mut self, _ty: &TypeKind) {}
    fn visit_ty_kind_end(&mut self, _ty: &TypeKind) {}
    fn visit_mut_ty(&mut self, _mut_ty: MutType) {}
    fn visit_eff_ty(&mut self, _ef_ty: &EffType) {}
}

/// Walks with a visitor, going into each member of a recursive type once. For a visitor that
/// learns nothing new from a type it has already visited, such as one collecting a set, this
/// bounds the walk by the size of the type, whereas a walk that only stops at cycles goes through
/// a member of a recursive type once per path to it. Other types are entered at each occurrence,
/// which the size limit bounds.
pub(crate) struct OncePerType<V> {
    pub(crate) visitor: V,
    entered: FxHashSet<Type>,
}

impl<V> OncePerType<V> {
    pub(crate) fn new(visitor: V) -> Self {
        Self {
            visitor,
            entered: FxHashSet::default(),
        }
    }
}

impl<V: TypeInnerVisitor> TypeInnerVisitor for OncePerType<V> {
    fn enter_type(&mut self, ty: Type) -> bool {
        (!ty.is_global_recursive() || self.entered.insert(ty)) && self.visitor.enter_type(ty)
    }
    fn visit_ty_kind_start(&mut self, ty: &TypeKind) {
        self.visitor.visit_ty_kind_start(ty);
    }
    fn visit_ty_kind_end(&mut self, ty: &TypeKind) {
        self.visitor.visit_ty_kind_end(ty);
    }
    fn visit_mut_ty(&mut self, mut_ty: MutType) {
        self.visitor.visit_mut_ty(mut_ty);
    }
    fn visit_eff_ty(&mut self, eff_ty: &EffType) {
        self.visitor.visit_eff_ty(eff_ty);
    }
}

/// Collect inner type variables from a type
pub(crate) struct TyVarsCollector<'a, C: Extend<TypeVar>>(pub(crate) &'a mut C);
impl<C: Extend<TypeVar>> TypeInnerVisitor for TyVarsCollector<'_, C> {
    fn visit_ty_kind_end(&mut self, ty: &TypeKind) {
        if let Some(var) = ty.as_variable() {
            self.0.extend(once(*var));
        }
    }
}

/// Collect all type variables from a list of types
pub fn collect_ty_vars(tys: &[impl TypeLike]) -> Vec<TypeVar> {
    let mut vars = Vec::new();
    let mut collector = OncePerType::new(TyVarsCollector(&mut vars));
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
            self.0.extend(once(*var));
        }
    }
}

/// Collect all mutability variables from a list of types
#[allow(dead_code)]
pub fn collect_mut_vars(tys: &[impl TypeLike]) -> Vec<MutVar> {
    let mut vars = Vec::new();
    let mut collector = OncePerType::new(MutVarsCollector(&mut vars));
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
            .extend(ty.iter().filter_map(|effect| effect.as_variable().copied()));
    }
}

/// Collect all effect variables from a list of types
#[allow(dead_code)]
pub fn collect_effect_vars(tys: &[impl TypeLike]) -> Vec<EffectVar> {
    let mut vars = Vec::new();
    let mut collector = OncePerType::new(EffectVarsCollector(&mut vars));
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
            self.ty_vars.extend(once(*var));
        }
    }
    fn visit_mut_ty(&mut self, mut_ty: MutType) {
        if let Some(var) = mut_ty.as_variable() {
            self.mut_vars.extend(once(*var));
        }
    }
    fn visit_eff_ty(&mut self, ty: &EffType) {
        self.effect_vars
            .extend(ty.iter().filter_map(|effect| effect.as_variable().copied()));
    }
}

/// Returns whether the type contains any of the given type variables
pub(crate) struct ContainsAnyTyVars<'a> {
    pub(crate) vars: &'a [TypeVar],
    pub(crate) found: bool,
}
impl TypeInnerVisitor for ContainsAnyTyVars<'_> {
    fn enter_type(&mut self, ty: Type) -> bool {
        if !self.found {
            let summary = ty.summary();
            self.found = self
                .vars
                .iter()
                .any(|var| summary.free_ty_vars.contains(*var));
        }
        false
    }
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
    fn enter_type(&mut self, ty: Type) -> bool {
        self.all_in &= ty
            .summary()
            .free_ty_vars
            .iter()
            .all(|var| self.vars.contains(&var));
        false
    }
    fn visit_ty_kind_end(&mut self, ty: &TypeKind) {
        if let Some(var) = ty.as_variable() {
            self.all_in &= self.vars.contains(var);
        }
    }
}
