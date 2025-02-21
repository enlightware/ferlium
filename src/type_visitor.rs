// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::collections::HashSet;

use crate::{
    effects::EffectVar,
    mutability::{MutType, MutVar},
    r#type::{TypeKind, TypeVar},
};

/// Allow for multiple TypeKind traversal strategies
pub trait TypeInnerVisitor {
    fn visit_ty_kind_start(&mut self, _ty: &TypeKind) {}
    fn visit_ty_kind_end(&mut self, _ty: &TypeKind) {}
    fn visit_mut_ty(&mut self, _mut_ty: MutType) {}
}

/// Collect inner mutability variables from a type
pub(crate) struct MutVarsCollector<'a>(pub(crate) &'a mut Vec<MutVar>);
impl TypeInnerVisitor for MutVarsCollector<'_> {
    fn visit_mut_ty(&mut self, mut_ty: MutType) {
        if let Some(var) = mut_ty.as_variable() {
            self.0.push(*var);
        }
    }
}

/// Collect inner type variables from a type
pub(crate) struct TyVarsCollector<'a>(pub(crate) &'a mut Vec<TypeVar>);
impl TypeInnerVisitor for TyVarsCollector<'_> {
    fn visit_ty_kind_end(&mut self, ty: &TypeKind) {
        if let Some(var) = ty.as_variable() {
            self.0.push(*var);
        }
    }
}

/// Collect inner effect variables from a type
pub(crate) struct EffectVarsCollector<'a>(pub(crate) &'a mut HashSet<EffectVar>);
impl TypeInnerVisitor for EffectVarsCollector<'_> {
    fn visit_ty_kind_end(&mut self, ty: &TypeKind) {
        if let TypeKind::Function(fn_type) = ty {
            fn_type.effects.fill_with_inner_effect_vars(self.0);
        }
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
