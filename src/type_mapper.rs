// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    effects::EffType, mutability::MutType, r#type::Type, type_inference::InstSubstitution,
};

/// A struct that can map a type and its effects to another type and effects
pub trait TypeMapper {
    fn map_type(&mut self, ty: Type) -> Type;
    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType;
    fn map_effect_type(&mut self, eff_ty: &EffType) -> EffType;
}

/// Map a type using the given substitution
pub(crate) struct SubstitutionTypeMapper<'a> {
    pub(crate) subst: &'a InstSubstitution,
}
impl TypeMapper for SubstitutionTypeMapper<'_> {
    fn map_type(&mut self, ty: Type) -> Type {
        if ty.data().is_variable() {
            let var = *ty.data().as_variable().unwrap();
            match self.subst.0.get(&var) {
                Some(ty) => *ty,
                None => Type::variable(var),
            }
        } else {
            ty
        }
    }
    fn map_mut_type(&mut self, ty: MutType) -> MutType {
        ty
    }
    fn map_effect_type(&mut self, effects: &EffType) -> EffType {
        effects.instantiate(&self.subst.1)
    }
}
