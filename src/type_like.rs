// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::collections::HashSet;

use itertools::Itertools;

use crate::effects::EffectVar;
use crate::mutability::MutVar;
use crate::r#type::{Type, TypeVar};
use crate::type_inference::InstSubstitution;
use crate::type_mapper::{SubstitutionTypeMapper, TypeMapper};
use crate::type_visitor::{
    ContainsAnyTyVars, ContainsOnlyTyVars, EffectVarsCollector, MutVarsCollector, TyVarsCollector,
    TypeInnerVisitor,
};

/// Something that is a type or part of it, and that can
/// be instantiated and queried for its free type variables.
pub trait TypeLike {
    /// Visit the type and its inner components, calling the visitor for each of them
    fn visit(&self, visitor: &mut impl TypeInnerVisitor);

    /// Map the type and its inner components, calling the type mapper for each of them
    fn map(&self, f: &mut impl TypeMapper) -> Self;

    /// Instantiate the type variables within this type with the given substitutions
    fn instantiate(&self, subst: &InstSubstitution) -> Self
    where
        Self: Sized,
    {
        self.map(&mut SubstitutionTypeMapper { subst })
    }

    /// Return all type variables contained in this type
    fn inner_ty_vars(&self) -> Vec<TypeVar> {
        self.inner_ty_vars_iter().collect()
    }

    /// Return all type variables contained in this type, as an iterator
    fn inner_ty_vars_iter(&self) -> impl Iterator<Item = TypeVar> {
        let mut vars = vec![];
        self.visit(&mut TyVarsCollector(&mut vars));
        vars.into_iter().unique()
    }

    /// Return all mutability variables contained in this type
    fn inner_mut_ty_vars(&self) -> Vec<MutVar> {
        let mut vars = vec![];
        self.visit(&mut MutVarsCollector(&mut vars));
        vars.into_iter().unique().collect()
    }

    /// Return all effect variables contained as input (i.e. must be retained)
    fn fill_with_input_effect_vars(&self, vars: &mut HashSet<EffectVar>) {
        self.visit(&mut EffectVarsCollector(vars));
    }

    /// Return all effect variables contained as input (i.e. must be retained)
    fn input_effect_vars(&self) -> HashSet<EffectVar> {
        let mut vars = HashSet::new();
        self.fill_with_input_effect_vars(&mut vars);
        vars
    }

    /// Return all effect variables contained as output (i.e. can be dropped if not used as input)
    fn fill_with_output_effect_vars(&self, _vars: &mut HashSet<EffectVar>) {
        // default no output effect variables
    }

    /// Return all effect variables contained as output (i.e. can be dropped if not used as input)
    fn output_effect_vars(&self) -> HashSet<EffectVar> {
        let mut vars = HashSet::new();
        self.fill_with_output_effect_vars(&mut vars);
        vars
    }

    /// Fill the given set with all effect variables contained in this type, union of input and output ones
    fn fill_with_inner_effect_vars(&self, vars: &mut HashSet<EffectVar>) {
        self.fill_with_input_effect_vars(vars);
        self.fill_with_output_effect_vars(vars);
    }

    /// Return all effect variables contained in this type, union of input and output ones
    fn inner_effect_vars(&self) -> HashSet<EffectVar> {
        let mut vars = HashSet::new();
        self.fill_with_inner_effect_vars(&mut vars);
        vars
    }

    /// Returns whether the type contains the given type variable
    fn contains_any_type_var(&self, var: TypeVar) -> bool {
        self.contains_any_ty_vars(&[var])
    }

    /// Returns whether the type contains any of the given type variables
    fn contains_any_ty_vars(&self, vars: &[TypeVar]) -> bool {
        let mut visitor = ContainsAnyTyVars { vars, found: false };
        self.visit(&mut visitor);
        visitor.found
    }

    /// Returns whether all type variables in the type are in the given list
    fn contains_only_ty_vars(&self, vars: &[TypeVar]) -> bool {
        let mut visitor = ContainsOnlyTyVars { vars, all_in: true };
        self.visit(&mut visitor);
        visitor.all_in
    }

    /// Return true if the type does not contain any type or effect variables
    fn is_constant(&self) -> bool {
        self.inner_ty_vars().is_empty()
            && self.inner_mut_ty_vars().is_empty()
            && self.inner_effect_vars().is_empty()
    }
}

pub fn instantiate_types<T: TypeLike>(tys: &[T], subst: &InstSubstitution) -> Vec<T> {
    tys.iter().map(|ty| ty.instantiate(subst)).collect()
}

/// Something that is like a type and can be casted to a type.
pub trait CastableToType: TypeLike {
    /// Return this as a type
    fn to_type(&self) -> Type;
}
