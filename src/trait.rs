// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    hash::{Hash, Hasher},
    num::NonZero,
    ops::Deref,
    rc::Rc,
};

use ustr::ustr;
use ustr::Ustr;

use crate::{
    containers::iterable_to_string,
    function::FunctionDefinition,
    r#type::{FnType, Type},
    value::Value,
};

/// A trait, equivalent to a multi-parameter type class in Haskell, with output types.
#[derive(Debug, Clone)]
pub struct Trait {
    /// Name of the trait, for debugging purposes.
    pub name: Ustr,
    /// Number of input types, by convention, the first type variables correspond to input types.
    pub input_type_count: NonZero<u32>,
    /// Number of output types, by convention, the type variables just after input types correspond to output types.
    pub output_type_count: u32,
    /// The functions provided by the trait.
    pub functions: Vec<(Ustr, FunctionDefinition)>,
    // TODO: add spans once traits can be defined in user code.
}

impl Trait {
    /// Validate the trait, ensuring that its function signatures adhere to the limitations of the current implementation.
    pub fn validate(&self) {
        let trait_type_count = self.input_type_count.get() + self.output_type_count;
        for (name, function) in &self.functions {
            for quantifier in &function.ty_scheme.ty_quantifiers {
                if quantifier.name() >= trait_type_count {
                    panic!("Generic trait functions are not supported yet, but function {} of trait {} has a quantifier {}.", name, self.name, quantifier);
                }
            }
            if !function.ty_scheme.eff_quantifiers.is_empty() {
                panic!("Generic effects are not supported in trait functions yet, but function {} of trait {} has generic effects {}.", name, self.name, iterable_to_string(&function.ty_scheme.eff_quantifiers, ", "));
            }
            if !function.ty_scheme.constraints.is_empty() {
                panic!("Generic constraints are not supported in trait functions yet, but function {} of trait {} has {} generic constraints.", name, self.name, function.ty_scheme.constraints.len());
            }
        }
    }

    /// Return the input types for this trait given the argument and return types for a function implementing this trait.
    pub fn io_types_given_fn(&self, index: usize, fn_ty: &FnType) -> (Vec<Type>, Vec<Type>) {
        let input_type_count = self.input_type_count.get();
        let mut input_tys = vec![Type::never(); input_type_count as usize];
        let mut output_tys = vec![Type::never(); self.output_type_count as usize];
        let definition = &self.functions[index].1;
        let mut store_ty_if_match = |in_fn_ty, trait_fn_ty: Type| {
            if let Some(ty_var) = trait_fn_ty.data().as_variable() {
                let ty_var = ty_var.name();
                if ty_var < input_type_count {
                    input_tys[ty_var as usize] = in_fn_ty;
                } else if ty_var < input_type_count + self.output_type_count {
                    output_tys[(ty_var - input_type_count) as usize] = in_fn_ty;
                }
            }
        };
        for (in_fn_ty, trait_fn_ty) in fn_ty.args_ty().zip(definition.ty_scheme.ty.args_ty()) {
            store_ty_if_match(in_fn_ty, trait_fn_ty);
        }
        store_ty_if_match(fn_ty.ret, definition.ty_scheme.ty.ret);
        assert!(
            input_tys.iter().copied().all(|ty| ty != Type::never()),
            "Broken trait: not all input types were present in function {index} of trait {}",
            self.name
        );
        if output_tys.iter().copied().all(|ty| ty == Type::never()) {
            output_tys.clear();
        }
        assert!(
            !output_tys.iter().copied().any(|ty| ty == Type::never()),
            "Broken trait: only some output types were present in function {index} of trait {}, {}",
            self.name,
            output_tys.len()
        );
        (input_tys, output_tys)
    }
}

#[derive(Debug, Clone)]
pub struct TraitRef(Rc<Trait>);

impl TraitRef {
    pub fn new<'a>(
        name: &str,
        input_type_count: u32,
        output_type_count: u32,
        functions: impl Into<Vec<(&'a str, FunctionDefinition)>>,
    ) -> Self {
        let functions = functions
            .into()
            .into_iter()
            .map(|(name, def)| (ustr(name), def))
            .collect();
        let trait_data = Trait {
            name: ustr(name),
            input_type_count: NonZero::new(input_type_count).unwrap(),
            output_type_count,
            functions,
        };
        trait_data.validate();
        Self(Rc::new(trait_data))
    }
}

impl Deref for TraitRef {
    type Target = Trait;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl PartialEq for TraitRef {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for TraitRef {}

impl Hash for TraitRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(Rc::as_ptr(&self.0), state)
    }
}

/// An implementation of a trait.
/// For now, only support non-generic types and functions in trait implementation.
/// This will be relaxed later.
#[derive(Debug, Clone)]
pub struct TraitImpl {
    /// The output types of the trait.
    pub output_tys: Vec<Type>,
    /// The implemented methods, in a tuple of first-class functions of the proper types.
    /// We use a tuple to simply clone it when filling the dictionary entries.
    pub functions: Value,
}

#[cfg(test)]
mod tests {
    use std::vec;

    use crate::{
        effects::EffType,
        std::{
            math::{float_type, int_type},
            string::string_type,
        },
    };

    use super::*;

    fn trait_add() -> TraitRef {
        let fn_ty = FnType::new_by_val(
            &[Type::variable_id(0), Type::variable_id(1)],
            Type::variable_id(2),
            EffType::empty(),
        );
        TraitRef::new(
            "Add",
            2,
            1,
            [(
                "add",
                FunctionDefinition::new_infer_quantifiers(
                    fn_ty,
                    &["lhs", "rhs"],
                    "test trait function add",
                ),
            )],
        )
    }

    #[test]
    fn trait_io_types_given_fn() {
        let my_fn_ty =
            FnType::new_by_val(&[int_type(), string_type()], float_type(), EffType::empty());
        let (input_tys, output_tys) = trait_add().io_types_given_fn(0, &my_fn_ty);
        assert_eq!(input_tys, vec![int_type(), string_type()]);
        assert_eq!(output_tys, vec![float_type()]);
    }
}
