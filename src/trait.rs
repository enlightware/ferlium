// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    collections::HashSet,
    fmt,
    fmt::Debug,
    hash::{Hash, Hasher},
    num::NonZero,
    ops::Deref,
    rc::Rc,
};

use dyn_clone::DynClone;
use ustr::ustr;
use ustr::Ustr;

use crate::{
    containers::iterable_to_string,
    error::InternalCompilationError,
    format::write_with_separator_and_format_fn,
    function::FunctionDefinition,
    module::{FmtWithModuleEnv, ModuleEnv},
    r#type::{Type, TypeVar},
    trait_solver::{ConcreteTraitImpl, TraitImpls},
    type_like::TypeLike,
    type_scheme::PubTypeConstraint,
    type_visitor::TyVarsCollector,
    Location,
};

/// Help deriving implementations of traits.
pub trait Deriver: Debug + DynClone {
    /// Derive an implementation of a trait for the given input types, if possible.
    fn derive_impl(
        &self,
        trait_ref: &TraitRef,
        input_types: &[Type],
        span: Location,
        impls: &mut TraitImpls,
    ) -> Result<Option<ConcreteTraitImpl>, InternalCompilationError>;
}

dyn_clone::clone_trait_object!(Deriver);

/// A trait, equivalent to a multi-parameter type class in Haskell, with output types.
#[derive(Debug, Clone)]
pub struct Trait {
    /// Name of the trait, for debugging purposes.
    pub name: Ustr,
    /// Number of input types, by convention, the first type variables correspond to input types.
    pub input_type_count: NonZero<u32>,
    /// Name of the output types.
    /// By convention, the type variables just after input types correspond to output types.
    pub output_type_names: Vec<Ustr>,
    /// The constraints on the trait, for example related to the associated types.
    pub constraints: Vec<PubTypeConstraint>,
    /// The functions provided by the trait.
    pub functions: Vec<(Ustr, FunctionDefinition)>,
    /// The trait derivators
    pub derives: Vec<Box<dyn Deriver>>,
    // TODO: add spans once traits can be defined in user code.
}

impl Trait {
    /// Return the number of output types in this trait.
    pub fn output_type_count(&self) -> u32 {
        self.output_type_names.len() as u32
    }

    /// Return the number of type variables in this trait.
    pub fn type_var_count(&self) -> u32 {
        self.input_type_count.get() + self.output_type_count()
    }

    /// Validate the trait, ensuring that its function signatures adhere to the limitations of the current implementation.
    pub fn validate(&self) {
        // Make sure that constraints only refer to the input or the output type variables.
        let trait_type_count = self.type_var_count();
        for constraint in &self.constraints {
            for ty_var in constraint.inner_ty_vars() {
                if ty_var.name() >= trait_type_count {
                    panic!("Invalid type variable in trait {}: {}", self.name, ty_var);
                }
            }
        }

        // Make sure that all function definitions are valid and refer to the correct type variables.
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
            for input_ty_var in 0..self.input_type_count.get() {
                let ty_var = TypeVar::new(input_ty_var);
                if !function.ty_scheme.ty_quantifiers.contains(&ty_var) {
                    panic!(
                        "Input type variable {} does appear in the quantifiers of function {} of trait {}.",
                        ty_var, name, self.name
                    );
                }
            }
            // Make sure that all constraints have their input type variables reachable from
            // the function type, in a single pass.
            // The single pass is important because in TraitImpls::get_impl()
            // we assume that we can get all output type variables in a single pass over the constraints.
            let mut quantifiers: HashSet<_> =
                function.ty_scheme.ty_quantifiers.iter().copied().collect();
            for (i, constraint) in self.constraints.iter().enumerate() {
                let (_, input_tys, output_tys, _) = constraint
                    .as_have_trait()
                    .expect("Only HaveTrait constraints are supported in traits.");
                assert!(input_tys
                    .iter()
                    .flat_map(TypeLike::inner_ty_vars)
                    .all(|ty_var| quantifiers.contains(&ty_var)), "In trait {}, constraint #{} has unreachable input type variable in function {}.", self.name, i, name);
                let mut additional_ty_vars = HashSet::new();
                let mut collector = TyVarsCollector(&mut additional_ty_vars);
                output_tys.iter().for_each(|ty| ty.visit(&mut collector));
                quantifiers.extend(additional_ty_vars);
            }
        }
    }
}

impl FmtWithModuleEnv for Trait {
    fn fmt_with_module_env(&self, f: &mut fmt::Formatter, env: &ModuleEnv) -> fmt::Result {
        write!(f, "trait {} <", self.name)?;
        let input_ty_count = self.input_type_count.get();
        write_with_separator_and_format_fn(
            0..input_ty_count,
            ", ",
            |index, f| write!(f, "{}", TypeVar::new(index)),
            f,
        )?;
        if self.output_type_count() > 0 {
            write!(f, " ↦ ")?;
            write_with_separator_and_format_fn(
                0..self.output_type_count(),
                ", ",
                |index, f| {
                    write!(
                        f,
                        "{} = {}",
                        self.output_type_names[index as usize],
                        TypeVar::new(input_ty_count + index)
                    )
                },
                f,
            )?;
        }
        if self.constraints.is_empty() {
            writeln!(f, "> {{")?;
        } else {
            writeln!(f, "> where")?;
            for constraint in &self.constraints {
                write!(f, "    ")?;
                constraint.fmt_with_module_env(f, env)?;
            }
            writeln!(f, "\n{{")?;
        }
        let mut first = true;
        for (name, def) in &self.functions {
            if first {
                first = false;
            } else {
                writeln!(f)?;
            }
            def.fmt_with_name_and_module_env(f, name, "    ", env)?;
        }
        writeln!(f, "}}")?;
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct TraitRef(pub(crate) Rc<Trait>);

impl TraitRef {
    pub fn new<'a>(
        name: &str,
        input_type_count: u32,
        output_type_names: impl Into<Vec<&'a str>>,
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
            output_type_names: output_type_names.into().into_iter().map(ustr).collect(),
            constraints: Vec::new(),
            functions,
            derives: Vec::new(),
        };
        trait_data.validate();
        Self(Rc::new(trait_data))
    }

    pub fn new_with_constraints<'a>(
        name: &str,
        input_type_count: u32,
        output_type_names: impl Into<Vec<&'a str>>,
        constraints: impl Into<Vec<PubTypeConstraint>>,
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
            output_type_names: output_type_names.into().into_iter().map(ustr).collect(),
            constraints: constraints.into(),
            functions,
            derives: Vec::new(),
        };
        trait_data.validate();
        Self(Rc::new(trait_data))
    }

    pub fn validate_impl_size(&self, input_tys: &[Type], output_tys: &[Type], fn_count: usize) {
        assert_eq!(
            self.input_type_count.get(),
            input_tys.len() as u32,
            "Mismatched input type count when implementing trait {}.",
            self.name,
        );
        assert_eq!(
            self.output_type_count(),
            output_tys.len() as u32,
            "Mismatched output type count when implementing trait {}.",
            self.name,
        );
        assert_eq!(
            self.functions.len(),
            fn_count,
            "Mismatched function count when implementing trait {}.",
            self.name,
        );
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

#[cfg(test)]
mod tests {
    // use std::vec;

    // use crate::{
    //     effects::EffType,
    //     std::{
    //         math::{float_type, int_type},
    //         string::string_type,
    //     }, r#type::FnType,
    // };

    // use super::*;

    // fn trait_add() -> TraitRef {
    //     let fn_ty = FnType::new_by_val(
    //         &[Type::variable_id(0), Type::variable_id(1)],
    //         Type::variable_id(2),
    //         EffType::empty(),
    //     );
    //     TraitRef::new(
    //         "Add",
    //         2,
    //         1,
    //         [(
    //             "add",
    //             FunctionDefinition::new_infer_quantifiers(
    //                 fn_ty,
    //                 &["lhs", "rhs"],
    //                 "test trait function add",
    //             ),
    //         )],
    //     )
    // }
}
