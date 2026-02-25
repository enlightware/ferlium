// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Debug},
    hash::{Hash, Hasher},
    ops::Deref,
    sync::Arc,
};

use dyn_clone::DynClone;
use ustr::Ustr;
use ustr::ustr;

use crate::{
    Location,
    containers::iterable_to_string,
    error::InternalCompilationError,
    format::{FormatWith, write_with_separator_and_format_fn},
    function::FunctionDefinition,
    module::{ModuleEnv, TraitImplId},
    trait_solver::TraitSolver,
    r#type::{Type, TypeSubstitution, TypeVar},
    type_like::TypeLike,
    type_scheme::PubTypeConstraint,
    type_visitor::TyVarsCollector,
};

/// Help deriving implementations of traits.
pub trait Deriver: Debug + DynClone + Sync + Send {
    /// Derive an implementation of a trait for the given input types, if possible.
    fn derive_impl(
        &self,
        trait_ref: &TraitRef,
        input_types: &[Type],
        span: Location,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError>;
}

dyn_clone::clone_trait_object!(Deriver);

/// A trait, equivalent to a multi-parameter type class in Haskell, with output types.
#[derive(Debug, Clone)]
pub struct Trait {
    /// Name of the trait, for debugging purposes.
    pub name: Ustr,
    /// Optional documentation for the trait.
    pub doc: Option<String>,
    /// Number of input types, by convention, the first type variables correspond to input types.
    pub input_type_names: Vec<Ustr>,
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
    /// Return the number of input types in this trait.
    pub fn input_type_count(&self) -> u32 {
        self.input_type_names.len() as u32
    }
    /// Return the number of output types in this trait.
    pub fn output_type_count(&self) -> u32 {
        self.output_type_names.len() as u32
    }

    /// Return the number of type variables in this trait.
    pub fn type_var_count(&self) -> u32 {
        self.input_type_count() + self.output_type_count()
    }

    /// Return the index of the method with the given name, if it exists.
    pub fn method_index(&self, name: Ustr) -> Option<usize> {
        self.functions
            .iter()
            .position(|(fn_name, _)| *fn_name == name)
    }

    /// Return the qualified method name for the given method index, e.g., "TraitName<…>::method_name"
    /// using the interned indices of the provided types.
    pub fn qualified_method_name(&self, index: usize, input_tys: &[Type]) -> String {
        let mut s = format!("{}<", self.name);
        for (i, ty) in input_tys.iter().enumerate() {
            if i > 0 {
                s.push_str(", ");
            }
            if let Some(world) = ty.world() {
                s.push_str(format!("{}-", world).as_str());
            }
            s.push_str(format!("{}", ty.index()).as_str());
        }
        s.push_str(&format!(">::{}", self.functions[index].0));
        s
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
                    panic!(
                        "Generic trait functions are not supported yet, but function {} of trait {} has a quantifier {}.",
                        name, self.name, quantifier
                    );
                }
            }
            if !function.ty_scheme.eff_quantifiers.is_empty() {
                panic!(
                    "Generic effects are not supported in trait functions yet, but function {} of trait {} has generic effects {}.",
                    name,
                    self.name,
                    iterable_to_string(&function.ty_scheme.eff_quantifiers, ", ")
                );
            }
            if !function.ty_scheme.constraints.is_empty() {
                panic!(
                    "Generic constraints are not supported in trait functions yet, but function {} of trait {} has {} generic constraints.",
                    name,
                    self.name,
                    function.ty_scheme.constraints.len()
                );
            }
            for input_ty_var in 0..self.input_type_count() {
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
                assert!(
                    input_tys
                        .iter()
                        .flat_map(TypeLike::inner_ty_vars)
                        .all(|ty_var| quantifiers.contains(&ty_var)),
                    "In trait {}, constraint #{} has unreachable input type variable in function {}.",
                    self.name,
                    i,
                    name
                );
                let mut additional_ty_vars = HashSet::new();
                let mut collector = TyVarsCollector(&mut additional_ty_vars);
                output_tys.iter().for_each(|ty| ty.visit(&mut collector));
                quantifiers.extend(additional_ty_vars);
            }
        }
    }

    /// Instantiate all function definitions of this trait for the given input and output types.
    pub fn instantiate_for_tys(
        &self,
        input_tys: &[Type],
        output_tys: &[Type],
    ) -> Vec<FunctionDefinition> {
        let ty_subst = self.get_substitution_for_tys(input_tys, output_tys);
        let inst_subst = (ty_subst, HashMap::new());
        self.functions
            .iter()
            .map(|(_, def)| {
                let mut def = def.instantiate(&inst_subst);
                def.ty_scheme.simplify();
                def
            })
            .collect::<Vec<_>>()
    }

    /// Get the type of the dictionary for this trait for the given input and output types.
    /// Only the types are substituted, the constraints are not considered.
    pub fn get_dictionary_type_for_tys(&self, input_tys: &[Type], output_tys: &[Type]) -> Type {
        let ty_subst = self.get_substitution_for_tys(input_tys, output_tys);
        let inst_subst = (ty_subst, HashMap::new());
        Type::tuple(
            self.functions
                .iter()
                .map(|(_, def)| Type::function_type(def.ty_scheme.ty.instantiate(&inst_subst)))
                .collect::<Vec<_>>(),
        )
    }

    fn get_substitution_for_tys(
        &self,
        input_tys: &[Type],
        output_tys: &[Type],
    ) -> TypeSubstitution {
        assert!(input_tys.len() == self.input_type_count() as usize);
        assert!(output_tys.len() == self.output_type_count() as usize);
        input_tys
            .iter()
            .chain(output_tys.iter())
            .enumerate()
            .map(|(i, ty)| (TypeVar::new(i as u32), *ty))
            .collect::<HashMap<_, _>>()
    }
}

impl FormatWith<ModuleEnv<'_>> for Trait {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv) -> fmt::Result {
        if let Some(doc) = &self.doc {
            for line in doc.split("\n") {
                writeln!(f, "/// {line}")?;
            }
        }
        write!(f, "trait {} <", self.name)?;
        let input_ty_count = self.input_type_count();
        write_with_separator_and_format_fn(
            0..input_ty_count,
            ", ",
            |index, f| {
                write!(
                    f,
                    "{} = {}",
                    self.input_type_names[index as usize],
                    TypeVar::new(index)
                )
            },
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
            write!(f, ">\nwhere")?;
            for constraint in &self.constraints {
                write!(f, "\n    ")?;
                constraint.fmt_with(f, env)?;
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
            def.fmt_with_name_and_module_env(f, *name, "    ", env)?;
        }
        writeln!(f, "\n}}")?;
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct TraitRef(pub(crate) Arc<Trait>);

impl TraitRef {
    pub fn new<'a>(
        name: &str,
        doc: &str,
        input_type_names: impl Into<Vec<&'a str>>,
        output_type_names: impl Into<Vec<&'a str>>,
        functions: impl Into<Vec<(&'a str, FunctionDefinition)>>,
    ) -> Self {
        let input_type_names = input_type_names.into();
        assert!(
            !input_type_names.is_empty(),
            "A trait must have at least one input type."
        );
        let functions = functions
            .into()
            .into_iter()
            .map(|(name, def)| (ustr(name), def))
            .collect();
        let trait_data = Trait {
            name: ustr(name),
            doc: Some(doc.to_string()),
            input_type_names: input_type_names.into_iter().map(ustr).collect(),
            output_type_names: output_type_names.into().into_iter().map(ustr).collect(),
            constraints: Vec::new(),
            functions,
            derives: Vec::new(),
        };
        trait_data.validate();
        Self(Arc::new(trait_data))
    }

    pub fn new_with_self_input_type<'a>(
        name: &str,
        doc: &str,
        output_type_names: impl Into<Vec<&'a str>>,
        functions: impl Into<Vec<(&'a str, FunctionDefinition)>>,
    ) -> Self {
        Self::new(name, doc, ["Self"], output_type_names, functions)
    }

    pub fn new_with_constraints<'a>(
        name: &str,
        doc: &str,
        input_type_names: impl Into<Vec<&'a str>>,
        output_type_names: impl Into<Vec<&'a str>>,
        constraints: impl Into<Vec<PubTypeConstraint>>,
        functions: impl Into<Vec<(&'a str, FunctionDefinition)>>,
    ) -> Self {
        let input_type_names = input_type_names.into();
        assert!(
            !input_type_names.is_empty(),
            "A trait must have at least one input type."
        );
        let functions = functions
            .into()
            .into_iter()
            .map(|(name, def)| (ustr(name), def))
            .collect();
        let trait_data = Trait {
            name: ustr(name),
            doc: Some(doc.to_string()),
            input_type_names: input_type_names.into_iter().map(ustr).collect(),
            output_type_names: output_type_names.into().into_iter().map(ustr).collect(),
            constraints: constraints.into(),
            functions,
            derives: Vec::new(),
        };
        trait_data.validate();
        Self(Arc::new(trait_data))
    }

    pub fn validate_impl_size(&self, input_tys: &[Type], output_tys: &[Type], fn_count: usize) {
        assert_eq!(
            self.input_type_count(),
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
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for TraitRef {}

impl Hash for TraitRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(Arc::as_ptr(&self.0), state)
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
