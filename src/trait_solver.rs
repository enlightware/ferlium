// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::{
    collections::{HashMap, HashSet},
    fmt,
    rc::Rc,
};

use ustr::Ustr;

use crate::{
    containers::{b, SVec2},
    error::InternalCompilationError,
    format::{write_with_separator_and_format_fn, FormatWith},
    function::{Closure, Function, FunctionDefinition, FunctionRc, FunctionRef},
    internal_compilation_error,
    module::{FmtWithModuleEnv, ModuleEnv},
    r#trait::TraitRef,
    r#type::{Type, TypeSubstitution, TypeVar},
    std::{core::REPR_TRAIT, new_module_using_std},
    type_inference::{InstSubstitution, UnifiedTypeInference},
    type_like::TypeLike,
    type_scheme::{format_constraints_consolidated, PubTypeConstraint},
    type_visitor::AllVarsCollector,
    value::Value,
    Location,
};

/// A concrete implementation of a trait.
#[derive(Debug, Clone)]
pub struct ConcreteTraitImpl {
    /// The output types of the trait.
    pub output_tys: Vec<Type>,
    /// The implemented methods, in a tuple of first-class functions of the proper types.
    /// We use a tuple to simply clone it when filling the dictionary entries.
    pub functions: Value,
}

/// A blanket implementation of a trait.
#[derive(Debug, Clone)]
pub struct BlanketTraitImpl {
    /// Number of type variables in this blanket implementation.
    pub ty_var_count: u32,
    /// The generic constraints necessary to implement the trait.
    pub constraints: Vec<PubTypeConstraint>,
    /// The output types of the trait.
    pub output_tys: Vec<Type>,
    /// The implemented methods, matching constraints
    pub functions: Vec<FunctionRc>,
}

/// A vector of traits.
pub type Traits = Vec<TraitRef>;

/// A pair of a trait reference and a list of input types forming a key for a concrete trait implementations.
pub type TraitImplKey = (TraitRef, Vec<Type>);

/// The trait blanket implementations for a given trait.
pub type BlanketTraitImpls = Vec<(Vec<Type>, Rc<BlanketTraitImpl>)>;

/// All trait implementations in a module or in a given context.
/// Trait solving is performed by this structure, mutating it by caching intermediate results.
#[derive(Clone, Debug, Default)]
pub struct TraitImpls {
    pub(crate) concrete: HashMap<TraitImplKey, Rc<ConcreteTraitImpl>>,
    pub(crate) blanket: HashMap<TraitRef, BlanketTraitImpls>,
}

impl TraitImpls {
    /// Add a concrete trait implementation to this module.
    pub fn add_concrete(
        &mut self,
        trait_ref: TraitRef,
        input_tys: impl Into<Vec<Type>>,
        output_tys: impl Into<Vec<Type>>,
        functions: impl Into<Vec<Function>>,
    ) -> Rc<ConcreteTraitImpl> {
        let input_tys = input_tys.into();
        let output_tys = output_tys.into();
        let functions: SVec2<_> = functions.into().into_iter().map(Value::function).collect();
        trait_ref.validate_impl_size(&input_tys, &output_tys, functions.len());
        let functions = Value::tuple(functions);
        let imp = ConcreteTraitImpl {
            output_tys,
            functions,
        };
        let key = (trait_ref, input_tys);
        let imp = Rc::new(imp);
        self.concrete.insert(key, imp.clone());
        imp
    }

    /// Add a blanket trait implementation to this module.
    pub fn add_blanket(
        &mut self,
        trait_ref: TraitRef,
        input_tys: impl Into<Vec<Type>>,
        output_tys: impl Into<Vec<Type>>,
        ty_var_count: u32,
        constraints: impl Into<Vec<PubTypeConstraint>>,
        functions: impl Into<Vec<FunctionRc>>,
    ) -> Rc<BlanketTraitImpl> {
        let input_tys = input_tys.into();
        let output_tys = output_tys.into();
        let constraints = constraints.into();
        let functions = functions.into();
        trait_ref.validate_impl_size(&input_tys, &output_tys, functions.len());
        let imp = BlanketTraitImpl {
            ty_var_count,
            constraints,
            output_tys,
            functions,
        };
        let imp = Rc::new(imp);
        self.blanket
            .entry(trait_ref)
            .or_default()
            .push((input_tys, imp.clone()));
        imp
    }

    pub fn concrete(&self) -> &HashMap<TraitImplKey, Rc<ConcreteTraitImpl>> {
        &self.concrete
    }

    pub fn blanket(&self) -> &HashMap<TraitRef, BlanketTraitImpls> {
        &self.blanket
    }

    pub fn is_empty(&self) -> bool {
        self.concrete.is_empty() && self.blanket.is_empty()
    }

    /// Get the output types for the given trait reference and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If no blanket implementation is found, an error is returned.
    /// This function is implemented using get_impl.
    pub fn get_output_types(
        &mut self,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        Ok(self
            .get_impl(trait_ref, input_tys, fn_span)?
            .output_tys
            .clone())
    }

    /// Get the functions dictionary value for the given trait reference and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If no blanket implementation is found, an error is returned.
    /// This function is implemented using get_impl.
    pub fn get_functions(
        &mut self,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<Value, InternalCompilationError> {
        Ok(self
            .get_impl(trait_ref, input_tys, fn_span)?
            .functions
            .clone())
    }

    /// Get the concrete trait implementation for the given trait reference and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If no blanket implementation is found, an error is returned.
    /// This is the trait solver's core function.
    pub fn get_impl(
        &mut self,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<Rc<ConcreteTraitImpl>, InternalCompilationError> {
        // Sanity checks
        assert!(
            input_tys.iter().all(Type::is_constant),
            "Getting trait implementation for non-constant input types"
        );

        // Special case for `Repr` trait.
        if trait_ref == &*REPR_TRAIT {
            let input_ty = input_tys[0];
            let ty_data = input_ty.data();
            let output_ty = if let Some(named) = ty_data.as_named() {
                if !named.params.is_empty() {
                    todo!("Repr trait for named types with arguments is not supported yet");
                }
                named.def.shape
            } else {
                input_ty
            };
            return Ok(Rc::new(ConcreteTraitImpl {
                output_tys: vec![output_ty],
                functions: Value::empty_tuple(),
            }));
        }

        // If a concrete implementation is found, return it.
        let key = (trait_ref.clone(), input_tys.to_vec());
        if let Some(imp) = self.concrete.get(&key) {
            return Ok(imp.clone());
        }

        // No concrete implementation found, search for a matching blanket implementation.
        if let Some(blanket_impls) = self.blanket.get(trait_ref) {
            // We clone because we might cache new implementations while recursing.
            let blanket_impls = blanket_impls.clone();
            'impl_loop: for (imp_input_tys, imp) in blanket_impls.iter() {
                // Sanity checks
                #[cfg(debug_assertions)]
                {
                    assert_eq!(imp_input_tys.len(), input_tys.len());
                    let mut ty_vars = HashSet::new();
                    let mut mut_vars = HashSet::new();
                    let mut eff_vars = HashSet::new();
                    let mut collector = AllVarsCollector {
                        ty_vars: &mut ty_vars,
                        mut_vars: &mut mut_vars,
                        effect_vars: &mut eff_vars,
                    };
                    for ty in imp_input_tys {
                        ty.visit(&mut collector);
                    }
                    for constraint in imp.constraints.iter() {
                        constraint.visit(&mut collector);
                    }
                    assert!(mut_vars.is_empty());
                    assert!(eff_vars.is_empty());
                    assert_eq!(ty_vars.len(), imp.ty_var_count as usize);
                }

                // Does this implementation matches the input types? We try to unify the types to find out.
                let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(imp.ty_var_count);
                for (imp_input_ty, input_ty) in imp_input_tys.iter().zip(input_tys.iter()) {
                    assert!(input_ty.is_constant());
                    // Note: expected_span is wrong in unify_same_type, but it doesn't matter because
                    // this error is not reported to the user.
                    if ty_inf
                        .unify_same_type(*imp_input_ty, fn_span, *input_ty, fn_span)
                        .is_err()
                    {
                        // No, try next implementation.
                        continue 'impl_loop;
                    }
                }

                // Yes, instantiate the constraints and get the corresponding function dictionaries
                // (as Value containing a tuple of first-class functions).
                let mut constraint_fn_dicts = Vec::new();
                // Note: we assume the constraints are ordered by dependency so that the output types
                // of one are the input types of the next.
                for constraint in &imp.constraints {
                    let (trait_ref, input_tys, output_tys, _span) = ty_inf
                        .substitute_in_constraint(constraint)
                        .into_have_trait()
                        .expect("Non trait constraint in blanket impl");
                    assert!(input_tys.iter().all(Type::is_constant));
                    let new_output_tys = self.get_output_types(&trait_ref, &input_tys, fn_span)?;
                    for (new_output_ty, output_ty) in new_output_tys.iter().zip(output_tys.iter()) {
                        assert!(new_output_ty.is_constant());
                        // Note: expected_span is wrong in unify_same_type, but it doesn't matter because
                        // this error is not reported to the user.
                        if ty_inf
                            .unify_same_type(*new_output_ty, fn_span, *output_ty, fn_span)
                            .is_err()
                        {
                            // No, try next implementation.
                            continue 'impl_loop;
                        }
                    }

                    let functions = self.get_functions(&trait_ref, &input_tys, fn_span);
                    let functions = match functions {
                        Ok(functions) => functions,
                        // Failed? Try next implementation.
                        Err(_) => continue 'impl_loop,
                    };
                    constraint_fn_dicts.push(functions.clone());
                }

                // Succeeded? Build a new concrete implementation with closures.
                let output_tys = ty_inf.substitute_in_types(&imp.output_tys);
                let closed_fns: SVec2<_> = imp
                    .functions
                    .iter()
                    .map(|f| {
                        Value::function(b(Closure::new(
                            FunctionRef::new_strong(f),
                            constraint_fn_dicts.clone(),
                        )))
                    })
                    .collect();
                let functions = Value::tuple(closed_fns);
                let concrete_imp = Rc::new(ConcreteTraitImpl {
                    output_tys,
                    functions,
                });

                // Cache the result and return it.
                self.concrete.insert(key, concrete_imp.clone());
                return Ok(concrete_imp);
            }
        }

        // No blanket implementation found, look for a derived implementation.
        for derive in &trait_ref.derives {
            if let Some(concrete_imp) = derive.derive_impl(trait_ref, input_tys, fn_span, self)? {
                // Cache the derived implementation.
                let key = (trait_ref.clone(), input_tys.to_vec());
                let concrete_imp = Rc::new(concrete_imp);
                self.concrete.insert(key, concrete_imp.clone());
                // And return it.
                return Ok(concrete_imp);
            } else {
                println!(
                    "Tried derivation for trait {} with input types {:?}, but failed.",
                    trait_ref.name, input_tys
                );
            }
        }

        // No matching implementation found.
        let others = crate::module::Modules::default();
        let current = new_module_using_std();
        let module_env = ModuleEnv::new(&current, &others);
        let filter = |tr: &TraitRef| tr.name == trait_ref.name;
        println!("Existing impls for {}:\n", trait_ref.name);
        println!(
            "{}",
            FormatWith {
                value: self,
                data: &(module_env, filter)
            }
        );
        Err(internal_compilation_error!(TraitImplNotFound {
            trait_ref: trait_ref.clone(),
            input_tys: input_tys.to_vec(),
            fn_span,
        }))
    }

    fn fmt_with_filter(
        &self,
        f: &mut std::fmt::Formatter,
        env: &crate::module::ModuleEnv<'_>,
        filter: impl Fn(&TraitRef) -> bool,
    ) -> std::fmt::Result {
        for (key, imp) in &self.concrete {
            if filter(&key.0) {
                format_concrete_impl(key, imp, f, env)?;
            }
        }
        for (trait_ref, impls) in &self.blanket {
            if filter(trait_ref) {
                for (input_ty, imp) in impls {
                    format_blanket_impl(trait_ref, input_ty, imp, f, env)?;
                }
            }
        }
        Ok(())
    }
}

impl FmtWithModuleEnv for TraitImpls {
    fn fmt_with_module_env(
        &self,
        f: &mut std::fmt::Formatter,
        env: &crate::module::ModuleEnv<'_>,
    ) -> std::fmt::Result {
        self.fmt_with_filter(f, env, |_| true)
    }
}

impl<F> fmt::Display for FormatWith<'_, TraitImpls, (ModuleEnv<'_>, F)>
where
    F: Fn(&TraitRef) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt_with_filter(f, &self.data.0, &self.data.1)
    }
}

fn format_concrete_impl(
    key: &TraitImplKey,
    imp: &ConcreteTraitImpl,
    f: &mut std::fmt::Formatter,
    env: &crate::module::ModuleEnv<'_>,
) -> std::fmt::Result {
    let (trait_ref, input_tys) = key;
    let subst = format_impl_header(trait_ref, input_tys, &imp.output_tys, f, env)?;
    let subst = (subst, HashMap::new());
    writeln!(f, " {{")?;
    let impl_functions = imp.functions.as_tuple().unwrap();
    let mut first = true;
    for ((name, def), fn_value) in trait_ref.functions.iter().zip(impl_functions.iter()) {
        if first {
            first = false;
        } else {
            writeln!(f)?;
        }
        let fn_code = fn_value.as_function().unwrap().0.get();
        format_impl_fn(*name, def, &subst, &fn_code, f, env)?;
    }
    writeln!(f, "}}\n")
}

fn format_blanket_impl(
    trait_ref: &TraitRef,
    input_tys: &[Type],
    imp: &BlanketTraitImpl,
    f: &mut std::fmt::Formatter,
    env: &crate::module::ModuleEnv<'_>,
) -> std::fmt::Result {
    let subst = format_impl_header(trait_ref, input_tys, &imp.output_tys, f, env)?;
    let subst = (subst, HashMap::new());
    if !imp.constraints.is_empty() {
        write!(f, " where ")?;
        format_constraints_consolidated(&imp.constraints, f, env)?;
    }
    writeln!(f, " {{")?;
    let mut first = true;
    for ((name, def), fn_code) in trait_ref.functions.iter().zip(imp.functions.iter()) {
        if first {
            first = false;
        } else {
            writeln!(f)?;
        }
        format_impl_fn(*name, def, &subst, fn_code, f, env)?;
    }
    writeln!(f, "}}\n")
}

fn format_impl_header(
    trait_ref: &TraitRef,
    input_tys: &[Type],
    output_tys: &[Type],
    f: &mut std::fmt::Formatter,
    env: &crate::module::ModuleEnv<'_>,
) -> Result<TypeSubstitution, std::fmt::Error> {
    write!(f, "impl {} for <", trait_ref.name)?;
    write_with_separator_and_format_fn(
        input_tys.iter(),
        ", ",
        |ty, f| write!(f, "{}", ty.format_with(env)),
        f,
    )?;
    if !output_tys.is_empty() {
        write!(f, " ↦ ")?;
        write_with_separator_and_format_fn(
            output_tys.iter(),
            ", ",
            |ty, f| write!(f, "{}", ty.format_with(env)),
            f,
        )?;
    }
    write!(f, ">")?;
    let mut subst = TypeSubstitution::new();
    for (i, ty) in input_tys.iter().enumerate() {
        subst.insert(TypeVar::new(i as u32), *ty);
    }
    for (i, ty) in output_tys.iter().enumerate() {
        subst.insert(TypeVar::new(i as u32 + input_tys.len() as u32), *ty);
    }
    Ok(subst)
}

fn format_impl_fn(
    name: Ustr,
    def: &FunctionDefinition,
    subst: &InstSubstitution,
    fn_code: &FunctionRc,
    f: &mut std::fmt::Formatter,
    env: &crate::module::ModuleEnv<'_>,
) -> std::fmt::Result {
    let ty = def.ty_scheme.ty.instantiate(subst);
    if def.ty_scheme.constraints.is_empty() {
        writeln!(f, "  fn {name} {}", ty.format_with(env))?;
    } else {
        write!(f, "  fn {name} {} where ", ty.format_with(env))?;
        format_constraints_consolidated(&def.ty_scheme.constraints, f, env)?;
        writeln!(f)?;
    }
    fn_code.borrow().format_ind(f, env, 1, 1)
}
