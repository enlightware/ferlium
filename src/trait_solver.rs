// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::{
    cell::RefCell,
    hash::{DefaultHasher, Hash, Hasher},
    rc::Rc,
};

use derive_new::new;
use itertools::MultiUnzip;
use ustr::Ustr;

use crate::{
    Location,
    containers::b,
    effects::EffType,
    error::InternalCompilationError,
    function::{Function, FunctionRc, ScriptFunction},
    internal_compilation_error,
    ir::Node,
    ir_syn::{get_dictionary, load, static_apply},
    module::{
        self, BlanketTraitImplKey, BlanketTraitImpls, ConcreteTraitImplKey, FunctionCollector,
        FunctionId, ImportFunctionSlot, ImportFunctionSlotId, ImportFunctionTarget, ImportImplSlot,
        ImportImplSlotId, LocalFunction, LocalImplId, ModuleEnv, ModuleFunction, Modules,
        TraitImpl, TraitImplId, TraitImpls, TraitKey,
    },
    mutability::MutType,
    std::{core::REPR_TRAIT, new_module_using_std},
    r#trait::TraitRef,
    r#type::{FnArgType, Type},
    type_inference::UnifiedTypeInference,
    type_like::TypeLike,
    value::Value,
};

#[cfg(debug_assertions)]
use crate::type_visitor::AllVarsCollector;
#[cfg(debug_assertions)]
use std::collections::HashSet;

/// Trait solving is performed by this structure, mutating it by caching intermediate results.
#[derive(Debug, new)]
#[must_use = "call .commit() to store the created functions"]
pub struct TraitSolver<'a> {
    /// Current module implementations.
    pub impls: &'a mut TraitImpls,
    /// Current module function import slots.
    pub import_fn_slots: &'a mut Vec<ImportFunctionSlot>,
    /// Current module trait import slots.
    pub import_impl_slots: &'a mut Vec<ImportImplSlot>,
    /// Collector for newly created current module functions.
    pub fn_collector: FunctionCollector,
    /// Other modules available for fetching trait implementations and normal functions (read only).
    pub others: &'a Modules,
}

/// Macro to create a trait solver from a module and a program.
/// This cannot be a function because of lifetime issues, as we must
/// mutably borrow parts of the module's data while not touching the function field.
macro_rules! trait_solver_from_module {
    ($module:expr, $program:expr) => {
        TraitSolver::new(
            &mut $module.impls,
            &mut $module.import_fn_slots,
            &mut $module.import_impl_slots,
            crate::module::FunctionCollector::new($module.functions.len()),
            $program,
        )
    };
}
pub(crate) use trait_solver_from_module;

impl<'a> TraitSolver<'a> {
    /// Commit the newly created functions to the module.
    /// This must be called after trait solving is done,
    /// otherwise the created functions will be lost.
    pub fn commit(mut self, functions: &mut Vec<LocalFunction>) {
        functions.append(&mut self.fn_collector.new_elements);
    }

    /// Add a concrete trait implementation from the given code node, for single-function traits.
    pub fn add_concrete_impl_from_code(
        &mut self,
        code: Node,
        trait_ref: &TraitRef,
        input_types: impl Into<Vec<Type>>,
        output_types: impl Into<Vec<Type>>,
    ) -> LocalImplId {
        let arg_names = trait_ref.functions[0].1.arg_names.clone();
        let function: Function = b(ScriptFunction::new(code, arg_names));
        self.impls.add_concrete_raw(
            trait_ref.clone(),
            input_types.into(),
            output_types.into(),
            [function],
            &mut self.fn_collector,
        )
    }

    /// Check if a concrete trait implementation exists, without performing any solving.
    /// This searches in current module first, then in other modules.
    /// Only public implementations from other modules are considered.
    pub fn has_concrete_impl(&self, key: &ConcreteTraitImplKey) -> bool {
        self.impls.concrete_key_to_id.contains_key(key)
            || self.others.modules.iter().any(|(_, m)| {
                let id = m.impls.concrete_key_to_id.get(key);
                if let Some(id) = id {
                    let imp = &m.impls.data[id.as_index()];
                    imp.public
                } else {
                    false
                }
            })
    }

    /// Get a concrete trait implementation by its key, without performing any solving.
    /// This searches in current module first, then in other modules.
    /// Only public implementations from other modules are considered.
    /// If found in other modules, the import slots are updated.
    pub fn get_concrete_impl(&mut self, key: &ConcreteTraitImplKey) -> Option<TraitImplId> {
        self.impls
            .concrete_key_to_id
            .get(key)
            .map(|id| TraitImplId::Local(*id))
            .or_else(|| {
                self.others.modules.iter().find_map(|(path, m)| {
                    m.impls.concrete_key_to_id.get(key).and_then(|id| {
                        let imp = &m.impls.data[id.as_index()];
                        if imp.public {
                            Some(TraitImplId::Import(self.import_impl_dictionary(
                                path,
                                TraitKey::Concrete(key.clone()),
                            )))
                        } else {
                            None
                        }
                    })
                })
            })
    }

    /// Get the blanket trait implementations for the given trait reference, without performing any solving.
    /// This searches in other modules first, then in the current module.
    fn get_blanket_impls<'s: 'b, 'b>(
        &'s self,
        trait_ref: &'b TraitRef,
    ) -> impl Iterator<Item = (Option<&'b module::Path>, &'b BlanketTraitImpls)> + use<'b> {
        self.impls
            .blanket_key_to_id
            .get(trait_ref)
            .map(|blankets| (None, blankets))
            .into_iter()
            .chain(self.others.modules.iter().flat_map(|(path, m)| {
                m.impls
                    .blanket_key_to_id
                    .get(trait_ref)
                    .map(|imp| (Some(path), imp))
            }))
    }

    /// Print all known implementations for the given trait reference.
    fn log_debug_impls(&self, trait_ref: &TraitRef) {
        log::debug!("In current module:");
        let fake_current = new_module_using_std();
        let env = ModuleEnv::new(&fake_current, self.others, false);
        self.impls.log_debug_impls_headers(trait_ref, env);
        for (module_path, module) in &self.others.modules {
            if module.impls.blanket_key_to_id.contains_key(trait_ref) {
                log::debug!("In module {}:", module_path);
                module.impls.log_debug_impls_headers(trait_ref, env);
            }
        }
    }

    /// Get a concrete trait implementation for the given trait reference and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If matching blanket implementation is found, a derivation is attempted, if available.
    /// Otherwise an error is returned.
    /// This is the trait solver's core function.
    pub fn solve_impl(
        &mut self,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<TraitImplId, InternalCompilationError> {
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
            drop(ty_data); // avoid borrow issues

            // Only search in current module, create a new implementation if not found.
            let key = ConcreteTraitImplKey::new(trait_ref.clone(), input_tys.to_vec());
            let local_id = if let Some(id) = self.impls.concrete_key_to_id.get(&key) {
                *id
            } else {
                let imp = TraitImpl {
                    output_tys: vec![output_ty],
                    methods: vec![],
                    interface_hash: 0,
                    dictionary_value: RefCell::new(Value::empty_tuple()),
                    dictionary_ty: Type::tuple([]),
                    public: false,
                };
                self.impls.add_concrete_struct(key, imp)
            };
            return Ok(TraitImplId::Local(local_id));
        }

        // If a concrete implementation is found, return it.
        let key = ConcreteTraitImplKey::new(trait_ref.clone(), input_tys.to_vec());
        if let Some(imp) = self.get_concrete_impl(&key) {
            return Ok(imp);
        }

        // No concrete implementation found, search for a matching blanket implementation.
        // We first clone all blanket implementations to avoid borrowing issues.
        let blankets = self
            .get_blanket_impls(trait_ref)
            .map(|(mod_path, blankets)| (mod_path.cloned(), blankets.clone()))
            .collect::<Vec<_>>();
        // Then we iterate over all blanket implementations, trying to unify their input types
        for (imp_mod_path, blanket_impls) in blankets {
            'impl_loop: for (sub_key, impl_id) in blanket_impls.iter() {
                let imp_input_tys = &sub_key.input_tys;
                let imp_ty_var_count = sub_key.ty_var_count;
                let imp_constraints = &sub_key.constraints;

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
                    for constraint in imp_constraints.iter() {
                        constraint.visit(&mut collector);
                    }
                    assert!(mut_vars.is_empty());
                    assert!(eff_vars.is_empty());
                    assert_eq!(ty_vars.len(), imp_ty_var_count as usize);
                }

                // Does this implementation matches the input types? We try to unify the types to find out.
                let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(imp_ty_var_count);
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
                // We process constraints iteratively because constraints may not be ordered by
                // dependency. After solving a constraint and unifying its output types, those
                // types become available for subsequent constraints that depend on them.
                // We maintain a map from constraint index to dict_id to preserve the original order.
                let mut constraint_dict_ids: Vec<Option<TraitImplId>> =
                    vec![None; imp_constraints.len()];
                let mut remaining_indices: Vec<_> = (0..imp_constraints.len()).collect();
                loop {
                    let initial_count = remaining_indices.len();
                    let mut still_remaining = Vec::new();

                    for constraint_idx in remaining_indices {
                        let constraint = &imp_constraints[constraint_idx];
                        let (trait_ref, input_tys, output_tys, _span) = ty_inf
                            .substitute_in_constraint(constraint)
                            .into_have_trait()
                            .expect("Non trait constraint in blanket impl");
                        // If some input types are not constant, we cannot solve this constraint yet.
                        // Defer it and try again after solving other constraints that may provide
                        // the missing type information.
                        if !input_tys.iter().all(Type::is_constant) {
                            still_remaining.push(constraint_idx);
                            continue;
                        }
                        let new_output_tys =
                            match self.solve_output_types(&trait_ref, &input_tys, fn_span) {
                                Ok(tys) => tys,
                                // Constraint not satisfied, try next implementation.
                                Err(_) => continue 'impl_loop,
                            };
                        for (new_output_ty, output_ty) in
                            new_output_tys.iter().zip(output_tys.iter())
                        {
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

                        let dict_id = self.solve_impl(&trait_ref, &input_tys, fn_span);
                        let dict_id = match dict_id {
                            Ok(functions) => functions,
                            // Failed? Try next implementation.
                            Err(_) => continue 'impl_loop,
                        };
                        constraint_dict_ids[constraint_idx] = Some(dict_id);
                    }

                    // If all constraints are solved, we're done.
                    if still_remaining.is_empty() {
                        break;
                    }

                    // If no progress was made, this implementation doesn't work.
                    if still_remaining.len() == initial_count {
                        continue 'impl_loop;
                    }

                    remaining_indices = still_remaining;
                }
                // Unwrap all the dict_ids - they should all be Some by now.
                let constraint_dict_ids: Vec<_> = constraint_dict_ids
                    .into_iter()
                    .map(|opt| opt.expect("All constraints should be solved"))
                    .collect();

                // Succeeded? First get the blanket implementation data and compute the output types.
                let impls = if let Some(module_path) = &imp_mod_path {
                    &self.others.modules[module_path].impls
                } else {
                    #[allow(clippy::needless_borrow)] // clippy has a bug here as of Rust 1.90
                    &self.impls
                };
                let imp = &impls.data[impl_id.as_index()];
                let output_tys = ty_inf.substitute_in_types(&imp.output_tys);

                // Then build IR nodes for fetching each closed constraint dictionary.
                // FIXME: using function span is quite incorrect here, think of a better span. Optional?
                let constraint_dict_nodes = constraint_dict_ids
                    .into_iter()
                    .map(|dict_id| {
                        let ty = self.get_impl_data_by_id(dict_id).dictionary_ty;
                        Node::new(get_dictionary(dict_id), ty, EffType::empty(), fn_span)
                    })
                    .collect::<Vec<_>>();

                // Then, for every function in the blanket implementation, if needed create a thunk function
                // importing it and closing over the constraint dictionaries.
                let trait_key =
                    TraitKey::Blanket(BlanketTraitImplKey::new(trait_ref.clone(), sub_key.clone()));
                let definitions = trait_ref.instantiate_for_tys(input_tys, &output_tys);
                let gen_functions = imp.methods.clone(); // clone to avoid borrowing issues
                let mut interface_hasher = DefaultHasher::new();
                let (methods, tys): (Vec<_>, Vec<_>) = gen_functions
                    .iter()
                    .zip(definitions.into_iter())
                    .enumerate()
                    .map(|(method_index, (fn_id, def))| {
                        // Build the concrete function type and hash its signature.
                        let fn_ty = Type::function_type(def.ty_scheme.ty.clone());
                        def.signature_hash().hash(&mut interface_hasher);

                        // Is the generic function from another module, or do we need to pass constraint dictionaries?
                        let id = if constraint_dict_nodes.is_empty() && imp_mod_path.is_none() {
                            // No, so we can just use the generic function as is.
                            *fn_id
                        } else {
                            // Yes, get the function id for doing the call to the generic function.
                            let function_id = match &imp_mod_path {
                                Some(module_path) => {
                                    let slot_id = self.import_impl_method(
                                        module_path,
                                        trait_key.clone(),
                                        method_index as u32,
                                    );
                                    FunctionId::Import(slot_id)
                                }
                                None => FunctionId::Local(*fn_id),
                            };

                            // Build the arguments for the call: first the constraint dictionaries, then the original arguments.
                            let arguments: Vec<_> = constraint_dict_nodes
                                .iter()
                                .cloned()
                                .chain(def.ty_scheme.ty.args.iter().enumerate().map(
                                    |(arg_i, arg_ty)| {
                                        Node::new(load(arg_i), arg_ty.ty, EffType::empty(), fn_span)
                                    },
                                ))
                                .collect();

                            // Build the function type with added constraint dictionary arguments.
                            let mut ext_fn_ty = def.ty_scheme.ty.clone();
                            ext_fn_ty.args.splice(
                                0..0,
                                constraint_dict_nodes
                                    .iter()
                                    .map(|n| FnArgType::new(n.ty, MutType::constant())),
                            );

                            // Build the application node.
                            let apply = static_apply(function_id, ext_fn_ty, arguments, fn_span);
                            let code = b(ScriptFunction::new(
                                Node::new(apply, def.ty_scheme.ty.ret, EffType::empty(), fn_span),
                                def.arg_names.clone(),
                            ));
                            let code: FunctionRc = Rc::new(RefCell::new(code));
                            let function = ModuleFunction::new_without_spans(def, code);
                            let name = Ustr::from(&format!(
                                "{} (thunk)>",
                                trait_ref.qualified_method_name(method_index)
                            ));
                            let local_fn =
                                LocalFunction::new_compute_interface_hash(function, name);
                            let id = self.fn_collector.next_id();
                            self.fn_collector.push(local_fn);
                            id
                        };

                        (id, fn_ty)
                    })
                    .multiunzip();

                // Build and insert the implementation.
                let interface_hash = interface_hasher.finish();
                let dictionary_ty = Type::tuple(tys);
                let dictionary_value = RefCell::new(Value::unit()); // filled later in finalize
                let imp = TraitImpl::new(
                    output_tys,
                    methods,
                    interface_hash,
                    dictionary_value,
                    dictionary_ty,
                    true,
                );
                let key = ConcreteTraitImplKey::new(trait_ref.clone(), input_tys.to_vec());
                let local_impl_id = self.impls.add_concrete_struct(key, imp);

                return Ok(TraitImplId::Local(local_impl_id));
            }
        }

        // No blanket implementation found, look for a derived implementation.
        for derive in &trait_ref.derives {
            if let Some(impl_id) = derive.derive_impl(trait_ref, input_tys, fn_span, self)? {
                return Ok(impl_id);
            } else {
                log::debug!(
                    "Tried derivation for trait {} with input types {:?}, but failed.",
                    trait_ref.name,
                    input_tys
                );
            }
        }

        // No matching implementation found.
        log::debug!(
            "No matching impl for trait \"{}\" found. Existing impls:",
            trait_ref.name
        );
        self.log_debug_impls(trait_ref);
        Err(internal_compilation_error!(TraitImplNotFound {
            trait_ref: trait_ref.clone(),
            input_tys: input_tys.to_vec(),
            fn_span,
        }))
    }

    /// Get a specific method implementation for the given trait reference and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If matching blanket implementation is found, a derivation is attempted, if available.
    /// Otherwise an error is returned.
    /// This function is implemented using solve_impl.
    pub fn solve_impl_method(
        &mut self,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        index: usize,
        fn_span: Location,
    ) -> Result<FunctionId, InternalCompilationError> {
        let impl_id = self.solve_impl(trait_ref, input_tys, fn_span)?;
        use TraitImplId::*;
        Ok(match impl_id {
            Local(id) => FunctionId::Local(self.impls.data[id.as_index()].methods[index]),
            Import(slot_id) => {
                let slot = &self.import_impl_slots[slot_id.as_index()];
                // FIXME: this clone is due to lifetime issues, find a better solution
                let module_path = slot.module.clone();
                let key = slot.key.as_concrete().unwrap();
                let key = TraitKey::Concrete(key.clone());
                FunctionId::Import(self.import_impl_method(&module_path, key, index as u32))
            }
        })
    }

    /// Get the output types for the given trait reference and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If matching blanket implementation is found, a derivation is attempted, if available.
    /// Otherwise an error is returned.
    /// This function is implemented using solve_impl.
    pub fn solve_output_types(
        &mut self,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        let impl_id = self.solve_impl(trait_ref, input_tys, fn_span)?;
        Ok(self.get_impl_data_by_id(impl_id).output_tys.clone())
    }

    /// Get a specific trait implementation data by its id.
    pub fn get_impl_data_by_id(&self, impl_id: TraitImplId) -> &TraitImpl {
        use TraitImplId::*;
        match impl_id {
            Local(id) => &self.impls.data[id.as_index()],
            Import(slot_id) => {
                let slot = &self.import_impl_slots[slot_id.as_index()];
                let module_path = &slot.module;
                let key = slot.key.as_concrete().unwrap();
                let other_impls = &self
                    .others
                    .modules
                    .get(module_path)
                    .expect("imported module not found")
                    .impls;
                let id = other_impls
                    .concrete_key_to_id
                    .get(key)
                    .expect("imported trait impl not found");
                &other_impls.data[id.as_index()]
            }
        }
    }

    /// Get a specific function from a given module.
    /// If necessary, the import slots are updated.
    pub fn get_function(
        &mut self,
        use_site: Location,
        module_path: &module::Path,
        function_name: Ustr,
    ) -> Result<FunctionId, InternalCompilationError> {
        let module = self.others.modules.get(module_path).ok_or_else(|| {
            internal_compilation_error!(Internal {
                error: format!(
                    "Module {module_path} not found when looking for function {function_name}"
                ),
                span: use_site
            })
        })?;
        module
            .get_unique_own_function(function_name)
            .ok_or_else(|| {
                internal_compilation_error!(Internal {
                    error: format!("Function {function_name} not found in module {module_path}"),
                    span: use_site
                })
            })?;
        Ok(FunctionId::Import(
            self.import_function(module_path, function_name),
        ))
    }

    /// Import a function from another module, possibly updating the import slots.
    /// The function is assumed to exist.
    fn import_function(
        &mut self,
        module_path: &module::Path,
        function_name: Ustr,
    ) -> ImportFunctionSlotId {
        self.import_fn_slots
            .iter()
            .position(|slot| slot.module == *module_path &&
                matches!(&slot.target, ImportFunctionTarget::NamedFunction(name) if *name == function_name)
            )
            .map(ImportFunctionSlotId::from_index)
            .unwrap_or_else(|| {
                let index = self.import_fn_slots.len();
                self.import_fn_slots.push(ImportFunctionSlot {
                    module: module_path.clone(),
                    target: ImportFunctionTarget::NamedFunction(function_name),
                    resolved: RefCell::new(None),
                });
                ImportFunctionSlotId::from_index(index)
            })
    }

    /// Import a trait impl method from another module, possibly updating the import slots.
    /// The trait impl is assumed to exist and the method index to be correct.
    fn import_impl_method(
        &mut self,
        module_path: &module::Path,
        key: TraitKey,
        method_index: u32,
    ) -> ImportFunctionSlotId {
        self.import_fn_slots
            .iter()
            .position(|slot| slot.module == *module_path &&
                matches!(&slot.target, ImportFunctionTarget::TraitImplMethod { key: k, index: i } if k == &key && *i == method_index)
            )
            .map(ImportFunctionSlotId::from_index)
            .unwrap_or_else(|| {
                let index = self.import_fn_slots.len();
                self.import_fn_slots.push(ImportFunctionSlot {
                    module: module_path.clone(),
                    target: ImportFunctionTarget::TraitImplMethod {
                        key,
                        index: method_index,
                    },
                    resolved: RefCell::new(None),
                });
                ImportFunctionSlotId::from_index(index)
            })
    }

    /// Import a trait impl dictionary from another module, possibly updating the import slots.
    /// The trait key is assumed to exist.
    fn import_impl_dictionary(
        &mut self,
        module_path: &module::Path,
        key: TraitKey,
    ) -> ImportImplSlotId {
        self.import_impl_slots
            .iter()
            .position(|slot| slot.module == *module_path && slot.key == key)
            .map(ImportImplSlotId::from_index)
            .unwrap_or_else(|| {
                let index = self.import_impl_slots.len();
                self.import_impl_slots.push(ImportImplSlot {
                    module: module_path.clone(),
                    key,
                    resolved: RefCell::new(None),
                });
                ImportImplSlotId::from_index(index)
            })
    }
}

impl<'a> Drop for TraitSolver<'a> {
    fn drop(&mut self) {
        if !self.fn_collector.new_elements.is_empty() {
            log::warn!(
                "TraitSolver dropped without committing the created functions. Call .commit() to store them in the module."
            );
        }
    }
}
