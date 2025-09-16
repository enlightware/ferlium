// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::{cell::RefCell, collections::HashSet, rc::Rc};

use derive_new::new;
use ustr::Ustr;

use crate::{
    containers::b,
    effects::EffType,
    error::InternalCompilationError,
    function::ScriptFunction,
    internal_compilation_error,
    ir::Node,
    ir_syn::{get_dictionary, load, static_apply},
    module::{
        BlanketTraitImplKey, BlanketTraitImpls, ConcreteTraitImplKey, FunctionCollector,
        FunctionId, ImportFunctionSlot, ImportFunctionSlotId, ImportFunctionTarget, ImportImplSlot,
        ImportImplSlotId, LocalFunction, ModuleEnv, ModuleFunction, Modules, TraitImpl,
        TraitImplId, TraitImpls, TraitKey,
    },
    mutability::MutType,
    r#trait::TraitRef,
    r#type::{FnArgType, Type},
    std::{core::REPR_TRAIT, new_module_using_std},
    type_inference::UnifiedTypeInference,
    type_like::TypeLike,
    type_visitor::AllVarsCollector,
    value::Value,
    Location,
};

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
    pub fn commit(self, functions: &mut Vec<LocalFunction>) {
        functions.extend(self.fn_collector.new_elements);
    }

    /// Check if a concrete trait implementation exists, without performing any solving.
    /// This searches in current module first, then in other modules.
    /// Only public implementations from other modules are considered.
    pub fn has_concrete_impl(&self, key: &ConcreteTraitImplKey) -> bool {
        self.impls.concrete_key_to_id.contains_key(key)
            || self
                .others
                .modules
                .iter()
                .find(|(_, m)| {
                    let id = m.impls.concrete_key_to_id.get(key);
                    if let Some(id) = id {
                        let imp = &m.impls.data[id.as_index()];
                        imp.public
                    } else {
                        false
                    }
                })
                .is_some()
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
                self.others.modules.iter().find_map(|(name, m)| {
                    m.impls.concrete_key_to_id.get(key).and_then(|id| {
                        let imp = &m.impls.data[id.as_index()];
                        if imp.public {
                            Some(TraitImplId::Import(self.import_impl_dictionary(
                                *name,
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
    ) -> impl Iterator<Item = (Option<Ustr>, &'b BlanketTraitImpls)> {
        self.impls
            .blanket_key_to_id
            .get(trait_ref)
            .map(|blankets| (None, blankets))
            .into_iter()
            .chain(self.others.modules.iter().flat_map(|(name, m)| {
                m.impls
                    .blanket_key_to_id
                    .get(trait_ref)
                    .map(|imp| (Some(*name), imp))
            }))
    }

    /// Print all known implementations for the given trait reference.
    fn print_impls(&self, trait_ref: &TraitRef) {
        println!("In current module:\n\n");
        let fake_current = new_module_using_std();
        let env = ModuleEnv::new(&fake_current, self.others);
        self.impls.print_impls_headers(trait_ref, env);
        for (module_name, module) in &self.others.modules {
            if let Some(_) = module.impls.blanket_key_to_id.get(trait_ref) {
                println!("In module {}:\n\n", module_name);
                module.impls.print_impls_headers(trait_ref, env);
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
            .map(|(mod_name, blankets)| (mod_name, blankets.clone()))
            .collect::<Vec<_>>();
        // Then we iterate over all blanket implementations, trying to unify their input types
        for (imp_mod_name, blanket_impls) in blankets {
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
                let mut constraint_dict_ids = Vec::new();
                // Note: we assume the constraints are ordered by dependency so that the output types
                // of one are the input types of the next.
                for constraint in imp_constraints.iter() {
                    let (trait_ref, input_tys, output_tys, _span) = ty_inf
                        .substitute_in_constraint(constraint)
                        .into_have_trait()
                        .expect("Non trait constraint in blanket impl");
                    assert!(input_tys.iter().all(Type::is_constant));
                    let new_output_tys =
                        self.solve_output_types(&trait_ref, &input_tys, fn_span)?;
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

                    let dict_id = self.solve_impl(&trait_ref, &input_tys, fn_span);
                    let dict_id = match dict_id {
                        Ok(functions) => functions,
                        // Failed? Try next implementation.
                        Err(_) => continue 'impl_loop,
                    };
                    constraint_dict_ids.push(dict_id);
                }

                // Succeeded? First get the blanket implementation data and compute the output types.
                let impls = if let Some(module_name) = imp_mod_name {
                    &self.others.modules[&module_name].impls
                } else {
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

                // Then, for every function in the implementation, create a thunk function closing over
                // the constraint dictionaries.
                let trait_key =
                    TraitKey::Blanket(BlanketTraitImplKey::new(trait_ref.clone(), sub_key.clone()));
                let definitions = trait_ref.instantiate_for_tys(input_tys, &output_tys);
                let functions = imp.methods.clone(); // clone to avoid borrowing issues
                let functions = functions
                    .iter()
                    .zip(definitions.into_iter())
                    .enumerate()
                    .map(|(method_index, (fn_id, def))| {
                        // Get the function id for doing the call to the generic function.
                        let function_id = match imp_mod_name {
                            Some(module_name) => {
                                let slot_id = self.import_impl_method(
                                    module_name,
                                    trait_key.clone(),
                                    method_index as u32,
                                );
                                FunctionId::Import(slot_id)
                            }
                            None => FunctionId::Local(*fn_id),
                        };

                        // TODO: only build the thunk if there are constraint dictionaries.

                        // Build the arguments for the call: first the constraint dictionaries, then the original arguments.
                        let arguments = constraint_dict_nodes
                            .iter()
                            .cloned()
                            .chain(def.ty_scheme.ty.args.iter().enumerate().map(
                                |(arg_i, arg_ty)| {
                                    Node::new(load(arg_i), arg_ty.ty, EffType::empty(), fn_span)
                                },
                            ))
                            .collect();

                        // Build the application node.
                        let mut fn_ty = def.ty_scheme.ty.clone();
                        fn_ty.args.splice(
                            0..0,
                            constraint_dict_nodes
                                .iter()
                                .map(|n| FnArgType::new(n.ty, MutType::constant())),
                        );
                        let apply = static_apply(function_id, fn_ty, fn_span, arguments);
                        let code = b(ScriptFunction::new(
                            Node::new(apply, def.ty_scheme.ty.ret, EffType::empty(), fn_span),
                            def.arg_names.clone(),
                        ));
                        ModuleFunction::new_without_spans(def, Rc::new(RefCell::new(code)))
                    })
                    .collect::<Vec<_>>();

                // Store the functions as a new concrete implementation, and return its id.
                let local_impl_id = self.impls.add_concrete(
                    trait_ref.clone(),
                    input_tys.to_vec(),
                    output_tys,
                    functions,
                    &mut self.fn_collector,
                );
                return Ok(TraitImplId::Local(local_impl_id));
            }
        }

        // No blanket implementation found, look for a derived implementation.
        for derive in &trait_ref.derives {
            if let Some(impl_id) = derive.derive_impl(trait_ref, input_tys, fn_span, self)? {
                return Ok(impl_id);
            } else {
                println!(
                    "Tried derivation for trait {} with input types {:?}, but failed.",
                    trait_ref.name, input_tys
                );
            }
        }

        // No matching implementation found.
        println!("Existing impls for {}:\n", trait_ref.name);
        self.print_impls(trait_ref);
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
                let module_name = slot.module_name;
                let key = slot.key.as_concrete().unwrap();
                let key = TraitKey::Concrete(key.clone());
                FunctionId::Import(self.import_impl_method(module_name, key, index as u32))
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
                let module_name = slot.module_name;
                let key = slot.key.as_concrete().unwrap();
                let other_impls = &self
                    .others
                    .modules
                    .get(&module_name)
                    .expect("imported module not found")
                    .impls;
                let id = other_impls
                    .concrete_key_to_id
                    .get(&key)
                    .expect("imported trait impl not found");
                &other_impls.data[id.as_index()]
            }
        }
    }

    /// Get a specific function from a given module.
    /// If necessary, the import slots are updated.
    pub fn get_function(
        &mut self,
        module_name: Ustr,
        function_name: Ustr,
    ) -> Result<FunctionId, InternalCompilationError> {
        let module = self.others.modules.get(&module_name).ok_or_else(|| {
            internal_compilation_error!(Internal(format!(
                "Module {module_name} not found when looking for function {function_name}"
            )))
        })?;
        module.get_own_function(function_name).ok_or_else(|| {
            internal_compilation_error!(Internal(format!(
                "Function {function_name} not found in module {module_name}"
            )))
        })?;
        Ok(FunctionId::Import(
            self.import_function(module_name, function_name),
        ))
    }

    /// Import a function from another module, possibly updating the import slots.
    /// The function is assumed to exist.
    fn import_function(&mut self, module_name: Ustr, function_name: Ustr) -> ImportFunctionSlotId {
        self.import_fn_slots
            .iter()
            .position(|slot| slot.module_name == module_name &&
                matches!(&slot.target, ImportFunctionTarget::NamedFunction(name) if *name == function_name)
            )
            .map(|index| ImportFunctionSlotId::from_index(index))
            .unwrap_or_else(|| {
                let index = self.import_fn_slots.len();
                self.import_fn_slots.push(ImportFunctionSlot {
                    module_name,
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
        module_name: Ustr,
        key: TraitKey,
        method_index: u32,
    ) -> ImportFunctionSlotId {
        self.import_fn_slots
            .iter()
            .position(|slot| slot.module_name == module_name &&
                matches!(&slot.target, ImportFunctionTarget::TraitImplMethod { key: k, index: i } if k == &key && *i == method_index)
            )
            .map(|index| ImportFunctionSlotId::from_index(index))
            .unwrap_or_else(|| {
                let index = self.import_fn_slots.len();
                self.import_fn_slots.push(ImportFunctionSlot {
                    module_name,
                    target: ImportFunctionTarget::TraitImplMethod {
                        key: key,
                        index: method_index,
                    },
                    resolved: RefCell::new(None),
                });
                ImportFunctionSlotId::from_index(index)
            })
    }

    /// Import a trait impl dictionary from another module, possibly updating the import slots.
    /// The trait key is assumed to exist.
    fn import_impl_dictionary(&mut self, module_name: Ustr, key: TraitKey) -> ImportImplSlotId {
        self.import_impl_slots
            .iter()
            .position(|slot| slot.module_name == module_name && slot.key == key)
            .map(|index| ImportImplSlotId::from_index(index))
            .unwrap_or_else(|| {
                let index = self.import_impl_slots.len();
                self.import_impl_slots.push(ImportImplSlot {
                    module_name,
                    key,
                    resolved: RefCell::new(None),
                });
                ImportImplSlotId::from_index(index)
            })
    }
}
