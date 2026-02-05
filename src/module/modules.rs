// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::rc::Weak;
use std::{collections::HashMap, rc::Rc};

use crate::module::Module;
use crate::module::path::Path;
use crate::module::{ImportFunctionTarget, TraitKey};

/// Arc-wrapped module bundle for sharing between threads
pub type ModuleRc = Rc<Module>;
/// Weak reference to a module bundle
pub type ModuleWeak = Weak<Module>;

/// A reference to a module
#[derive(Clone)]
pub enum ModuleRef {
    /// Strong references are used for third parties holding on to a module
    Strong(ModuleRc),
    /// Weak references are used to avoid cycles within a module itself
    Weak(ModuleWeak),
}

// dependee -> list of dependents
//type Dependencies = HashMap<Ustr, Vec<Ustr>>;

/// Registry of all modules in the world
#[derive(Debug, Clone, Default)]
pub struct Modules {
    /// Map from module name to the latest module
    pub(crate) modules: HashMap<Path, ModuleRc>,
}

impl Modules {
    pub fn new_empty() -> Self {
        Self::default()
    }

    pub fn get(&self, path: &Path) -> Option<&ModuleRc> {
        self.modules.get(path)
    }

    /// Non-incremental linking of all import slots in a module
    pub fn link(&self, module: &ModuleRc) {
        // Link functions.
        for (slot_index, slot) in module.iter_import_fn_slots().enumerate() {
            if slot.resolved.borrow().is_some() {
                continue; // Already linked
            }
            if let Some(target_module) = self.modules.get(&slot.module) {
                let (function, hash) = match &slot.target {
                    ImportFunctionTarget::NamedFunction(function_name) => {
                        if let Some(target_function) =
                            target_module.get_local_function(*function_name)
                        {
                            (
                                &target_function.function.code,
                                target_function.interface_hash,
                            )
                        } else {
                            panic!(
                                "Function {} not found in module {}",
                                function_name, slot.module
                            );
                        }
                    }
                    ImportFunctionTarget::TraitImplMethod { key, index } => {
                        // Get the impl identifier.
                        let impl_id = match key {
                            TraitKey::Concrete(key) => target_module
                                .get_concrete_impl_by_key(key)
                                .expect("Concrete trait impl not found in target module"),
                            TraitKey::Blanket(key) => target_module
                                .get_blanket_impl_by_key(&key.trait_ref)
                                .expect("Blanket trait not found in target module")
                                .get(&key.sub_key)
                                .expect("Blanket trait impl sub-key not found in target module"),
                        };
                        // Extract the method function by index from the tuple.
                        let imp = target_module.get_impl_data(*impl_id).unwrap();
                        let fn_id = imp.methods[*index as usize];
                        let local_fn = &target_module.get_local_function_by_id(fn_id).unwrap();
                        (&local_fn.function.code, local_fn.interface_hash)
                    }
                };
                *slot.resolved.borrow_mut() = Some((function.clone(), target_module.clone(), hash));
            } else {
                panic!(
                    "Module {} not found for import function slot {}",
                    slot.module, slot_index
                );
            }
        }

        // Link impl dictionaries
        for (slot_index, slot) in module.import_impl_slots.iter().enumerate() {
            if slot.resolved.borrow().is_some() {
                continue; // Already linked
            }
            if let Some(target_module) = self.modules.get(&slot.module) {
                let imp = target_module
                    .get_impl_data_by_trait_key(&slot.key)
                    .expect("Trait impl not found in target module for import impl slot");
                *slot.resolved.borrow_mut() = Some((
                    imp.dictionary_value.borrow().clone(),
                    target_module.clone(),
                    imp.interface_hash,
                ));
            } else {
                panic!(
                    "Module {} not found for import impl slot {}",
                    slot.module, slot_index
                );
            }
        }
    }

    /// Register a new module bundle
    pub fn register_module(&mut self, path: Path, module: Module) {
        self.register_module_rc(path, Rc::new(module));
    }

    /// Register a new module bundle
    pub fn register_module_rc(&mut self, path: Path, module: ModuleRc) {
        self.modules.insert(path, module.clone());
    }

    /*
    /// Register a new module bundle, potentially replacing an older version
    pub fn register_module(&mut self, module_name: Ustr, mut module: Module) -> RelinkResult {
        // Increment version if this is a recompilation of an existing module
        if let Some(old_bundle) = self.modules.get(&module_name) {
            module.version = old_bundle.version + 1;
        }

        let new_bundle = Rc::new(module);

        // Check if we need to relink dependents
        let needs_relink = if let Some(old_bundle) = self.modules.get(&module_name) {
            !new_bundle.is_interface_compatible_with(&old_bundle)
        } else {
            false // New module, no dependents to relink yet
        };

        // Register the new bundle
        self.modules.insert(module_name, new_bundle.clone());

        // Build list of modules that need relinking
        let mut modules_to_relink = Vec::new();
        if needs_relink {
            // Automatically recompute all dependencies based on import slots
            let dependencies = self.compute_dependencies();
            if let Some(dependents) = dependencies.get(&module_name) {
                modules_to_relink.extend(dependents.clone());
            }
        }

        RelinkResult {
            new_bundle,
            modules_to_relink,
        }
    }

    /// Automatically compute and update all dependency relationships
    /// based on import slots in registered modules
    fn compute_dependencies(&self) -> Dependencies {
        let mut dependencies: Dependencies = HashMap::new();
        for (module_name, module) in &self.modules {
            for slot in &module.import_fn_slots {
                // Record that this module depends on the imported module
                dependencies
                    .entry(slot.module_name)
                    .or_default()
                    .push(*module_name);
            }
        }
        dependencies
    }
    */

    /// Get a module bundle by name
    pub fn get_module(&self, path: &Path) -> Option<ModuleRc> {
        self.modules.get(path).cloned()
    }

    /// Get the name of a registered module
    pub fn get_module_path(&self, module: &ModuleRc) -> Option<Path> {
        for (path, m) in &self.modules {
            if Rc::ptr_eq(m, module) {
                return Some(path.clone());
            }
        }
        None
    }

    /// List all registered modules
    pub fn list_modules(&self) -> Vec<Path> {
        self.modules.keys().cloned().collect()
    }

    /// Check if this program has any modules (used by ModuleRelinker)
    pub fn is_empty(&self) -> bool {
        self.modules.is_empty()
    }
}

/*

/// Result of registering a new module bundle
#[derive(Debug, Clone)]
pub struct RelinkResult {
    /// The newly registered bundle
    pub new_bundle: ModuleRc,
    /// List of modules that need relinking due to interface changes
    pub modules_to_relink: Vec<Ustr>,
}

/// Relinker that updates import slots when modules are recompiled
#[derive(Debug, new)]
pub struct ModuleRelinker<'a> {
    registry: &'a Modules,
}

impl<'a> ModuleRelinker<'a> {
    pub fn needs_recompilation(&self) -> bool {
        self.registry.has_modules()
    }

    /// Relink all import slots in a module bundle
    pub fn relink_module(&self, module: &Module) -> RelinkStatus {
        let mut updated_slots = Vec::new();
        let mut missing_dependencies = Vec::new();

        // Relink functions.
        for (slot_index, slot) in module.import_fn_slots.iter().enumerate() {
            if let Some(target_module) = self.registry.get_module(slot.module_name) {
                match &slot.target {
                    ImportFunctionTarget::NamedFunction(function_name) => {
                        if let Some(target_function) =
                            target_module.get_local_function(*function_name)
                        {
                            updated_slots.push(RelinkedSlot {
                                slot_id: ImportFunctionSlotId(slot_index as u32),
                                resolved_function: target_function.function.code.clone(),
                                new_interface_hash: target_function.interface_hash,
                            });
                        } else {
                            missing_dependencies.push(MissingDependency {
                                slot_id: ImportFunctionSlotId(slot_index as u32),
                                module_name: slot.module_name,
                                function_name: *function_name,
                                reason: MissingDependencyReason::FunctionNotFound,
                            });
                        }
                    }
                    ImportFunctionTarget::TraitImplMethod { key, index, .. } => {
                        // Search for a matching concrete impl by (trait name, input types)
                        let mut found_fn_rc = None;
                        for (check_key, id) in target_module.impls.concrete().iter() {
                            if key == check_key {
                                // Extract the method function by index from the tuple
                                let imp = &target_module.impls.data[id.as_index()];
                                let fn_id = imp.methods[*index as usize];
                                let local_fn = &target_module.functions[fn_id.as_index()];
                                found_fn_rc =
                                    Some((local_fn.function.code.clone(), local_fn.interface_hash));
                                break;
                            }
                        }

                        if let Some((fn_rc, hash)) = found_fn_rc {
                            updated_slots.push(RelinkedSlot {
                                slot_id: ImportFunctionSlotId(slot_index as u32),
                                resolved_function: fn_rc,
                                new_interface_hash: hash,
                            });
                        } else {
                            missing_dependencies.push(MissingDependency {
                                slot_id: ImportFunctionSlotId(slot_index as u32),
                                module_name: slot.module_name,
                                function_name: ustr::ustr("<trait impl method>"),
                                reason: MissingDependencyReason::FunctionNotFound,
                            });
                        }
                    }
                }
            } else {
                let function_name = match &slot.target {
                    ImportFunctionTarget::NamedFunction(function_name) => *function_name,
                    ImportFunctionTarget::TraitImplMethod { .. } => {
                        ustr::ustr("<trait impl method>")
                    }
                };
                missing_dependencies.push(MissingDependency {
                    slot_id: ImportFunctionSlotId(slot_index as u32),
                    module_name: slot.module_name,
                    function_name,
                    reason: MissingDependencyReason::ModuleNotFound,
                });
            }
        }

        RelinkStatus {
            updated_slots,
            missing_dependencies,
        }
    }
}

#[derive(Debug, Clone)]
pub struct RelinkedSlot {
    pub slot_id: ImportFunctionSlotId,
    pub resolved_function: FunctionRc,
    pub new_interface_hash: u64,
}

#[derive(Debug, Clone)]
pub enum MissingDependencyReason {
    ModuleNotFound,
    FunctionNotFound,
}

#[derive(Debug, Clone)]
pub struct MissingDependency {
    pub slot_id: ImportFunctionSlotId,
    pub module_name: Ustr,
    pub function_name: Ustr,
    pub reason: MissingDependencyReason,
}

#[derive(Debug, Clone)]
pub struct RelinkStatus {
    pub updated_slots: Vec<RelinkedSlot>,
    pub missing_dependencies: Vec<MissingDependency>,
}
*/
