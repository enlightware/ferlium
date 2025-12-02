// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Module bundle system for incremental rebuilds and leak-free hot reloads
//!
//! This module implements the following architecture where:
//! - Each compiled module version is an Rc<Module>
//! - Cross-module references go through import slots + a relink step
//! - Call sites use local integer IDs for local calls or ImportFunctionSlotId/ImportTraitSlotId for external calls

pub mod function;
pub mod id;
pub mod module_env;
pub mod modules;
pub mod trait_impl;
pub mod uses;

pub use function::*;
pub use module_env::*;
pub use modules::*;
pub use trait_impl::*;
pub use uses::*;

use std::{
    cell::{Ref, RefCell, RefMut},
    collections::HashMap,
    fmt,
    hash::{DefaultHasher, Hash, Hasher},
};

use ustr::{Ustr, ustr};

use crate::{
    containers::SVec2,
    emit_ir::EmitTraitOutput,
    format::FormatWith,
    function::Function,
    ir::Node,
    r#trait::TraitRef,
    r#type::{Type, TypeAliases, TypeDefRef},
    value::Value,
};

// Module itself

/// Immutable module bundle containing all compiled module data
#[derive(Debug, Clone, Default)]
pub struct Module {
    pub import_fn_slots: Vec<ImportFunctionSlot>,
    pub import_impl_slots: Vec<ImportImplSlot>,

    pub uses: Uses,

    // Functions, including methods of concrete trait
    pub functions: Vec<LocalFunction>,
    pub function_name_to_id: HashMap<Ustr, LocalFunctionId>,

    // Type system content
    pub type_aliases: TypeAliases,
    pub type_defs: HashMap<Ustr, TypeDefRef>,
    pub traits: Traits,
    pub impls: TraitImpls,

    // Source info for IDE support
    pub source: Option<String>,
}

impl Module {
    /// Add a named function to this module, returning its ID.
    pub fn add_named_function(&mut self, name: Ustr, function: ModuleFunction) {
        self.add_function(Some(name), function);
    }

    /// Add a function to this module, returning its ID.
    pub fn add_function(
        &mut self,
        name: Option<Ustr>,
        function: ModuleFunction,
    ) -> LocalFunctionId {
        if let Some(name) = name {
            // FIXME: decide whether we want to allow that (useful for REPL?), but then we would leak
            assert!(!self.function_name_to_id.contains_key(&name));
        }
        let id = LocalFunctionId::from_index(self.functions.len());
        let interface_hash = function.definition.signature_hash();
        self.functions.push(LocalFunction {
            name,
            function,
            interface_hash,
        });
        if let Some(name) = name {
            self.function_name_to_id.insert(name, id);
        }
        id
    }

    /// Add a concrete trait implementation to this module, with raw functions.
    /// The definition will be retrieved by instantiating the trait method definitions with the given types.
    /// The caller is responsible to ensure that the input and output types match the trait reference
    /// and that the constraints are satisfied.
    pub fn add_concrete_impl(
        &mut self,
        trait_ref: TraitRef,
        input_tys: impl Into<Vec<Type>>,
        output_tys: impl Into<Vec<Type>>,
        functions: impl Into<Vec<Function>>,
    ) {
        // Add the impl, collecting new functions
        let mut fn_collector = FunctionCollector::new(self.functions.len());
        self.impls.add_concrete_raw(
            trait_ref,
            input_tys,
            output_tys,
            functions,
            &mut fn_collector,
        );
        self.functions.extend(fn_collector.new_elements);
    }

    /// Add a blanket trait implementation to this module, with raw functions.
    /// The definition will be retrieved by instantiating the trait method definitions with the given types.
    /// The caller is responsible to ensure that the input and output types match the trait reference
    /// and that the provided constraints are consistent with the trait definition.
    pub fn add_blanket_impl(
        &mut self,
        trait_ref: TraitRef,
        sub_key: BlanketTraitImplSubKey,
        output_tys: impl Into<Vec<Type>>,
        functions: impl Into<Vec<Function>>,
    ) {
        // Add the impl, collecting new functions
        let mut fn_collector = FunctionCollector::new(self.functions.len());
        self.impls
            .add_blanket_raw(trait_ref, sub_key, output_tys, functions, &mut fn_collector);
        self.functions.extend(fn_collector.new_elements);
    }

    /// Add a concrete or blanket trait implementation to this module, using already-added local functions.
    pub(crate) fn add_emitted_impl(
        &mut self,
        trait_ref: TraitRef,
        emit_output: EmitTraitOutput,
    ) -> LocalImplId {
        // TODO: ensure coherence

        let (dictionary_ty, interface_hash) = self.computer_interface_hash(&emit_output.functions);
        // Build and insert the implementation.
        let dictionary_value = RefCell::new(Value::unit()); // filled later in finalize
        let imp = TraitImpl::new(
            emit_output.output_tys,
            emit_output.functions,
            interface_hash,
            dictionary_value,
            dictionary_ty,
            true,
        );
        if emit_output.ty_var_count == 0 {
            let key = ConcreteTraitImplKey::new(trait_ref, emit_output.input_tys);
            self.impls.add_concrete_struct(key, imp)
        } else {
            let sub_key = BlanketTraitImplSubKey::new(
                emit_output.input_tys,
                emit_output.ty_var_count,
                emit_output.constraints,
            );
            self.impls
                .add_blanket_struct(BlanketTraitImplKey::new(trait_ref, sub_key), imp)
        }
    }

    fn computer_interface_hash(&self, function_ids: &[LocalFunctionId]) -> (Type, u64) {
        let mut interface_hasher = DefaultHasher::new();
        let tys: Vec<_> = function_ids
            .iter()
            .map(|id| {
                let local_fn = &self
                    .functions
                    .get(id.as_index())
                    .expect("Invalid function ID");
                local_fn.interface_hash.hash(&mut interface_hasher);
                let function = &local_fn.function;
                Type::function_type(function.definition.ty_scheme.ty.clone())
            })
            .collect();
        let hash = interface_hasher.finish();
        let dictionary_ty = Type::tuple(tys);
        (dictionary_ty, hash)
    }

    /// Check if this module is "empty" (has no meaningful content)
    pub fn is_empty(&self) -> bool {
        self.functions.is_empty()
            && self.import_fn_slots.is_empty()
            && self.type_aliases.is_empty()
            && self.type_defs.is_empty()
            && self.traits.is_empty()
            && self.impls.is_empty()
    }

    /// Return an iterator over the names of all own symbols (functions) in this module.
    pub fn own_symbols(&self) -> impl Iterator<Item = Ustr> + use<'_> {
        self.function_name_to_id
            .keys()
            .cloned()
            .chain(self.type_defs.keys().cloned())
            .chain(self.type_aliases.iter().map(|(name, _)| *name))
    }

    /// Return the type for the source pos, if any.
    pub fn type_at(&self, pos: usize) -> Option<Type> {
        for function in self.functions.iter() {
            let mut code = function.function.code.borrow_mut();
            let ty = code
                .as_script_mut()
                .and_then(|script_fn| script_fn.code.type_at(pos));
            if ty.is_some() {
                return ty;
            }
        }
        None
    }

    /// Return whether this module uses sym_name from mod_name.
    pub fn uses(&self, mod_name: Ustr, sym_name: Ustr) -> bool {
        self.uses.iter().any(|u| match u {
            Use::All(module) => *module == mod_name,
            Use::Some(some) => some.module == mod_name && some.symbols.contains(&sym_name),
        })
    }

    /// Look-up a function by name in this module or in any of the modules this module uses.
    pub fn get_function<'a>(
        &'a self,
        name: &'a str,
        others: &'a Modules,
    ) -> Option<&'a ModuleFunction> {
        self.get_member(name, others, &|name, module| {
            module.get_own_function(ustr(name))
        })
        .map(|(_, f)| f)
    }

    /// Look-up a member by name in this module or in any of the modules this module uses.
    /// Returns the module name if the member is from another module.
    /// The getter function is used to get the member from a module.
    pub fn get_member<'a, T>(
        &'a self,
        name: &'a str,
        others: &'a Modules,
        getter: &impl Fn(&'a str, &'a Self) -> Option<T>,
    ) -> Option<(Option<Ustr>, T)> {
        getter(name, self).map_or_else(
            || {
                self.uses.iter().find_map(|use_module| match use_module {
                    Use::All(module) => {
                        let module_ref = others.get(module)?;
                        getter(name, module_ref).map(|t| (Some(*module), t))
                    }
                    Use::Some(use_some) => {
                        if use_some.symbols.contains(&ustr(name)) {
                            let module = use_some.module;
                            let module_ref = others.get(&module)?;
                            getter(name, module_ref).map(|t| (Some(module), t))
                        } else {
                            None
                        }
                    }
                })
            },
            |t| Some((None, t)),
        )
    }

    /// Get a local function and its data by name
    pub fn get_local_function(&self, name: Ustr) -> Option<&LocalFunction> {
        let id = self.function_name_to_id.get(&name)?;
        self.functions.get(id.as_index())
    }

    /// Get a local function by name
    pub fn get_own_function(&self, name: Ustr) -> Option<&ModuleFunction> {
        self.get_local_function(name).map(|f| &f.function)
    }

    /// Get a mutable local function by name
    pub fn get_own_function_mut(&mut self, name: Ustr) -> Option<&mut ModuleFunction> {
        self.get_own_function_id_mut(name).map(|(_, f)| f)
    }

    /// Get a mutable local function and its ID by name
    pub fn get_own_function_id_mut(
        &mut self,
        name: Ustr,
    ) -> Option<(LocalFunctionId, &mut ModuleFunction)> {
        let id = self.function_name_to_id.get(&name)?;
        self.functions
            .get_mut(id.as_index())
            .map(|f| (*id, &mut f.function))
    }

    /// Look-up a function by name only in this module and return its script node, if it is a script function.
    pub fn get_own_function_node(&mut self, name: Ustr) -> Option<Ref<'_, Node>> {
        self.get_own_function(name)?.get_node()
    }

    /// Look-up a function by name only in this module and return its mutable script node, if it is a script function.
    pub fn get_own_function_node_mut(&mut self, name: Ustr) -> Option<RefMut<'_, Node>> {
        self.get_own_function_mut(name)?.get_node_mut()
    }

    /// Get a local function by ID
    pub fn get_own_function_by_id(&self, id: LocalFunctionId) -> Option<&ModuleFunction> {
        self.functions.get(id.as_index()).map(|f| &f.function)
    }

    /// Get an import slot by ID
    pub fn get_import_slot(&self, slot_id: ImportFunctionSlotId) -> Option<&ImportFunctionSlot> {
        self.import_fn_slots.get(slot_id.as_index())
    }

    /*
    /// Check if this module's interface is compatible with another (i.e., no dependents need recompilation).
    /// Uses hash collision detection and looks up actual function data when hashes match.
    pub fn is_interface_compatible_with(&self, other: &Self) -> bool {
        // 1. Functions: Check if all functions that existed before are still compatible.
        for other_fn in &other.functions {
            match self
                .functions
                .iter()
                .find(|this_fn| this_fn.name == other_fn.name)
            {
                Some(this_fn) => {
                    if this_fn.interface_hash != other_fn.interface_hash {
                        return false; // Interface definitely changed
                    }
                    // Hash collision detection: if hashes match, verify actual signatures
                    if this_fn.function.definition.signature()
                        != other_fn.function.definition.signature()
                    {
                        return false; // Hash collision - signatures actually differ
                    }
                }
                None => return false, // Symbol was removed
            }
        }

        // 2. Concrete trait implementations: ensure previously exported impls remain compatible.
        for (other_key, other_impl_id) in other.impls.concrete().iter() {
            // Find matching impl by trait name and TraitReq value, as currently it is stable.
            let maybe_this = self
                .impls
                .concrete()
                .iter()
                .find(|(this_key, _)| *this_key == other_key);

            let Some((_, this_impl_id)) = maybe_this else {
                return false; // Previously available impl no longer exists
            };

            // Compare method interface hashes (same order as functions)
            let this_impl = &self.impls.data[this_impl_id.as_index()];
            let other_impl = &other.impls.data[other_impl_id.as_index()];
            if this_impl.interface_hash != other_impl.interface_hash {
                return false; // Method interfaces changed
            }
            // Has hash matches, verify actual signatures
            for (this_f_id, other_f_id) in this_impl.methods.iter().zip(other_impl.methods.iter()) {
                let this_f = &self.functions[this_f_id.as_index()];
                let other_f = &other.functions[other_f_id.as_index()];
                if this_f.function.definition.signature() != other_f.function.definition.signature()
                {
                    return false; // Hash collision - signatures actually differ
                }
            }

            // Compare output types (associated/derived outputs)
            if this_impl.output_tys != other_impl.output_tys {
                return false; // Output types changed
            }
        }

        // 3. Blanket trait implementations: ensure previously exported impls remain compatible.
        todo!("check blanket impls");

        true // All existing symbols and impls are compatible (new ones are OK)
    }
    */

    fn format_with_modules(
        &self,
        f: &mut fmt::Formatter,
        modules: &Modules,
        show_details: bool,
    ) -> fmt::Result {
        let env = ModuleEnv::new(self, modules, false);
        if !self.uses.is_empty() {
            writeln!(f, "Use directives ({}):", self.uses.len())?;
            for use_module in self.uses.iter() {
                match use_module {
                    Use::All(module) => writeln!(f, "  {module}: *")?,
                    Use::Some(use_some) => {
                        write!(f, "  {}:", use_some.module)?;
                        for symbol in use_some.symbols.iter() {
                            write!(f, " {symbol}")?;
                        }
                        writeln!(f)?;
                    }
                }
            }
            writeln!(f, "\n")?;
        }
        if !self.type_aliases.is_empty() {
            writeln!(f, "Type aliases ({}):\n", self.type_aliases.len())?;
            for (name, ty) in self.type_aliases.iter() {
                writeln!(f, "{}: {}", name, ty.format_with(&env))?;
            }
            writeln!(f, "\n")?;
        }
        if !self.type_defs.is_empty() {
            writeln!(f, "New types ({}):\n", self.type_defs.len())?;
            for (_, decl) in self.type_defs.iter() {
                write!(f, "  ")?;
                decl.format_details(&env, f)?;
                writeln!(f)?;
            }
            writeln!(f, "\n")?;
        }
        if !self.traits.is_empty() {
            writeln!(f, "Traits ({}):\n", self.traits.len())?;
            for trait_ref in self.traits.iter() {
                writeln!(f, "{}", trait_ref.format_with(&env))?;
            }
            writeln!(f)?;
        }
        if !self.impls.is_empty() {
            writeln!(f, "Trait implementations ({}):\n", self.impls.len())?;
            let level = if show_details {
                DisplayFilter::MethodCode
            } else {
                DisplayFilter::MethodDefinitions
            };
            let filter = |_: &TraitRef, _: LocalImplId| level;
            self.impls.fmt_with_filter(f, &env, filter)?;
        }
        if !self.functions.is_empty() {
            let named_count = self.functions.iter().filter(|f| f.name.is_some()).count();
            writeln!(f, "Named functions ({}):\n", named_count)?;
            for (i, LocalFunction { name, function, .. }) in self.functions.iter().enumerate() {
                if name.is_none() {
                    continue;
                }
                function
                    .definition
                    .fmt_with_name_and_module_env(f, name, "", &env)?;
                writeln!(f, " (#{i})")?;
                if show_details {
                    function.fmt_code(f, &env)?;
                    writeln!(f)?;
                }
            }
            let unnamed_count = self.functions.len() - named_count;
            if unnamed_count > 0 {
                writeln!(f, "\nNot showing {} unnamed functions.", unnamed_count)?;
            }
        }
        Ok(())
    }

    pub fn list_stats(&self) -> String {
        let mut stats = String::new();
        if !self.uses.is_empty() {
            stats.push_str(&format!("use directives: {}", self.uses.len()));
        }
        if !self.type_aliases.is_empty() {
            if !stats.is_empty() {
                stats.push_str(", ");
            }
            stats.push_str(&format!("type aliases: {}", self.type_aliases.len()));
        }
        if !self.type_defs.is_empty() {
            if !stats.is_empty() {
                stats.push_str(", ");
            }
            stats.push_str(&format!("new types: {}", self.type_defs.len()));
        }
        if !self.traits.is_empty() {
            if !stats.is_empty() {
                stats.push_str(", ");
            }
            stats.push_str(&format!("traits: {}", self.traits.len()));
        }
        if !self.impls.is_empty() {
            if !stats.is_empty() {
                stats.push_str(", ");
            }
            stats.push_str(&format!("trait implementations: {}", self.impls.len()));
        }
        if !self.functions.is_empty() {
            if !stats.is_empty() {
                stats.push_str(", ");
            }
            let named_count = self.functions.iter().filter(|f| f.name.is_some()).count();
            stats.push_str(&format!("named functions: {}", named_count));
            if self.functions.len() > named_count {
                let unnamed_count = self.functions.len() - named_count;
                stats.push_str(&format!(", unnamed functions: {}", unnamed_count));
            }
        }
        stats
    }
}

/// Finalize the module:
/// - Build dictionary values for trait implementations.
/// - Resolve pending function values inside the module by attaching the module's weak reference.
pub fn finalize_module(module_rc: &ModuleRc) {
    for local_fn in &module_rc.functions {
        let mut fn_mut = local_fn.function.code.borrow_mut();
        if let Some(script_fn) = fn_mut.as_script_mut() {
            script_fn.code.finalize_pending_values(module_rc);
        }
    }
    for imp in &module_rc.impls.data {
        let mut value = imp.dictionary_value.borrow_mut();
        let values = imp
            .methods
            .iter()
            .map(|fn_id| {
                let local_fn = &module_rc.functions[fn_id.as_index()];
                let code = local_fn.function.code.clone();
                Value::PendingFunction(code.clone())
            })
            .collect::<SVec2<_>>();
        *value = Value::tuple(values);
        value.finalize_pending(module_rc);
    }
}

impl FormatWith<Modules> for Module {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, data: &Modules) -> fmt::Result {
        self.format_with_modules(f, data, false)
    }
}

pub struct ShowModuleDetails<'a>(pub &'a Modules);

impl FormatWith<ShowModuleDetails<'_>> for Module {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, data: &ShowModuleDetails) -> fmt::Result {
        self.format_with_modules(f, data.0, true)
    }
}

impl FormatWith<ModuleEnv<'_>> for LocalFunction {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        self.function
            .definition
            .fmt_with_name_and_module_env(f, &self.name, "", env)?;
        self.function.code.borrow().format_ind(f, env, 1, 1)
    }
}
