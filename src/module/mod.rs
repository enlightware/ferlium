// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

//! Module bundle system for incremental rebuilds and leak-free hot reloads
//!
//! This module implements the following architecture where:
//! - Each compiled module version is an Rc<Module>
//! - Cross-module references go through import slots + a relink step
//! - Call sites use local integer IDs for local calls or ImportFunctionSlotId/ImportTraitSlotId for external calls

pub mod function;
pub mod id;
pub mod module_env;
pub mod path;
pub mod trait_impl;
pub mod uses;

use enum_as_inner::EnumAsInner;
pub use function::*;
pub use module_env::*;
pub use path::*;
pub use trait_impl::*;
pub use uses::*;

use std::{
    cell::{Ref, RefMut},
    fmt,
    hash::Hash,
};

use ustr::{Ustr, ustr};

use crate::{
    Location, define_id_type,
    emit_ir::EmitTraitOutput,
    error::{ImportKind, ImportSite, InternalCompilationError},
    format::FormatWith,
    function::Function,
    internal_compilation_error,
    ir::Node,
    module::id::{Id, NamedIndexed},
    r#trait::TraitRef,
    r#type::{LocalTypeAliasId, Type, TypeAliases, TypeDefRef},
    value::build_dictionary_value,
};

define_id_type!(
    /// ID of a module within a CompilerSession
    ModuleId
);

define_id_type!(
    /// ID of a definition within a module
    LocalDefId
);

/// A reference to a definition, consisting of the module ID and the definition index within that module.
pub type DefId = (ModuleId, LocalDefId);

define_id_type!(
    /// ID of a type definition within a module
    LocalTypeDefId
);

define_id_type!(
    /// ID of a trait definition within a module
    LocalTraitId
);

/// All possible kinds of definitions within a module
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, EnumAsInner)]
pub enum DefKind {
    Function(LocalFunctionId),
    TypeDef(LocalTypeDefId),
    TypeAlias(LocalTypeAliasId),
    Trait(LocalTraitId),
    // Impl(LocalImplId), currently not accessed by name, if we want to add it, we must take care in trait solver to register the ones it adds
}

pub type DefTable = NamedIndexed<Ustr, LocalDefId, DefKind>;

// Module itself

/// Once-built immutable module bundle containing all compiled module data
/// Items are conceptually private, but some are pub(crate) for lifetime constraints.
/// These are only accessed directly by emit_ir and trait_solver, other users should go through accessors,
/// with the exception of uses which is also accessed directly by desugar.
#[derive(Debug, Clone)]
pub struct Module {
    pub(crate) import_fn_slots: Vec<ImportFunctionSlot>,
    pub(crate) import_impl_slots: Vec<ImportImplSlot>,

    pub(crate) uses: Uses,

    /// All symbols defined in this module
    pub(crate) def_table: DefTable,

    // Functions, including methods of trait implementations.
    pub(crate) functions: Vec<ModuleFunction>,

    // Type system content
    type_aliases: TypeAliases,
    type_defs: Vec<TypeDefRef>,
    traits: Traits,
    pub(crate) impls: TraitImpls,
}

impl Module {
    /// Create a new empty module with the given ID, store the id in impls for later use.
    pub fn new(module_id: ModuleId) -> Self {
        Self {
            import_fn_slots: Vec::new(),
            import_impl_slots: Vec::new(),
            uses: Uses::default(),
            def_table: DefTable::new(),
            functions: Vec::new(),
            type_aliases: TypeAliases::default(),
            type_defs: Vec::new(),
            traits: Traits::new(),
            impls: TraitImpls::new(module_id),
        }
    }

    /// Get this module's ID.
    pub fn module_id(&self) -> ModuleId {
        self.impls.module_id
    }

    // Imports

    /// Get a function import slot by ID
    pub fn get_import_fn_slot(&self, slot_id: ImportFunctionSlotId) -> Option<&ImportFunctionSlot> {
        self.import_fn_slots.get(slot_id.as_index())
    }

    /// Iterate over all function import slots in this module.
    pub fn iter_import_fn_slots(&self) -> impl Iterator<Item = &ImportFunctionSlot> {
        self.import_fn_slots.iter()
    }

    /// Return the number of function import slots in this module.
    pub fn import_fn_slot_count(&self) -> usize {
        self.import_fn_slots.len()
    }

    /// Get a trait implementation import slot by ID
    pub fn get_import_impl_slot(&self, slot_id: ImportImplSlotId) -> Option<&ImportImplSlot> {
        self.import_impl_slots.get(slot_id.as_index())
    }

    // Uses

    /// Add an explicit use of a symbol from another module.
    pub fn add_explicit_use(&mut self, sym_name: Ustr, module: Path, span: Location) {
        self.uses
            .explicits
            .insert(sym_name, UseData::new(module, span));
    }

    /// Add a wildcard use of another module.
    pub fn add_wildcard_use(&mut self, module: Path, span: Location) {
        self.uses.wildcards.push(UseData::new(module, span));
    }

    /// Return whether this module uses sym_name from mod_name.
    pub fn uses(&self, mod_path: &Path, sym_name: Ustr) -> bool {
        self.uses
            .explicits
            .get(&sym_name)
            .is_some_and(|use_data| use_data.module == *mod_path)
            || self.uses.wildcards.iter().any(|u| u.module == *mod_path)
    }

    // Functions

    /// Add a function to this module, returning its ID.
    pub fn add_function(&mut self, name: Ustr, function: ModuleFunction) -> LocalFunctionId {
        let id = LocalFunctionId::from_index(self.functions.len());
        self.functions.push(function);
        self.def_table.insert(name, DefKind::Function(id));
        id
    }

    /// Add an anonymous function to this module, returning its ID.
    /// The function can be named later using `name_function`.
    pub(crate) fn add_function_anonymous(&mut self, function: ModuleFunction) -> LocalFunctionId {
        let id = LocalFunctionId::from_index(self.functions.len());
        self.functions.push(function);
        id
    }

    /// Name a previously added anonymous function.
    pub(crate) fn name_function(&mut self, id: LocalFunctionId, new_name: Ustr) {
        self.def_table.insert(new_name, DefKind::Function(id));
    }

    /// Add collected functions from a FunctionCollector to this module.
    pub fn add_collected_functions(&mut self, collector: FunctionCollector) {
        let start_id = self.functions.len();
        let functions =
            collector
                .new_elements
                .into_iter()
                .enumerate()
                .map(|(i, (name, function))| {
                    let local_id = LocalFunctionId::from_index(start_id + i);
                    self.def_table.insert(name, DefKind::Function(local_id));
                    function
                });
        self.functions.extend(functions);
    }

    /// Check if a local function name is unique in this module.
    pub fn is_non_trait_local_function(&self, name: Ustr) -> bool {
        !name.contains(">::")
    }

    /// Get a local function ID by name
    pub fn get_local_function_id(&self, name: Ustr) -> Option<LocalFunctionId> {
        self.get_definition(name)
            .and_then(|def_kind| def_kind.as_function().copied())
    }

    /// Get a local function by name
    pub fn get_function(&self, name: Ustr) -> Option<&ModuleFunction> {
        let id = self.get_local_function_id(name)?;
        self.functions.get(id.as_index())
    }

    /// Get a mutable local function by name
    pub fn get_function_mut(&mut self, name: Ustr) -> Option<&mut ModuleFunction> {
        self.get_function_id_mut(name).map(|(_, f)| f)
    }

    /// Get a mutable local function and its ID by name
    pub fn get_function_id_mut(
        &mut self,
        name: Ustr,
    ) -> Option<(LocalFunctionId, &mut ModuleFunction)> {
        let id = self.get_local_function_id(name)?;
        self.functions.get_mut(id.as_index()).map(|f| (id, f))
    }

    /// Get a function by name only in this module and return its script node, if it is a script function.
    pub fn get_function_node(&mut self, name: Ustr) -> Option<Ref<'_, Node>> {
        self.get_function(name)?.get_node()
    }

    /// Gets a function by name only in this module and return its mutable script node, if it is a script function.
    pub fn get_function_node_mut(&mut self, name: Ustr) -> Option<RefMut<'_, Node>> {
        self.get_function_mut(name)?.get_node_mut()
    }

    /// Get a local function name by ID (slow, iterates over the def table)
    pub fn get_function_name_by_id(&self, id: LocalFunctionId) -> Option<Ustr> {
        self.def_table
            .iter()
            .find(|(def_kind, _)| {
                def_kind
                    .as_function()
                    .is_some_and(|function_id| *function_id == id)
            })
            .and_then(|(_, name)| *name)
    }

    /// Get a local function by ID
    pub fn get_function_by_id(&self, id: LocalFunctionId) -> Option<&ModuleFunction> {
        self.functions.get(id.as_index())
    }

    /// Get a mutable local function by ID
    pub fn get_function_by_id_mut(&mut self, id: LocalFunctionId) -> Option<&mut ModuleFunction> {
        self.functions.get_mut(id.as_index())
    }

    /// Iterate over all local functions in this module.
    pub fn iter_functions(&self) -> impl Iterator<Item = &ModuleFunction> {
        self.functions.iter()
    }

    /// Iterate over all named local functions in this module, returning their name and data.
    pub fn iter_named_functions(&self) -> impl Iterator<Item = (Ustr, &ModuleFunction)> {
        self.def_table.iter().filter_map(|(def_kind, name_opt)| {
            let name = (*name_opt)?;
            def_kind.as_function().map(|function_id| {
                let function = &self.functions[function_id.as_index()];
                (name, function)
            })
        })
    }

    /// Get the number of functions in this module.
    pub fn function_count(&self) -> usize {
        self.functions.len()
    }

    /// Look-up a function by name in this module or in any of the modules this module uses.
    pub fn lookup_function<'a>(
        &'a self,
        name: &'a str,
        others: &'a Modules,
    ) -> Result<Option<&'a ModuleFunction>, InternalCompilationError> {
        self.get_member(name, others, &|name, module| {
            module.get_function(ustr(name))
        })
        .map(|opt| opt.map(|(_, f)| f))
    }

    // Type aliases

    /// Add a type alias to this module, name by &str, returning its ID.
    pub(crate) fn add_type_alias_str(&mut self, name: &str, ty: Type) -> LocalTypeAliasId {
        self.add_type_alias(ustr(name), ty)
    }

    /// Add a type alias to this module, returning its ID.
    pub(crate) fn add_type_alias(&mut self, name: Ustr, ty: Type) -> LocalTypeAliasId {
        let id = LocalTypeAliasId::from_index(self.type_aliases.type_len());
        self.type_aliases.set(name, ty);
        self.def_table.insert(name, DefKind::TypeAlias(id));
        id
    }

    /// Look-up a type alias by name in this module.
    pub fn get_type_alias(&self, name: Ustr) -> Option<Type> {
        self.get_definition(name).and_then(|def_kind| {
            def_kind
                .as_type_alias()
                .map(|type_alias_id| self.type_aliases.get_type(*type_alias_id))
        })
    }

    /// Add a bare native type alias to this module, name by &str.
    pub(crate) fn add_bare_native_type_alias_str(
        &mut self,
        name: &str,
        native: Box<dyn crate::r#type::BareNativeType>,
    ) {
        self.add_bare_native_type_alias(ustr(name), native)
    }

    /// Add a bare native type alias to this module.
    pub(crate) fn add_bare_native_type_alias(
        &mut self,
        name: Ustr,
        native: Box<dyn crate::r#type::BareNativeType>,
    ) {
        self.type_aliases.set_bare_native(name, native);
    }

    // Type definitions

    /// Add a type definition to this module, returning its ID.
    pub(crate) fn add_type_def(&mut self, name: Ustr, type_def: TypeDefRef) -> LocalTypeDefId {
        let id = LocalTypeDefId::from_index(self.type_defs.len());
        self.type_defs.push(type_def);
        self.def_table.insert(name, DefKind::TypeDef(id));
        id
    }

    /// Look-up a type definition by name in this module.
    pub fn get_type_def(&self, name: Ustr) -> Option<&TypeDefRef> {
        self.get_definition(name).and_then(|def_kind| {
            def_kind
                .as_type_def()
                .map(|type_def_id| &self.type_defs[type_def_id.as_index()])
        })
    }

    // Trait definitions and implementations

    /// Add a trait definition to this module, returning its ID.
    pub fn add_trait(&mut self, trait_ref: TraitRef) -> LocalTraitId {
        let id = LocalTraitId::from_index(self.traits.len());
        self.traits.push(trait_ref.clone());
        // As currently only std defines traits, we asserts that it has not been added yet.
        assert!(self.def_table.get_by_name(&trait_ref.name).is_none());
        self.def_table.insert(trait_ref.name, DefKind::Trait(id));
        id
    }

    /// Iterate over all traits defined in this module.
    pub fn trait_iter(&self) -> impl Iterator<Item = &TraitRef> + '_ {
        self.traits.iter()
    }

    // Trait implementations

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
        // TODO: find the name and use it to store the impl
        self.add_collected_functions(fn_collector);
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
        self.add_collected_functions(fn_collector);
    }

    /// Add a concrete or blanket trait implementation to this module, using already-added local functions.
    pub(crate) fn add_emitted_impl(
        &mut self,
        trait_ref: TraitRef,
        emit_output: EmitTraitOutput,
    ) -> LocalImplId {
        // TODO: ensure coherence

        let dictionary_ty = self.computer_dictionary_ty(&emit_output.functions);
        let dictionary_value = build_dictionary_value(&emit_output.functions, self.impls.module_id);
        let imp = TraitImpl::new(
            emit_output.output_tys,
            emit_output.functions,
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

    /// Return a concrete implementation id by its key, if it exists in this module.
    pub fn get_concrete_impl_by_key(&self, key: &ConcreteTraitImplKey) -> Option<&LocalImplId> {
        self.impls.concrete().get(key)
    }

    /// Return a set of blanket implementation by their trait reference, if any exist in this module.
    pub fn get_blanket_impl_by_key(&self, key: &TraitRef) -> Option<&BlanketTraitImpls> {
        self.impls.blanket().get(key)
    }

    /// Return a trait implementation's data by ID.
    pub fn get_impl_data(&self, impl_id: LocalImplId) -> Option<&TraitImpl> {
        self.impls.data.get(impl_id.as_index())
    }

    /// Return a trait implementation's data by trait key.
    pub fn get_impl_data_by_trait_key(&self, key: &TraitKey) -> Option<&TraitImpl> {
        self.impls.get_impl_by_key(key)
    }

    /// Return a trait trait by implementation ID.
    pub fn get_impl_trait_key_by_id(&self, impl_id: LocalImplId) -> Option<TraitKey> {
        self.impls.get_key_by_local_id(impl_id)
    }

    /// Get the number of trait implementations in this module.
    pub fn impl_count(&self) -> usize {
        self.impls.data.len()
    }

    // General module queries

    /// Check if this module is "empty" (has no meaningful content)
    pub fn is_empty(&self) -> bool {
        self.functions.is_empty()
            && self.import_fn_slots.is_empty()
            && self.type_aliases.is_empty()
            && self.type_defs.is_empty()
            && self.traits.is_empty()
            && self.impls.is_empty()
    }

    /// Return an iterator over the names of all own symbols in this module.
    pub fn own_symbols(&self) -> impl Iterator<Item = Ustr> + use<'_> {
        self.def_table.iter_names().copied()
    }

    /// Return the type for the source pos, if any.
    pub fn type_at(&self, pos: usize) -> Option<Type> {
        for function in self.functions.iter() {
            let mut code = function.code.borrow_mut();
            let ty = code
                .as_script_mut()
                .and_then(|script_fn| script_fn.code.type_at(pos));
            if ty.is_some() {
                return ty;
            }
        }
        None
    }

    /// Look-up a definition by name in this module.
    pub fn get_definition(&self, name: Ustr) -> Option<DefKind> {
        self.def_table
            .get_by_name(&name)
            .map(|(_, def_kind)| *def_kind)
    }

    /// Look-up a member by name in this module or in any of the modules this module uses.
    /// Returns the module name if the member is from another module.
    /// The getter function is used to get the member from a module.
    pub fn get_member<'a, T>(
        &'a self,
        name: &'a str,
        others: &'a Modules,
        getter: &impl Fn(&'a str, &'a Self) -> Option<T>,
    ) -> Result<Option<(Option<ModuleId>, T)>, InternalCompilationError> {
        if let Some(t) = getter(name, self) {
            return Ok(Some((None, t)));
        }

        let u_name = ustr(name);
        if let Some(use_data) = self.uses.explicits.get(&u_name) {
            if let Some((module_id, module_ref)) = others.get_by_name(&use_data.module) {
                if let Some(t) = getter(name, module_ref) {
                    return Ok(Some((Some(module_id), t)));
                }
            }
        }

        let mut matches = Vec::new();
        for wildcard_use in &self.uses.wildcards {
            if let Some((module_id, module_ref)) = others.get_by_name(&wildcard_use.module) {
                if let Some(t) = getter(name, module_ref) {
                    matches.push((wildcard_use, module_id, t));
                }
            }
        }

        match matches.len() {
            0 => Ok(None),
            1 => {
                let (_, module_id, t) = matches.pop().unwrap();
                Ok(Some((Some(module_id), t)))
            }
            _ => {
                let occurrences = matches
                    .iter()
                    .map(|(w, _, _)| ImportSite {
                        module: w.module.clone(),
                        span: w.span,
                        kind: ImportKind::Module,
                    })
                    .collect();
                Err(internal_compilation_error!(NameImportedMultipleTimes {
                    name: u_name,
                    occurrences,
                }))
            }
        }
    }

    pub fn list_stats(&self) -> String {
        let mut stats = String::new();
        if !self.uses.explicits.is_empty() || !self.uses.wildcards.is_empty() {
            stats.push_str(&format!(
                "use directives: {} explicit, {} wildcards",
                self.uses.explicits.len(),
                self.uses.wildcards.len()
            ));
        }
        if !self.type_aliases.is_empty() {
            if !stats.is_empty() {
                stats.push_str(", ");
            }
            stats.push_str(&format!("type aliases: {}", self.type_aliases.type_len()));
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
            let named_count = self
                .def_table
                .iter()
                .filter(|(kind, name)| {
                    if !kind.is_function() {
                        false
                    } else {
                        name.is_some_and(|name| self.is_non_trait_local_function(name))
                    }
                })
                .count();
            stats.push_str(&format!("named functions: {}", named_count));
            if self.functions.len() > named_count {
                let unnamed_count = self.functions.len() - named_count;
                stats.push_str(&format!(", trait impl functions: {}", unnamed_count));
            }
        }
        stats
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

    fn computer_dictionary_ty(&self, function_ids: &[LocalFunctionId]) -> Type {
        let tys: Vec<_> = function_ids
            .iter()
            .map(|id| {
                let function = &self
                    .functions
                    .get(id.as_index())
                    .expect("Invalid function ID");
                Type::function_type(function.definition.ty_scheme.ty.clone())
            })
            .collect();
        Type::tuple(tys)
    }

    fn format_with_modules(
        &self,
        f: &mut fmt::Formatter,
        modules: &Modules,
        show_details: bool,
    ) -> fmt::Result {
        let env = ModuleEnv::new(self, modules, false);
        if !self.uses.explicits.is_empty() {
            writeln!(
                f,
                "Explicit use directives ({}):",
                self.uses.explicits.len()
            )?;
            for (symbol, use_data) in self.uses.explicits.iter() {
                writeln!(f, "  {}: {}", use_data.module, symbol)?;
            }
            writeln!(f, "\n")?;
        }
        if !self.uses.wildcards.is_empty() {
            writeln!(
                f,
                "Wildcard use directives ({}):",
                self.uses.wildcards.len()
            )?;
            for wildcard_use in self.uses.wildcards.iter() {
                writeln!(f, "  {}: *", wildcard_use.module)?;
            }
            writeln!(f, "\n")?;
        }
        if self.type_aliases.type_len() > 0 {
            writeln!(f, "Type aliases ({}):\n", self.type_aliases.type_len())?;
            for ty in self.type_aliases.type_iter() {
                let name = self.type_aliases.get_name(ty).unwrap();
                writeln!(f, "{}: {}", name, ty.data().format_with(&env))?;
            }
            writeln!(f, "\n")?;
        }
        if self.type_aliases.bare_native_len() > 0 {
            writeln!(
                f,
                "Bare native type aliases ({}):\n",
                self.type_aliases.bare_native_len()
            )?;
            for (name, native) in self.type_aliases.bare_native_iter() {
                writeln!(f, "{}: {}", name, native.type_name())?;
            }
            writeln!(f, "\n")?;
        }
        if !self.type_defs.is_empty() {
            writeln!(f, "New types ({}):\n", self.type_defs.len())?;
            for decl in self.type_defs.iter() {
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
            let named_count = self
                .iter_named_functions()
                .filter(|&(name, _)| self.is_non_trait_local_function(name))
                .count();
            writeln!(f, "Non-trait impl functions ({}):\n", named_count)?;
            for (i, (name, function)) in self.iter_named_functions().enumerate() {
                if !self.is_non_trait_local_function(name) {
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
                writeln!(f, "\nNot showing {} trait impl functions.", unnamed_count)?;
            }
        }
        Ok(())
    }
}

impl FormatWith<Modules> for Module {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, data: &Modules) -> fmt::Result {
        self.format_with_modules(f, data, false)
    }
}

/// A set of modules indexed both by name (Path) and by numeric ID (ModuleId).
/// This is the canonical way to hold a collection of modules in a compilation session.
pub type Modules = NamedIndexed<Path, ModuleId, Module>;

pub struct ShowModuleDetails<'a>(pub &'a Modules);

impl FormatWith<ShowModuleDetails<'_>> for Module {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, data: &ShowModuleDetails) -> fmt::Result {
        self.format_with_modules(f, data.0, true)
    }
}

// impl FormatWith<ModuleEnv<'_>> for LocalFunction {
//     fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
//         self.function
//             .definition
//             .fmt_with_name_and_module_env(f, self.name, "", env)?;
//         self.function.code.borrow().format_ind(f, env, 1, 1)
//     }
// }
