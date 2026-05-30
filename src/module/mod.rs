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

pub mod debug_info;
pub mod function;
pub mod id;
pub mod module_env;
pub mod path;
pub mod trait_impl;
mod type_alias_name;
pub mod uses;

pub use debug_info::*;
use derive_new::new;
use enum_as_inner::EnumAsInner;
pub use function::*;
use itertools::Itertools;
pub use module_env::*;
pub use path::*;
pub use trait_impl::*;
pub use uses::*;

use std::{fmt, hash::Hash, ops};

use ustr::{Ustr, ustr};

use crate::{
    FxHashMap, FxHashSet, Location, Modules,
    ast::UstrSpan,
    compiler::error::{ImportKind, ImportSite, InternalCompilationError},
    define_id_type,
    format::{FormatWith, write_identifier},
    hir::{self, ENodeArena, emit_ir::EmitTraitOutput, function::Function, value::LiteralValue},
    internal_compilation_error,
    module::id::{Id, NamedIndexed},
    types::{
        r#trait::Trait,
        r#type::{
            LocalTypeAliasId, Type, TypeAliasEntry, TypeAliases, TypeDef, TypeDefSlot,
            TypeDisplayEnv, TypeKind, TypeVar,
        },
        type_scheme::PubTypeConstraint,
    },
};

pub(crate) const GENERATED_LAMBDA_PREFIX: &str = "$lambda$";

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

/// Item visibility
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Visibility {
    #[default]
    Module,
    Public,
}

impl Visibility {
    pub fn is_public(self) -> bool {
        matches!(self, Self::Public)
    }
}

define_id_type!(
    /// ID of a type definition within a module
    LocalTypeDefId
);

/// A fully-qualified reference to a type definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, new)]
pub struct TypeDefId {
    pub module: ModuleId,
    pub index: LocalTypeDefId,
}

impl FormatWith<ModuleEnv<'_>> for TypeDefId {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        let type_name = env
            .try_type_def_name(*self)
            .map(|name| name.to_string())
            .unwrap_or_else(|| format!("#{}", self.index));

        if self.module == env.current.module_id() {
            write!(f, "{type_name}")
        } else if let Some(module_name) = env.modules.get_name(self.module) {
            write!(f, "{module_name}::{type_name}")
        } else {
            write!(f, "#{}::{type_name}", self.module)
        }
    }
}

define_id_type!(
    /// ID of a trait definition within a module
    LocalTraitId
);

/// A fully-qualified reference to a trait definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, new)]
pub struct TraitId {
    pub module: ModuleId,
    pub index: LocalTraitId,
}

impl FormatWith<ModuleEnv<'_>> for TraitId {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        let trait_name = env
            .try_trait_name(*self)
            .map(|name| name.to_string())
            .unwrap_or_else(|| format!("#{}", self.index));

        if self.module == env.current.module_id() {
            write!(f, "{trait_name}")
        } else if let Some(module_name) = env.modules.get_name(self.module) {
            write!(f, "{module_name}::{trait_name}")
        } else {
            write!(f, "#{}::{trait_name}", self.module)
        }
    }
}

/// All possible kinds of definitions within a module
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, EnumAsInner)]
pub enum DefKind {
    Function(LocalFunctionId),
    TypeDef(LocalTypeDefId),
    TypeAlias(LocalTypeAliasId),
    BareNativeTypeAlias,
    Trait(LocalTraitId),
    // Impl(LocalImplId), currently not accessed by name, if we want to add it, we must take care in trait solver to register the ones it adds
}

/// A symbol definition along with its visibility
#[derive(Debug, Clone, Copy, PartialEq, Eq, new)]
pub struct Def {
    pub kind: DefKind,
    pub visibility: Visibility,
}

impl Def {
    pub fn public(kind: DefKind) -> Self {
        Self::new(kind, Visibility::Public)
    }
}

/// The symbol definition table
pub type DefTable = NamedIndexed<Ustr, LocalDefId, Def>;

#[derive(Debug, Clone, Default)]
pub(crate) struct TypeDefSlots(Vec<TypeDefSlot>);

impl TypeDefSlots {
    fn push(&mut self, slot: TypeDefSlot) {
        self.0.push(slot);
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn get(&self, index: usize) -> Option<&TypeDefSlot> {
        self.0.get(index)
    }

    fn iter(&self) -> impl Iterator<Item = &TypeDefSlot> {
        self.0.iter()
    }

    pub(crate) fn as_slice(&self) -> &[TypeDefSlot] {
        &self.0
    }
}

impl ops::Index<usize> for TypeDefSlots {
    type Output = TypeDefSlot;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl ops::IndexMut<usize> for TypeDefSlots {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

// Module itself

/// Once-built immutable module bundle containing all compiled module data
/// Items are conceptually private, but some are pub(crate) for lifetime constraints.
/// These are only accessed directly by emit_ir and trait_solver, other users should go through accessors,
/// with the exception of uses which is also accessed directly by desugar.
#[derive(Debug, Clone)]
pub struct Module {
    pub(crate) import_fn_slots: Vec<ImportFunctionSlot>,
    pub(crate) import_impl_slots: Vec<ImportImplSlot>,
    // Dependencies from type import
    pub(crate) type_deps: FxHashSet<ModuleId>,

    pub(crate) uses: Uses,

    /// All symbols defined in this module
    pub(crate) def_table: DefTable,

    /// Names of unsafe implementation details. Access policy is enforced during lookup.
    unsafe_items: FxHashSet<Ustr>,

    // Functions, including methods of trait implementations.
    pub(crate) functions: Vec<ModuleFunction>,

    // Type system content
    type_aliases: TypeAliases,
    pub(crate) type_defs: TypeDefSlots,
    pub(crate) traits: Traits,
    pub(crate) impls: TraitImpls,

    /// Arena holding all HIR nodes for all functions in this module.
    pub ir_arena: ENodeArena,
}

impl Module {
    /// Create a new empty module with the given ID, store the id in impls for later use.
    pub fn new(module_id: ModuleId) -> Self {
        Self {
            import_fn_slots: Vec::new(),
            import_impl_slots: Vec::new(),
            type_deps: FxHashSet::default(),
            uses: Uses::default(),
            def_table: DefTable::new(),
            unsafe_items: FxHashSet::default(),
            functions: Vec::new(),
            type_aliases: TypeAliases::default(),
            type_defs: TypeDefSlots::default(),
            traits: Traits::new(),
            impls: TraitImpls::new(module_id),
            ir_arena: ENodeArena::default(),
        }
    }

    /// Create a new empty module with the given ID and specified uses, store the id in impls for later use.
    pub fn from_uses(module_id: ModuleId, uses: Uses) -> Self {
        Self {
            import_fn_slots: Vec::new(),
            import_impl_slots: Vec::new(),
            type_deps: FxHashSet::default(),
            uses,
            def_table: DefTable::new(),
            unsafe_items: FxHashSet::default(),
            functions: Vec::new(),
            type_aliases: TypeAliases::default(),
            type_defs: TypeDefSlots::default(),
            traits: Traits::new(),
            impls: TraitImpls::new(module_id),
            ir_arena: ENodeArena::default(),
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

    /// Modules this module depends on
    pub fn deps(&self) -> impl Iterator<Item = ModuleId> {
        self.type_deps
            .iter()
            .copied()
            .chain(self.import_fn_slots.iter().map(|slot| slot.module))
            .chain(self.import_impl_slots.iter().map(|slot| slot.module))
            .unique()
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
        self.add_function_with_visibility(name, function, Visibility::Public)
    }

    /// Add a function to this module with explicit source visibility.
    pub fn add_function_with_visibility(
        &mut self,
        name: Ustr,
        function: ModuleFunction,
        visibility: Visibility,
    ) -> LocalFunctionId {
        let id = LocalFunctionId::from_index(self.functions.len());
        self.functions.push(function);
        self.def_table
            .insert(name, Def::new(DefKind::Function(id), visibility));
        id
    }

    /// Add a private unsafe function whose use is controlled by compiler policy.
    pub(crate) fn add_private_unsafe_function(
        &mut self,
        name: Ustr,
        function: ModuleFunction,
    ) -> LocalFunctionId {
        let id = self.add_function_with_visibility(name, function, Visibility::Module);
        self.unsafe_items.insert(name);
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
        self.def_table
            .insert(new_name, Def::public(DefKind::Function(id)));
    }

    /// Add collected final functions from a FunctionCollector to this module.
    pub fn add_collected_functions(&mut self, collector: FunctionCollector) {
        let start_id = self.functions.len();
        let functions =
            collector
                .new_elements
                .into_iter()
                .enumerate()
                .map(|(i, (name, function))| {
                    let local_id = LocalFunctionId::from_index(start_id + i);
                    self.def_table
                        .insert(name, Def::public(DefKind::Function(local_id)));
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

    /// Get a local function name by ID (slow, iterates over the def table)
    pub fn get_function_name_by_id(&self, id: LocalFunctionId) -> Option<Ustr> {
        self.def_table
            .iter()
            .find(|(def, _)| {
                def.kind
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
        self.def_table.iter().filter_map(|(def, name_opt)| {
            let name = (*name_opt)?;
            def.kind.as_function().map(|function_id| {
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

    /// Add a documented non-generic type alias to this module (by &str), returning its ID.
    pub(crate) fn add_type_alias_str_with_doc(
        &mut self,
        name: &str,
        ty: Type,
        doc: impl Into<String>,
    ) -> LocalTypeAliasId {
        self.add_type_alias_with_param_spans_and_visibility(
            ustr(name),
            vec![],
            0,
            ty,
            Visibility::Public,
            Some(doc.into()),
        )
    }

    pub(crate) fn add_type_alias_with_param_spans_and_visibility(
        &mut self,
        name: Ustr,
        generic_params: Vec<UstrSpan>,
        ty_var_count: u32,
        ty: Type,
        visibility: Visibility,
        doc: Option<String>,
    ) -> LocalTypeAliasId {
        let id = LocalTypeAliasId::from_index(self.type_aliases.type_len());
        self.type_aliases
            .set(name, generic_params, ty_var_count, ty, doc);
        self.def_table
            .insert(name, Def::new(DefKind::TypeAlias(id), visibility));
        id
    }

    /// Look-up a type alias by name in this module, returning the full entry.
    pub fn get_type_alias(&self, name: Ustr) -> Option<&TypeAliasEntry> {
        self.get_definition(name).and_then(|def_kind| {
            def_kind
                .as_type_alias()
                .map(|type_alias_id| self.type_aliases.get_entry(*type_alias_id))
        })
    }

    /// Look-up a bare native type alias by name in this module.
    pub fn get_bare_native_type_alias(
        &self,
        name: Ustr,
    ) -> Option<crate::containers::B<dyn crate::types::r#type::BareNativeType>> {
        self.type_aliases.get_bare_native_by_name(name).cloned()
    }

    /// Add an unsafe bare native type alias whose use is controlled by compiler policy.
    pub(crate) fn add_unsafe_bare_native_type_alias_str(
        &mut self,
        name: &str,
        native: Box<dyn crate::types::r#type::BareNativeType>,
    ) {
        self.add_bare_native_type_alias_with_visibility(ustr(name), native, Visibility::Module);
        self.unsafe_items.insert(ustr(name));
    }

    fn add_bare_native_type_alias_with_visibility(
        &mut self,
        name: Ustr,
        native: Box<dyn crate::types::r#type::BareNativeType>,
        visibility: Visibility,
    ) {
        self.type_aliases.set_bare_native(name, native);
        self.def_table
            .insert(name, Def::new(DefKind::BareNativeTypeAlias, visibility));
    }

    /// Return whether a named item is an unsafe implementation detail.
    pub fn is_unsafe_item(&self, name: Ustr) -> bool {
        self.unsafe_items.contains(&name)
    }

    // Type definitions

    /// Add a type definition to this module, returning its ID.
    pub fn reserve_type_def(
        &mut self,
        name: Ustr,
        generic_params: Vec<UstrSpan>,
        span: Location,
    ) -> TypeDefId {
        self.reserve_type_def_with_visibility(name, generic_params, span, Visibility::Public)
    }

    pub fn reserve_type_def_with_visibility(
        &mut self,
        name: Ustr,
        generic_params: Vec<UstrSpan>,
        span: Location,
        visibility: Visibility,
    ) -> TypeDefId {
        let id = LocalTypeDefId::from_index(self.type_defs.len());
        self.type_defs
            .push(TypeDefSlot::reserved(name, generic_params, span));
        self.def_table
            .insert(name, Def::new(DefKind::TypeDef(id), visibility));
        TypeDefId::new(self.module_id(), id)
    }

    /// Add a type definition to this module, returning its ID.
    pub fn add_type_def(&mut self, name: Ustr, type_def: TypeDef) -> TypeDefId {
        self.add_type_def_with_visibility(name, type_def, Visibility::Public)
    }

    pub fn add_type_def_with_visibility(
        &mut self,
        name: Ustr,
        type_def: TypeDef,
        visibility: Visibility,
    ) -> TypeDefId {
        let id = LocalTypeDefId::from_index(self.type_defs.len());
        self.type_defs.push(TypeDefSlot::resolved(type_def));
        self.def_table
            .insert(name, Def::new(DefKind::TypeDef(id), visibility));
        TypeDefId::new(self.module_id(), id)
    }

    /// Fill a reserved type definition slot.
    pub fn fill_type_def(&mut self, id: TypeDefId, type_def: TypeDef) {
        assert_eq!(id.module, self.module_id());
        self.type_defs[id.index.as_index()].fill(type_def);
    }

    pub fn type_def_name(&self, id: TypeDefId) -> Ustr {
        assert_eq!(id.module, self.module_id());
        self.type_defs[id.index.as_index()].name()
    }

    pub fn try_type_def_name(&self, id: TypeDefId) -> Option<Ustr> {
        if id.module == self.module_id() {
            self.type_defs
                .get(id.index.as_index())
                .map(TypeDefSlot::name)
        } else {
            None
        }
    }

    pub fn type_def_param_names(&self, id: TypeDefId) -> impl ExactSizeIterator<Item = Ustr> + '_ {
        assert_eq!(id.module, self.module_id());
        self.type_defs[id.index.as_index()].param_names()
    }

    pub fn try_type_def_param_names(
        &self,
        id: TypeDefId,
    ) -> Option<impl ExactSizeIterator<Item = Ustr> + '_> {
        if id.module == self.module_id() {
            self.type_defs
                .get(id.index.as_index())
                .map(TypeDefSlot::param_names)
        } else {
            None
        }
    }

    pub fn type_def_param_spans(
        &self,
        id: TypeDefId,
    ) -> impl ExactSizeIterator<Item = Location> + '_ {
        assert_eq!(id.module, self.module_id());
        self.type_defs[id.index.as_index()].param_spans()
    }

    pub fn try_type_def_param_spans(
        &self,
        id: TypeDefId,
    ) -> Option<impl ExactSizeIterator<Item = Location> + '_> {
        if id.module == self.module_id() {
            self.type_defs
                .get(id.index.as_index())
                .map(TypeDefSlot::param_spans)
        } else {
            None
        }
    }

    pub fn type_def_span(&self, id: TypeDefId) -> Location {
        assert_eq!(id.module, self.module_id());
        self.type_defs[id.index.as_index()].span()
    }

    pub fn try_type_def_span(&self, id: TypeDefId) -> Option<Location> {
        if id.module == self.module_id() {
            self.type_defs
                .get(id.index.as_index())
                .map(TypeDefSlot::span)
        } else {
            None
        }
    }

    /// Return a resolved type definition by ID.
    pub fn type_def(&self, id: TypeDefId) -> &TypeDef {
        assert_eq!(id.module, self.module_id());
        self.type_defs[id.index.as_index()].def()
    }

    pub fn try_type_def(&self, id: TypeDefId) -> Option<&TypeDef> {
        if id.module == self.module_id() {
            self.type_defs
                .get(id.index.as_index())
                .map(TypeDefSlot::def)
        } else {
            None
        }
    }

    /// Iterate over type definition IDs in declaration order.
    pub(crate) fn type_def_ids(&self) -> impl Iterator<Item = TypeDefId> + '_ {
        (0..self.type_defs.len())
            .map(|index| TypeDefId::new(self.module_id(), LocalTypeDefId::from_index(index)))
    }

    /// Look-up a type definition ID by name in this module.
    pub fn get_type_def_id(&self, name: Ustr) -> Option<TypeDefId> {
        self.get_definition(name).and_then(|def_kind| {
            def_kind
                .as_type_def()
                .map(|type_def_id| TypeDefId::new(self.module_id(), *type_def_id))
        })
    }

    /// Look-up a resolved type definition by name in this module.
    pub fn get_type_def(&self, name: Ustr) -> Option<&TypeDef> {
        self.get_type_def_id(name).map(|id| self.type_def(id))
    }

    pub(crate) fn owns_type_def(&self, type_def: TypeDefId) -> bool {
        type_def.module == self.module_id()
            && type_def.index.as_index() < self.type_defs.len()
            && self
                .get_definition(self.type_def_name(type_def))
                .is_some_and(|def| def.as_type_def() == Some(&type_def.index))
    }

    // Trait definitions and implementations

    /// Add a trait definition to this module, returning its ID.
    pub fn add_trait(&mut self, trait_def: Trait) -> LocalTraitId {
        self.add_trait_with_visibility(trait_def, Visibility::Public)
    }

    pub fn add_trait_with_visibility(
        &mut self,
        trait_def: Trait,
        visibility: Visibility,
    ) -> LocalTraitId {
        let id = LocalTraitId::from_index(self.traits.len());
        let trait_name = trait_def.name;
        self.traits.push(trait_def);
        // Trait names are module-level symbols, so they must remain unique.
        assert!(self.def_table.get_by_name(&trait_name).is_none());
        self.def_table
            .insert(trait_name, Def::new(DefKind::Trait(id), visibility));
        id
    }

    /// Iterate over all traits defined in this module.
    pub fn trait_iter(&self) -> impl Iterator<Item = (TraitId, &Trait)> + '_ {
        self.traits.iter().enumerate().map(|(index, trait_def)| {
            (
                TraitId::new(self.module_id(), LocalTraitId::from_index(index)),
                trait_def,
            )
        })
    }

    /// Look-up a trait definition by name in this module.
    pub fn get_trait_id(&self, name: Ustr) -> Option<TraitId> {
        self.get_definition(name).and_then(|def_kind| {
            def_kind
                .as_trait()
                .map(|trait_id| TraitId::new(self.module_id(), *trait_id))
        })
    }

    /// Look-up a trait definition by string name in this module.
    pub fn get_trait_id_str(&self, name: &str) -> Option<TraitId> {
        self.get_trait_id(ustr(name))
    }

    /// Look-up a trait definition by string name in this module, panicking if it is missing.
    pub fn expect_trait_id_str(&self, name: &str) -> TraitId {
        self.get_trait_id_str(name)
            .unwrap_or_else(|| panic!("trait `{name}` not found in module #{}", self.module_id()))
    }

    /// Look-up a std trait while building the std module.
    pub fn expect_std_trait_id_in_current_module(&self, name: &str) -> TraitId {
        assert_eq!(
            self.module_id(),
            crate::std::STD_MODULE_ID,
            "std trait lookup in current module requires the std module"
        );
        self.expect_trait_id_str(name)
    }

    /// Look-up a trait by string name in another module.
    pub fn expect_trait_id_str_in_module(
        module_id: ModuleId,
        modules: &Modules,
        name: &str,
    ) -> TraitId {
        modules
            .get(module_id)
            .and_then(|entry| entry.module())
            .and_then(|module| module.get_trait_id_str(name))
            .unwrap_or_else(|| panic!("trait `{name}` not found in module #{module_id}"))
    }

    /// Look-up a std trait in the registered std module.
    pub fn expect_std_trait_id(modules: &Modules, name: &str) -> TraitId {
        Self::expect_trait_id_str_in_module(crate::std::STD_MODULE_ID, modules, name)
    }

    /// Look-up a trait definition by name in this module.
    pub fn get_trait(&self, name: Ustr) -> Option<&Trait> {
        self.get_trait_id(name).map(|id| self.trait_def(id))
    }

    /// Look-up a trait definition by name in this module, using &str.
    pub fn get_trait_str(&self, name: &str) -> Option<&Trait> {
        self.get_trait(ustr(name))
    }

    /// Return the trait definition for a trait id owned by this module.
    pub fn trait_def(&self, id: TraitId) -> &Trait {
        assert_eq!(id.module, self.module_id());
        &self.traits[id.index.as_index()]
    }

    /// Return the trait definition for a trait id owned by this module, if the id is valid.
    pub fn try_trait_def(&self, id: TraitId) -> Option<&Trait> {
        (id.module == self.module_id())
            .then(|| self.traits.get(id.index.as_index()))
            .flatten()
    }

    /// Return the trait name for a trait id owned by this module, if the id is valid.
    pub fn try_trait_name(&self, id: TraitId) -> Option<Ustr> {
        (id.module == self.module_id())
            .then(|| {
                self.traits
                    .get(id.index.as_index())
                    .map(|trait_def| trait_def.name)
            })
            .flatten()
    }

    // Trait implementations

    /// Add a native concrete trait implementation with no associated const values.
    pub(crate) fn add_native_concrete_impl(
        &mut self,
        trait_id: TraitId,
        input_tys: impl Into<Vec<Type>>,
        output_tys: impl Into<Vec<Type>>,
        functions: impl Into<Vec<Function>>,
    ) {
        self.add_concrete_impl_no_locals(trait_id, input_tys, output_tys, [], functions);
    }

    /// Add a concrete trait implementation to this module, with raw functions and no local variables.
    /// The definition will be retrieved by instantiating the trait method definitions with the given types.
    /// The caller is responsible to ensure that the input and output types match the trait definition
    /// and that the constraints are satisfied.
    pub fn add_concrete_impl_no_locals(
        &mut self,
        trait_id: TraitId,
        input_tys: impl Into<Vec<Type>>,
        output_tys: impl Into<Vec<Type>>,
        associated_const_values: impl Into<Vec<LiteralValue>>,
        functions: impl Into<Vec<Function>>,
    ) {
        let functions: Vec<_> = functions
            .into()
            .into_iter()
            .map(|f| (f, Vec::new()))
            .collect();
        self.add_concrete_impl(
            trait_id,
            input_tys,
            output_tys,
            associated_const_values,
            functions,
        );
    }

    /// Add a concrete trait implementation with an explicit trait definition and no local variables.
    pub fn add_concrete_impl_for_trait_def_no_locals(
        &mut self,
        trait_id: TraitId,
        trait_def: &Trait,
        input_tys: impl Into<Vec<Type>>,
        output_tys: impl Into<Vec<Type>>,
        associated_const_values: impl Into<Vec<LiteralValue>>,
        functions: impl Into<Vec<Function>>,
    ) {
        let functions: Vec<_> = functions
            .into()
            .into_iter()
            .map(|f| (f, Vec::new()))
            .collect();
        self.add_concrete_impl_for_trait_def(
            trait_id,
            trait_def,
            input_tys,
            output_tys,
            associated_const_values,
            functions,
        );
    }

    /// Add a concrete trait implementation to this module, with raw functions.
    /// The definition will be retrieved by instantiating the trait method definitions with the given types.
    /// The caller is responsible to ensure that the input and output types match the trait definition
    /// and that the constraints are satisfied.
    pub fn add_concrete_impl(
        &mut self,
        trait_id: TraitId,
        input_tys: impl Into<Vec<Type>>,
        output_tys: impl Into<Vec<Type>>,
        associated_const_values: impl Into<Vec<LiteralValue>>,
        functions: impl Into<Vec<(Function, Vec<LocalDecl>)>>,
    ) {
        assert_eq!(trait_id.module, self.module_id());
        let trait_def = &self.traits[trait_id.index.as_index()];
        // Add the impl, collecting new functions
        let mut fn_collector = FunctionCollector::new(self.functions.len());
        self.impls.add_concrete_raw(
            trait_id,
            trait_def,
            input_tys,
            output_tys,
            associated_const_values,
            functions,
            &mut fn_collector,
        );
        self.add_collected_functions(fn_collector);
    }

    /// Add a concrete trait implementation using an explicit trait definition.
    ///
    /// This is needed for tests and setup code that add an implementation of a
    /// trait owned by another module while constructing a module directly.
    pub fn add_concrete_impl_for_trait_def(
        &mut self,
        trait_id: TraitId,
        trait_def: &Trait,
        input_tys: impl Into<Vec<Type>>,
        output_tys: impl Into<Vec<Type>>,
        associated_const_values: impl Into<Vec<LiteralValue>>,
        functions: impl Into<Vec<(Function, Vec<LocalDecl>)>>,
    ) {
        // Add the impl, collecting new functions
        let mut fn_collector = FunctionCollector::new(self.functions.len());
        self.impls.add_concrete_raw(
            trait_id,
            trait_def,
            input_tys,
            output_tys,
            associated_const_values,
            functions,
            &mut fn_collector,
        );
        self.add_collected_functions(fn_collector);
    }

    /// Add a blanket trait implementation to this module, with raw functions and no local variables.
    /// The definition will be retrieved by instantiating the trait method definitions with the given types.
    /// The caller is responsible to ensure that the input and output types match the trait definition
    /// and that the provided constraints are consistent with the trait definition.
    pub fn add_blanket_impl_no_locals(
        &mut self,
        trait_id: TraitId,
        sub_key: BlanketTraitImplSubKey,
        output_tys: impl Into<Vec<Type>>,
        associated_const_values: impl Into<Vec<LiteralValue>>,
        functions: impl Into<Vec<Function>>,
    ) {
        let functions: Vec<_> = functions
            .into()
            .into_iter()
            .map(|f| (f, Vec::new()))
            .collect();
        self.add_blanket_impl(
            trait_id,
            sub_key,
            output_tys,
            associated_const_values,
            functions,
        );
    }

    /// Add a blanket trait implementation to this module, with raw functions.
    /// The definition will be retrieved by instantiating the trait method definitions with the given types.
    /// The caller is responsible to ensure that the input and output types match the trait definition
    /// and that the provided constraints are consistent with the trait definition.
    pub fn add_blanket_impl(
        &mut self,
        trait_id: TraitId,
        sub_key: BlanketTraitImplSubKey,
        output_tys: impl Into<Vec<Type>>,
        associated_const_values: impl Into<Vec<LiteralValue>>,
        functions: impl Into<Vec<(Function, Vec<LocalDecl>)>>,
    ) {
        assert_eq!(trait_id.module, self.module_id());
        let trait_def = &self.traits[trait_id.index.as_index()];
        // Add the impl, collecting new functions
        let mut fn_collector = FunctionCollector::new(self.functions.len());
        self.impls.add_blanket_raw(
            trait_id,
            trait_def,
            sub_key,
            output_tys,
            associated_const_values,
            functions,
            &mut fn_collector,
        );
        self.add_collected_functions(fn_collector);
    }

    /// Add a concrete or blanket trait implementation to this module, using already-added local functions.
    pub(crate) fn add_emitted_impl(
        &mut self,
        trait_id: TraitId,
        emit_output: EmitTraitOutput,
        associated_const_values: impl Into<Vec<LiteralValue>>,
        associated_const_tys: impl IntoIterator<Item = Type>,
        public: bool,
        source_span: Option<Location>,
    ) -> LocalImplId {
        let associated_const_values = associated_const_values.into();
        let dictionary_ty =
            self.computer_dictionary_ty(&emit_output.functions, associated_const_tys);
        let dictionary_value =
            build_dictionary_value(&emit_output.functions, &associated_const_values);
        let imp = TraitImpl::new(
            emit_output.output_tys,
            emit_output.functions,
            dictionary_value,
            dictionary_ty,
            public,
            source_span,
        )
        .with_associated_const_values(associated_const_values);
        if emit_output.ty_var_count == 0 {
            let key = ConcreteTraitImplKey::new(trait_id, emit_output.input_tys);
            self.impls.add_concrete_struct(key, imp)
        } else {
            let sub_key = BlanketTraitImplSubKey::new(
                emit_output.input_tys,
                emit_output.ty_var_count,
                emit_output.constraints,
            );
            self.impls
                .add_blanket_struct(BlanketTraitImplKey::new(trait_id, sub_key), imp)
        }
    }

    /// Return a concrete implementation id by its key, if it exists in this module.
    pub fn get_concrete_impl_by_key(&self, key: &ConcreteTraitImplKey) -> Option<&LocalImplId> {
        self.impls.concrete().get(key)
    }

    /// Return a set of blanket implementations by their trait id, if any exist in this module.
    pub fn get_blanket_impl_by_key(&self, key: &TraitId) -> Option<&BlanketTraitImpls> {
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

    /// Return a trait implementation's local ID by trait key.
    pub fn get_impl_id_by_trait_key(&self, key: &TraitKey) -> Option<LocalImplId> {
        self.impls.get_impl_id_by_key(key)
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

    /// Return an iterator over public own symbols in this module.
    pub fn public_symbols(&self) -> impl Iterator<Item = Ustr> + use<'_> {
        self.def_table
            .iter_named()
            .filter_map(|(name, def)| def.visibility.is_public().then_some(*name))
    }

    /// Return the declared visibility for a module-level symbol.
    pub fn symbol_visibility(&self, name: Ustr) -> Option<Visibility> {
        self.def_table
            .get_by_name(&name)
            .map(|(_, def)| def.visibility)
    }

    /// Return whether a symbol can be named from the given module.
    pub fn is_symbol_accessible_from(&self, name: Ustr, from_module: ModuleId) -> bool {
        self.symbol_visibility(name)
            .is_some_and(|visibility| self.module_id() == from_module || visibility.is_public())
    }

    /// Return whether a type definition owned by this module is accessible from the given module.
    pub fn is_type_def_accessible_from(&self, id: TypeDefId, from_module: ModuleId) -> bool {
        if id.module != self.module_id() {
            return false;
        }
        self.try_type_def_name(id)
            .is_some_and(|name| self.is_symbol_accessible_from(name, from_module))
    }

    /// Return whether all named types in a type are accessible from the given module.
    pub fn is_type_accessible_from(
        &self,
        ty: Type,
        from_module: ModuleId,
        others: &Modules,
    ) -> bool {
        self.is_type_visible_by(ty, others, |module, type_def| {
            module.is_type_def_accessible_from(type_def, from_module)
        })
    }

    fn module_for<'a>(&'a self, module_id: ModuleId, others: &'a Modules) -> Option<&'a Module> {
        if module_id == self.module_id() {
            return Some(self);
        }
        others.get(module_id).and_then(|entry| entry.module())
    }

    fn is_type_visible_by(
        &self,
        ty: Type,
        others: &Modules,
        is_named_type_visible: impl Fn(&Module, TypeDefId) -> bool + Copy,
    ) -> bool {
        use TypeKind::*;
        match &*ty.data() {
            Variable(_) | Native(_) | Never => true,
            Variant(fields) | Record(fields) => fields
                .iter()
                .all(|(_, ty)| self.is_type_visible_by(*ty, others, is_named_type_visible)),
            Tuple(fields) => fields
                .iter()
                .all(|ty| self.is_type_visible_by(*ty, others, is_named_type_visible)),
            Function(function) => {
                function
                    .args
                    .iter()
                    .all(|arg| self.is_type_visible_by(arg.ty, others, is_named_type_visible))
                    && self.is_type_visible_by(function.ret, others, is_named_type_visible)
            }
            Named(named) => {
                self.is_type_def_ref_visible_by(named.def, others, is_named_type_visible)
                    && named
                        .params
                        .iter()
                        .all(|ty| self.is_type_visible_by(*ty, others, is_named_type_visible))
            }
        }
    }

    fn is_type_def_ref_visible_by(
        &self,
        id: TypeDefId,
        others: &Modules,
        is_named_type_visible: impl Fn(&Module, TypeDefId) -> bool + Copy,
    ) -> bool {
        self.module_for(id.module, others)
            .is_some_and(|module| is_named_type_visible(module, id))
    }

    /// Return whether a trait can be named from the given module.
    pub fn is_trait_accessible_from(
        &self,
        trait_id: TraitId,
        from_module: ModuleId,
        others: &Modules,
    ) -> bool {
        self.is_trait_visible_by(trait_id, others, |module, trait_name| {
            module.is_symbol_accessible_from(trait_name, from_module)
        })
    }

    /// Return whether all named items in a trait constraint are accessible from the given module.
    pub fn is_trait_constraint_accessible_from(
        &self,
        constraint: &PubTypeConstraint,
        from_module: ModuleId,
        others: &Modules,
    ) -> bool {
        self.is_trait_constraint_visible_by(
            constraint,
            others,
            |module, trait_name| module.is_symbol_accessible_from(trait_name, from_module),
            |module, type_def| module.is_type_def_accessible_from(type_def, from_module),
        )
    }

    fn is_type_public(&self, ty: Type, others: &Modules) -> bool {
        self.is_type_visible_by(ty, others, Module::is_type_def_public)
    }

    fn is_type_def_public(&self, id: TypeDefId) -> bool {
        self.try_type_def_name(id)
            .is_some_and(|name| self.is_symbol_public(name))
    }

    fn is_symbol_public(&self, name: Ustr) -> bool {
        self.symbol_visibility(name)
            .is_some_and(Visibility::is_public)
    }

    fn is_trait_public(&self, trait_id: TraitId, others: &Modules) -> bool {
        self.is_trait_visible_by(trait_id, others, Module::is_symbol_public)
    }

    fn is_trait_visible_by(
        &self,
        trait_id: TraitId,
        others: &Modules,
        is_named_trait_visible: impl Fn(&Module, Ustr) -> bool + Copy,
    ) -> bool {
        self.module_for(trait_id.module, others)
            .is_some_and(|module| {
                module
                    .try_trait_name(trait_id)
                    .is_some_and(|name| is_named_trait_visible(module, name))
            })
    }

    fn is_trait_constraint_visible_by(
        &self,
        constraint: &PubTypeConstraint,
        others: &Modules,
        is_named_trait_visible: impl Fn(&Module, Ustr) -> bool + Copy,
        is_named_type_visible: impl Fn(&Module, TypeDefId) -> bool + Copy,
    ) -> bool {
        match constraint {
            PubTypeConstraint::TupleAtIndexIs {
                tuple_ty,
                element_ty,
                ..
            } => {
                self.is_type_visible_by(*tuple_ty, others, is_named_type_visible)
                    && self.is_type_visible_by(*element_ty, others, is_named_type_visible)
            }
            PubTypeConstraint::RecordFieldIs {
                record_ty,
                element_ty,
                ..
            } => {
                self.is_type_visible_by(*record_ty, others, is_named_type_visible)
                    && self.is_type_visible_by(*element_ty, others, is_named_type_visible)
            }
            PubTypeConstraint::TypeHasVariant {
                variant_ty,
                payload_ty,
                ..
            } => {
                self.is_type_visible_by(*variant_ty, others, is_named_type_visible)
                    && self.is_type_visible_by(*payload_ty, others, is_named_type_visible)
            }
            PubTypeConstraint::HaveTrait {
                trait_id,
                input_tys,
                output_tys,
                ..
            } => {
                self.is_trait_visible_by(*trait_id, others, is_named_trait_visible)
                    && input_tys
                        .iter()
                        .chain(output_tys)
                        .all(|ty| self.is_type_visible_by(*ty, others, is_named_type_visible))
            }
        }
    }

    /// Return whether a trait implementation can be exported outside this module.
    pub fn is_trait_impl_exportable(
        &self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        others: &Modules,
    ) -> bool {
        self.is_trait_public(trait_id, others)
            && input_tys
                .iter()
                .chain(output_tys)
                .all(|ty| self.is_type_public(*ty, others))
    }

    /// Return all own definitions in this module.
    pub fn iter_definitions(
        &self,
    ) -> impl Iterator<Item = (LocalDefId, Option<Ustr>, DefKind)> + '_ {
        self.def_table
            .enumerates()
            .map(|(id, def, name)| (id, *name, def.kind))
    }

    /// Return the type for the source pos, if any.
    pub fn type_at(&self, pos: usize) -> Option<Type> {
        for function in self.functions.iter() {
            let ty = function
                .code
                .as_script()
                .and_then(|script_fn| hir::type_at(&self.ir_arena, script_fn.entry_node_id, pos));
            if ty.is_some() {
                return ty;
            }
        }
        None
    }

    /// Look-up a definition by name in this module.
    pub fn get_definition(&self, name: Ustr) -> Option<DefKind> {
        self.def_table.get_by_name(&name).map(|(_, def)| def.kind)
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
        self.find_member(name, others, &|name, module, require_accessible| {
            if require_accessible && !module.is_symbol_accessible_from(ustr(name), self.module_id())
            {
                return None;
            }
            getter(name, module)
        })
    }

    /// Look up an unqualified local or imported member, letting the getter enforce item visibility.
    pub(crate) fn find_member<'a, T>(
        &'a self,
        name: &'a str,
        others: &'a Modules,
        getter: &impl Fn(&'a str, &'a Self, bool) -> Option<T>,
    ) -> Result<Option<(Option<ModuleId>, T)>, InternalCompilationError> {
        if let Some(t) = getter(name, self, false) {
            return Ok(Some((None, t)));
        }

        let u_name = ustr(name);
        if let Some(use_data) = self.uses.explicits.get(&u_name)
            && let Some((module_id, entry)) = others.get_by_name(&use_data.module)
            && let Some(module) = entry.module()
            && let Some(t) = getter(name, module, true)
        {
            return Ok(Some((Some(module_id), t)));
        }

        let mut matches = Vec::new();
        for wildcard_use in &self.uses.wildcards {
            if let Some((module_id, entry)) = others.get_by_name(&wildcard_use.module)
                && let Some(module) = entry.module()
                && let Some(t) = getter(name, module, true)
            {
                matches.push((wildcard_use, module_id, t));
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
                .filter(|(def, name)| {
                    if !def.kind.is_function() {
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

    pub(crate) fn computer_dictionary_ty(
        &self,
        function_ids: &[LocalFunctionId],
        associated_const_tys: impl IntoIterator<Item = Type>,
    ) -> Type {
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
        TraitImpls::dictionary_ty(tys, associated_const_tys)
    }

    fn should_show_symbol(&self, name: Ustr, show_private_items: bool) -> bool {
        show_private_items
            || self
                .symbol_visibility(name)
                .is_some_and(Visibility::is_public)
    }

    pub fn is_generated_lambda_name(name: Ustr) -> bool {
        name.as_str().starts_with(GENERATED_LAMBDA_PREFIX)
    }

    fn should_show_named_function(
        &self,
        name: Ustr,
        show_all_functions: bool,
        show_private_items: bool,
    ) -> bool {
        if !self.should_show_symbol(name, show_private_items) {
            return false;
        }
        if Self::is_generated_lambda_name(name) {
            return show_all_functions;
        }
        show_all_functions || self.is_non_trait_local_function(name)
    }

    fn format_with_modules(
        &self,
        f: &mut fmt::Formatter,
        modules: &Modules,
        show_details: bool,
        show_all_functions: bool,
        show_private_items: bool,
    ) -> fmt::Result {
        let env = ModuleEnv::new(self, modules);
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
        let type_aliases = self
            .type_aliases
            .type_entries()
            .filter(|alias| self.should_show_symbol(alias.name, show_private_items))
            .collect::<Vec<_>>();
        if !type_aliases.is_empty() {
            writeln!(f, "Type aliases ({}):\n", type_aliases.len())?;
            for alias in type_aliases {
                if let Some(doc) = alias.doc_with_fallback(&env) {
                    for line in doc.split('\n') {
                        writeln!(f, "/// {line}")?;
                    }
                }
                write_identifier(f, alias.name.as_str())?;
                let mut ty_var_names = FxHashMap::default();
                if !alias.generic_params.is_empty() {
                    write!(f, "<")?;
                    for (index, (name, _)) in alias.generic_params.iter().enumerate() {
                        if index > 0 {
                            write!(f, ", ")?;
                        }
                        write_identifier(f, name.as_str())?;
                        ty_var_names.insert(TypeVar::new(index as u32), *name);
                    }
                    write!(f, ">")?;
                } else if alias.ty_var_count > 0 {
                    fmt_ordered_quantifiers(f, alias.ty_var_count)?;
                }
                let type_env = TypeDisplayEnv::new(&env, &ty_var_names);
                writeln!(f, ": {}", alias.ty.data().format_with(&type_env))?;
            }
            writeln!(f, "\n")?;
        }
        let bare_native_aliases = self
            .type_aliases
            .bare_native_iter()
            .filter(|(name, _)| self.should_show_symbol(*name, show_private_items))
            .collect::<Vec<_>>();
        if !bare_native_aliases.is_empty() {
            writeln!(
                f,
                "Bare native type aliases ({}):\n",
                bare_native_aliases.len()
            )?;
            for (name, native) in bare_native_aliases {
                writeln!(f, "{}: {}", name, native.type_name())?;
            }
            writeln!(f, "\n")?;
        }
        let type_defs = self
            .type_defs
            .iter()
            .filter(|decl| self.should_show_symbol(decl.name(), show_private_items))
            .collect::<Vec<_>>();
        if !type_defs.is_empty() {
            writeln!(f, "New types ({}):\n", type_defs.len())?;
            for decl in type_defs {
                decl.def().format_details(&env, f)?;
                writeln!(f)?;
            }
            writeln!(f, "\n")?;
        }
        let traits = self
            .traits
            .iter()
            .filter(|trait_def| self.should_show_symbol(trait_def.name, show_private_items))
            .collect::<Vec<_>>();
        if !traits.is_empty() {
            writeln!(f, "Traits ({}):\n", traits.len())?;
            for trait_def in traits {
                writeln!(f, "{}", trait_def.format_with(&env))?;
            }
            writeln!(f)?;
        }
        let shown_impl_count = self
            .impls
            .data
            .iter()
            .filter(|imp| show_private_items || imp.public)
            .count();
        if shown_impl_count > 0 {
            writeln!(f, "Trait implementations ({}):\n", shown_impl_count)?;
            let level = if show_details {
                DisplayFilter::MethodCode
            } else {
                DisplayFilter::MethodDefinitions
            };
            let filter = |_: TraitId, id: LocalImplId| {
                if show_private_items || self.impls.get_impl_by_local_id(id).public {
                    level
                } else {
                    DisplayFilter::Hide
                }
            };
            self.impls.fmt_with_filter(f, &env, filter)?;
        }
        if !self.functions.is_empty() {
            let named_count = self
                .iter_named_functions()
                .filter(|&(name, _)| {
                    self.should_show_named_function(name, show_all_functions, show_private_items)
                })
                .count();
            writeln!(f, "Non-trait impl functions ({}):\n", named_count)?;
            for (i, (name, function)) in self.iter_named_functions().enumerate() {
                if !self.should_show_named_function(name, show_all_functions, show_private_items) {
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
            let mut hidden_trait_functions = 0;
            let mut hidden_lambdas = 0;
            let mut hidden_private_functions = 0;
            let mut hidden_anonymous_functions = self.functions.len();
            for (name, _) in self.iter_named_functions() {
                hidden_anonymous_functions -= 1;
                if self.should_show_named_function(name, show_all_functions, show_private_items) {
                    continue;
                }
                if Self::is_generated_lambda_name(name) {
                    hidden_lambdas += 1;
                } else if !self.is_non_trait_local_function(name) {
                    hidden_trait_functions += 1;
                } else if !self.should_show_symbol(name, show_private_items) {
                    hidden_private_functions += 1;
                }
            }
            let hidden_private_items = if show_private_items {
                0
            } else {
                self.def_table
                    .iter_named()
                    .filter(|(_, def)| !def.kind.is_function() && !def.visibility.is_public())
                    .count()
            };
            let hidden = [
                (hidden_trait_functions, "trait impl functions"),
                (hidden_lambdas, "generated lambda functions"),
                (hidden_private_functions, "private functions"),
                (hidden_private_items, "private items"),
                (hidden_anonymous_functions, "anonymous functions"),
            ]
            .into_iter()
            .filter(|(count, _)| *count > 0)
            .map(|(count, label)| format!("{count} {label}"))
            .join(", ");
            if !hidden.is_empty() {
                writeln!(f, "\nNot showing {hidden}.")?;
            }
        }
        Ok(())
    }
}

impl FormatWith<Modules> for Module {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, data: &Modules) -> fmt::Result {
        self.format_with_modules(f, data, false, false, true)
    }
}

pub struct ShowModuleWithOptions<'a> {
    pub modules: &'a Modules,
    pub show_details: bool,
    pub show_all_functions: bool,
    pub show_private_items: bool,
}

impl<'a> ShowModuleWithOptions<'a> {
    pub fn new(modules: &'a Modules, show_details: bool, show_all_functions: bool) -> Self {
        Self {
            modules,
            show_details,
            show_all_functions,
            show_private_items: show_details,
        }
    }

    pub fn public(modules: &'a Modules) -> Self {
        Self {
            modules,
            show_details: false,
            show_all_functions: false,
            show_private_items: false,
        }
    }
}

impl FormatWith<ShowModuleWithOptions<'_>> for Module {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, options: &ShowModuleWithOptions) -> fmt::Result {
        self.format_with_modules(
            f,
            options.modules,
            options.show_details,
            options.show_all_functions,
            options.show_private_items,
        )
    }
}

pub(crate) fn fmt_ordered_quantifiers(f: &mut fmt::Formatter<'_>, count: u32) -> fmt::Result {
    write!(f, "<")?;
    for i in 0..count {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{}", TypeVar::new(i))?;
    }
    write!(f, ">")
}

// impl FormatWith<ModuleEnv<'_>> for LocalFunction {
//     fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
//         self.function
//             .definition
//             .fmt_with_name_and_module_env(f, self.name, "", env)?;
//         self.function.code.borrow().format_ind(f, env, 1, 1)
//     }
// }
