// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::{fmt, hash::Hash};

use crate::{FxHashMap, module::fmt_ordered_quantifiers};

use derive_new::new;
use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use ustr::Ustr;

use crate::{
    define_id_type,
    format::{FormatWith, write_with_separator_and_format_fn},
    hir::function::Function,
    hir::value::LiteralValue,
    module::{
        LocalDecl, LocalFunctionId, ModuleEnv, ModuleFunction, ModuleId, PendingModuleFunction,
        QualifiedNameEnv, TraitId, Visibility, id::Id, unique_generated_name,
    },
    parser::location::Location,
    types::effects::{EffType, EffectVar, format_effect_binding_value},
    types::r#trait::{
        Trait, TraitAssociatedConstIndex, TraitDictionaryEntryIndex, TraitMethodIndex,
    },
    types::r#type::{Type, TypeVar, fmt_fn_type_with_arg_names},
    types::type_inference::substitution::InstSubst,
    types::type_like::TypeLike,
    types::type_scheme::PubTypeConstraint,
    types::type_scheme_display::format_constraints_consolidated,
};

define_id_type!(
    /// Local trait implementation ID within a module
    LocalImplId
);

define_id_type!(
    /// Import slot ID for cross-module trait implementation dictionaries.
    ImportImplSlotId
);

/// An identifier for a trait implementation
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TraitImplId {
    /// Local trait implementation in a module
    Local(LocalImplId),
    /// Imported trait implementation through an import slot
    Import(ImportImplSlotId),
}

/// Canonical runtime handle to a trait dictionary body owned by a compiled module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TraitDictionaryId {
    pub module_id: ModuleId,
    pub impl_id: LocalImplId,
}

impl FormatWith<ModuleEnv<'_>> for TraitImplId {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        match *self {
            TraitImplId::Local(id) => {
                let imp = env.current.get_impl_data(id).unwrap();
                if let Some(key) = env.current.get_impl_trait_key_by_id(id) {
                    write!(f, "local dictionary ")?;
                    format_impl_header_by_key(f, &key, imp, env)?;
                    write!(f, " (#{id})")
                } else {
                    write!(f, "local anonymous dictionary (#{id})")
                }
            }
            TraitImplId::Import(id) => {
                let slot = env.current.get_import_impl_slot(id).unwrap();
                let module_id = slot.module;
                let module_name = env
                    .modules
                    .get_name(module_id)
                    .unwrap_or_else(|| panic!("imported module {module_id} not found"));
                write!(f, "imported dictionary {module_name}::<")?;
                format_impl_header_by_import_slot(f, slot, env)?;
                write!(f, "> (slot #{id})")
            }
        }
    }
}

/// Import slot that can be resolved to a trait dictionary from another module
#[derive(Debug, Clone)]
pub struct ImportImplSlot {
    /// ID of the module to import from
    pub module: ModuleId,
    /// The key of the trait impl in that module
    pub key: TraitKey,
}

/// A vector of trait definitions.
pub type Traits = Vec<Trait>;

/// A pair of a trait id and a list of input types forming a key for a concrete trait implementations.
#[derive(Debug, Clone, PartialEq, Eq, Hash, new)]
pub struct ConcreteTraitImplKey {
    /// The trait being implemented.
    pub trait_id: TraitId,
    /// The input types of the trait implementation.
    pub input_tys: Vec<Type>,
}

/// A sub-key for looking up blanket implementations for a given trait.
#[derive(Debug, Clone, PartialEq, Eq, Hash, new)]
pub struct BlanketTraitImplSubKey {
    /// The input types of the trait implementation.
    pub input_tys: Vec<Type>,
    /// Number of type variables in this blanket implementation.
    pub ty_var_count: u32,
    /// Number of effect variables in this blanket implementation.
    pub eff_var_count: u32,
    /// The generic constraints necessary to implement the trait.
    pub constraints: Vec<PubTypeConstraint>,
}

/// All necessary information to form a key for a blanket trait implementations.
#[derive(Debug, Clone, PartialEq, Eq, Hash, new)]
pub struct BlanketTraitImplKey {
    /// The trait being implemented.
    pub trait_id: TraitId,
    /// The information to distinguish different blanket implementations for the same trait.
    pub sub_key: BlanketTraitImplSubKey,
}

/// An abstraction of trait key for either concrete or blanket implementations.
#[derive(Debug, Clone, PartialEq, Eq, Hash, EnumAsInner)]
pub enum TraitKey {
    /// A concrete implementation for specific input types
    Concrete(ConcreteTraitImplKey),
    /// A blanket implementation with constraints
    Blanket(BlanketTraitImplKey),
}
impl TraitKey {
    /// Get the input types of this key.
    pub fn input_tys(&self) -> &[Type] {
        match self {
            TraitKey::Concrete(key) => &key.input_tys,
            TraitKey::Blanket(key) => &key.sub_key.input_tys,
        }
    }
    /// Get the trait id of this key.
    pub fn trait_id(&self) -> TraitId {
        match self {
            TraitKey::Concrete(key) => key.trait_id,
            TraitKey::Blanket(key) => key.trait_id,
        }
    }
}

/// Runtime metadata for a trait dictionary.
///
/// Dictionary bodies are module-owned metadata, not Ferlium values. Runtime
/// code passes `TraitDictionaryId` handles around; projecting one entry
/// materializes a normal function value or associated const value.
#[derive(Debug, Clone)]
pub struct TraitDictionary {
    methods: Vec<LocalFunctionId>,
    associated_const_values: Vec<LiteralValue>,
}

/// A projected entry from a runtime trait dictionary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraitDictionaryEntry {
    Method(LocalFunctionId),
    AssociatedConst(LiteralValue),
}

impl TraitDictionary {
    pub fn new(methods: &[LocalFunctionId], associated_const_values: &[LiteralValue]) -> Self {
        Self {
            methods: methods.to_vec(),
            associated_const_values: associated_const_values.to_vec(),
        }
    }

    pub fn entry(&self, index: TraitDictionaryEntryIndex) -> TraitDictionaryEntry {
        let index = index.as_index();
        if index < self.methods.len() {
            TraitDictionaryEntry::Method(self.methods[index])
        } else {
            TraitDictionaryEntry::AssociatedConst(
                self.associated_const_values[index - self.methods.len()].clone(),
            )
        }
    }
}

pub fn build_dictionary_value(
    methods: &[LocalFunctionId],
    associated_const_values: &[LiteralValue],
) -> TraitDictionary {
    TraitDictionary::new(methods, associated_const_values)
}

/// An implementation of a trait.
#[derive(Debug, Clone, new)]
pub struct TraitImpl {
    /// The output types of the trait.
    pub output_tys: Vec<Type>,
    /// The output effects of the trait.
    pub output_effs: Vec<EffType>,
    /// The implemented methods in the module.
    pub methods: Vec<LocalFunctionId>,
    /// Values for associated consts, in trait declaration order.
    #[new(default)]
    pub associated_const_values: Vec<LiteralValue>,
    /// The runtime dictionary, with methods first and associated const values after them.
    pub dictionary_value: TraitDictionary,
    /// The type of the runtime dictionary.
    /// If the implementation is a blanket one, the key contains the rest of the type scheme.
    pub dictionary_ty: Type,
    /// Visibility, hand-written implementations are public, derived ones are private.
    pub public: bool,
    /// Location of the source implementation when it comes from Ferlium code.
    pub source_span: Option<Location>,
}

impl TraitImpl {
    pub fn with_associated_const_values(
        mut self,
        associated_const_values: impl Into<Vec<LiteralValue>>,
    ) -> Self {
        self.associated_const_values = associated_const_values.into();
        self
    }

    pub fn associated_const_value(&self, index: TraitAssociatedConstIndex) -> Option<LiteralValue> {
        self.associated_const_values
            .get(usize::from(index))
            .cloned()
    }
}

/// Collects final local functions to be added to a module when adding trait implementations.
#[derive(Clone, Debug, new)]
pub struct FunctionCollector {
    pub initial_count: usize,
    #[new(default)]
    pub new_elements: Vec<(Ustr, ModuleFunction)>,
}

/// Collects generated HIR functions that must still be elaborated before they are stored in a module.
#[derive(Clone, Debug, new)]
pub struct PendingFunctionCollector {
    pub initial_count: usize,
    /// `None` marks a reserved slot whose body will be supplied by `replace`.
    #[new(default)]
    pub new_elements: Vec<(Ustr, Option<PendingModuleFunction>, Visibility)>,
}

impl FunctionCollector {
    fn existing_index_for_name(&self, name: Ustr) -> Option<usize> {
        self.new_elements
            .iter()
            .position(|&(fn_name, _)| fn_name == name)
    }

    pub(crate) fn unique_generated_name(&self, base_name: Ustr) -> Ustr {
        unique_generated_name(base_name, |name| {
            self.existing_index_for_name(name).is_some()
        })
    }

    pub fn next_id(&self) -> LocalFunctionId {
        LocalFunctionId::from_index(self.initial_count + self.new_elements.len())
    }

    pub fn push(&mut self, name: Ustr, mut function: ModuleFunction) {
        let name = self.unique_generated_name(name);
        function.assign_local_slots();
        self.new_elements.push((name, function));
    }

    pub fn get_function(&self, name: Ustr) -> Option<LocalFunctionId> {
        self.existing_index_for_name(name)
            .map(|i| LocalFunctionId::from_index(self.initial_count + i))
    }
}

impl PendingFunctionCollector {
    fn existing_index_for_name(&self, name: Ustr) -> Option<usize> {
        self.new_elements
            .iter()
            .position(|(fn_name, _, _)| *fn_name == name)
    }

    pub(crate) fn unique_generated_name(&self, base_name: Ustr) -> Ustr {
        unique_generated_name(base_name, |name| {
            self.existing_index_for_name(name).is_some()
        })
    }

    pub fn next_id(&self) -> LocalFunctionId {
        LocalFunctionId::from_index(self.initial_count + self.new_elements.len())
    }

    pub fn push(&mut self, name: Ustr, function: PendingModuleFunction) {
        self.push_with_visibility(name, function, Visibility::Public);
    }

    pub fn push_with_visibility(
        &mut self,
        name: Ustr,
        mut function: PendingModuleFunction,
        visibility: Visibility,
    ) {
        let name = self.unique_generated_name(name);
        function.assign_local_slots();
        self.new_elements.push((name, Some(function), visibility));
    }

    pub fn reserve(&mut self, name: Ustr) {
        self.reserve_with_visibility(name, Visibility::Public);
    }

    pub fn reserve_with_visibility(&mut self, name: Ustr, visibility: Visibility) {
        let name = self.unique_generated_name(name);
        self.new_elements.push((name, None, visibility));
    }

    pub(crate) fn replace(&mut self, id: LocalFunctionId, mut function: PendingModuleFunction) {
        function.assign_local_slots();
        let index = id
            .as_index()
            .checked_sub(self.initial_count)
            .expect("cannot replace an already committed function");
        self.new_elements[index].1 = Some(function);
    }

    pub fn get_function(&self, name: Ustr) -> Option<LocalFunctionId> {
        self.existing_index_for_name(name)
            .map(|i| LocalFunctionId::from_index(self.initial_count + i))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DisplayFilter {
    Hide,
    ImplSignature,
    MethodDefinitions,
    MethodCode,
}

pub(crate) type ConcreteImpls = FxHashMap<ConcreteTraitImplKey, LocalImplId>;
pub(crate) type BlanketTraitImpls = FxHashMap<BlanketTraitImplSubKey, LocalImplId>;
pub(crate) type BlanketImpls = FxHashMap<TraitId, BlanketTraitImpls>;

/// All trait implementations in a module or in a given context.
#[derive(Clone, Debug, new)]
pub struct TraitImpls {
    /// The ID of the module this TraitImpls belongs to, used to construct dictionary values.
    pub(crate) module_id: ModuleId,
    #[new(default)]
    pub(crate) concrete_key_to_id: ConcreteImpls,
    #[new(default)]
    pub(crate) blanket_key_to_id: BlanketImpls,
    #[new(default)]
    pub(crate) data: Vec<TraitImpl>,
}

impl TraitImpls {
    /// Add a concrete trait implementation to this module, with final raw functions.
    /// The definition will be retrieved by instantiating the trait method definitions with the given types.
    /// The caller is responsible to ensure that the input and output types match the trait definition
    /// and that the constraints are satisfied.
    /// An empty `output_effs` defaults to all-empty output effects.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn add_concrete_raw(
        &mut self,
        trait_id: TraitId,
        trait_def: &Trait,
        input_tys: impl Into<Vec<Type>>,
        output_tys: impl Into<Vec<Type>>,
        output_effs: impl Into<Vec<EffType>>,
        associated_const_values: impl Into<Vec<LiteralValue>>,
        functions: impl Into<Vec<(Function, Vec<LocalDecl>)>>,
        fn_collector: &mut FunctionCollector,
        qualified_name_env: &QualifiedNameEnv<'_>,
    ) -> LocalImplId {
        let input_tys = input_tys.into();
        let output_tys = output_tys.into();
        let output_effs = trait_def.impl_output_effs_or_pure_defaults(output_effs.into());
        let associated_const_values = associated_const_values.into();

        // Recover the definitions from the trait by instantiating the trait method definitions with the given types.
        let definitions = trait_def.instantiate_for_tys(&input_tys, &output_tys, &output_effs);

        // Combine them into module functions.
        let functions: Vec<_> = definitions
            .into_iter()
            .zip(functions.into())
            .map(|(def, (function, locals))| {
                ModuleFunction::new_without_debug_info(def, function, None, locals)
            })
            .collect();

        // Add the impl, collecting new functions.
        self.add_concrete(
            trait_id,
            trait_def,
            input_tys,
            output_tys,
            output_effs,
            associated_const_values,
            functions,
            fn_collector,
            qualified_name_env,
        )
    }

    /// Add a concrete trait implementation, with module functions.
    /// The caller is responsible to ensure that the input and output types match the trait definition
    /// and that the constraints are satisfied.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn add_concrete(
        &mut self,
        trait_id: TraitId,
        trait_def: &Trait,
        input_tys: Vec<Type>,
        output_tys: Vec<Type>,
        output_effs: Vec<EffType>,
        associated_const_values: impl Into<Vec<LiteralValue>>,
        functions: Vec<ModuleFunction>,
        fn_collector: &mut FunctionCollector,
        qualified_name_env: &QualifiedNameEnv<'_>,
    ) -> LocalImplId {
        let output_effs = trait_def.impl_output_effs_or_pure_defaults(output_effs);
        let associated_const_values = associated_const_values.into();
        // Minimal validation
        trait_def.validate_impl_shape(
            &input_tys,
            &output_tys,
            &output_effs,
            associated_const_values.len(),
            functions.len(),
        );

        // Add to local functions, collect their IDs and build the overall interface hash.
        let namer = |method_index: usize| {
            qualified_name_env
                .disambiguated_impl_method_name(
                    trait_id,
                    trait_def,
                    TraitMethodIndex::from_index(method_index),
                    &input_tys,
                    &output_tys,
                    &output_effs,
                    0,
                    0,
                    &[],
                )
                .into()
        };
        let (methods, method_tys) = Self::bundle_module_functions(functions, fn_collector, namer);

        // Build and insert the implementation.
        let associated_const_tys = trait_def.instantiate_associated_const_tys_for_tys(
            &input_tys,
            &output_tys,
            &output_effs,
        );
        let dictionary_type = Self::dictionary_ty(method_tys, associated_const_tys);
        let dictionary_value = build_dictionary_value(&methods, &associated_const_values);
        let imp = TraitImpl::new(
            output_tys,
            output_effs,
            methods,
            dictionary_value,
            dictionary_type,
            true,
            None,
        )
        .with_associated_const_values(associated_const_values);
        let key = ConcreteTraitImplKey::new(trait_id, input_tys);
        self.add_concrete_struct(key, imp)
    }

    /// Add a concrete trait implementation whose methods still need HIR elaboration.
    /// The caller is responsible to provide functions whose definitions match the trait instance.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn add_concrete_pending(
        &mut self,
        trait_id: TraitId,
        trait_def: &Trait,
        input_tys: Vec<Type>,
        output_tys: Vec<Type>,
        output_effs: Vec<EffType>,
        associated_const_values: impl Into<Vec<LiteralValue>>,
        functions: Vec<PendingModuleFunction>,
        fn_collector: &mut PendingFunctionCollector,
        qualified_name_env: &QualifiedNameEnv<'_>,
    ) -> LocalImplId {
        let output_effs = trait_def.impl_output_effs_or_pure_defaults(output_effs);
        let associated_const_values = associated_const_values.into();
        trait_def.validate_impl_shape(
            &input_tys,
            &output_tys,
            &output_effs,
            associated_const_values.len(),
            functions.len(),
        );

        let namer = |method_index: usize| {
            qualified_name_env
                .disambiguated_impl_method_name(
                    trait_id,
                    trait_def,
                    TraitMethodIndex::from_index(method_index),
                    &input_tys,
                    &output_tys,
                    &output_effs,
                    0,
                    0,
                    &[],
                )
                .into()
        };
        let (methods, method_tys) =
            Self::bundle_pending_module_functions(functions, fn_collector, namer);

        let associated_const_tys = trait_def.instantiate_associated_const_tys_for_tys(
            &input_tys,
            &output_tys,
            &output_effs,
        );
        let dictionary_type = Self::dictionary_ty(method_tys, associated_const_tys);
        let dictionary_value = build_dictionary_value(&methods, &associated_const_values);
        let imp = TraitImpl::new(
            output_tys,
            output_effs,
            methods,
            dictionary_value,
            dictionary_type,
            true,
            None,
        )
        .with_associated_const_values(associated_const_values);
        let key = ConcreteTraitImplKey::new(trait_id, input_tys);
        self.add_concrete_struct(key, imp)
    }

    /// Add a concrete trait implementation structure, returning its local id.
    pub fn add_concrete_struct(
        &mut self,
        key: ConcreteTraitImplKey,
        imp: TraitImpl,
    ) -> LocalImplId {
        let id = LocalImplId::from_index(self.data.len());
        self.data.push(imp);
        self.concrete_key_to_id.insert(key, id);
        id
    }

    /// Add a module-owned runtime dictionary that is not a selectable trait impl.
    pub fn add_anonymous_dictionary_struct(&mut self, imp: TraitImpl) -> LocalImplId {
        let id = LocalImplId::from_index(self.data.len());
        self.data.push(imp);
        id
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn add_blanket_raw(
        &mut self,
        trait_id: TraitId,
        trait_def: &Trait,
        sub_key: BlanketTraitImplSubKey,
        output_tys: impl Into<Vec<Type>>,
        output_effs: impl Into<Vec<EffType>>,
        associated_const_values: impl Into<Vec<LiteralValue>>,
        functions: impl Into<Vec<(Function, Vec<LocalDecl>)>>,
        fn_collector: &mut FunctionCollector,
        qualified_name_env: &QualifiedNameEnv<'_>,
    ) -> LocalImplId {
        let output_tys = output_tys.into();
        let output_effs = trait_def.impl_output_effs_or_pure_defaults(output_effs.into());
        let associated_const_values = associated_const_values.into();

        // Recover the definitions from the trait by instantiating the trait method definitions with the given types.
        let definitions =
            trait_def.instantiate_for_tys(&sub_key.input_tys, &output_tys, &output_effs);

        // Combine them into module functions.
        let functions: Vec<_> = definitions
            .into_iter()
            .zip(functions.into())
            .map(|(def, (function, locals))| {
                ModuleFunction::new_without_debug_info(def, function, None, locals)
            })
            .collect();

        // Add the impl, collecting new functions.
        self.add_blanket(
            trait_id,
            trait_def,
            sub_key,
            output_tys,
            output_effs,
            associated_const_values,
            functions,
            fn_collector,
            qualified_name_env,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn add_blanket(
        &mut self,
        trait_id: TraitId,
        trait_def: &Trait,
        sub_key: BlanketTraitImplSubKey,
        output_tys: Vec<Type>,
        output_effs: Vec<EffType>,
        associated_const_values: impl Into<Vec<LiteralValue>>,
        functions: Vec<ModuleFunction>,
        fn_collector: &mut FunctionCollector,
        qualified_name_env: &QualifiedNameEnv<'_>,
    ) -> LocalImplId {
        let output_effs = trait_def.impl_output_effs_or_pure_defaults(output_effs);
        let associated_const_values = associated_const_values.into();
        // Minimal validation
        trait_def.validate_impl_shape(
            &sub_key.input_tys,
            &output_tys,
            &output_effs,
            associated_const_values.len(),
            functions.len(),
        );

        // Add to local functions, collect their IDs and build the overall interface hash.
        let namer = |method_index: usize| {
            qualified_name_env
                .disambiguated_impl_method_name(
                    trait_id,
                    trait_def,
                    TraitMethodIndex::from_index(method_index),
                    &sub_key.input_tys,
                    &output_tys,
                    &output_effs,
                    sub_key.ty_var_count,
                    sub_key.eff_var_count,
                    &sub_key.constraints,
                )
                .into()
        };
        let (methods, method_tys) = Self::bundle_module_functions(functions, fn_collector, namer);

        // Build and insert the implementation.
        let associated_const_tys = trait_def.instantiate_associated_const_tys_for_tys(
            &sub_key.input_tys,
            &output_tys,
            &output_effs,
        );
        let dictionary_type = Self::dictionary_ty(method_tys, associated_const_tys);
        let dictionary_value = build_dictionary_value(&methods, &associated_const_values);
        let imp = TraitImpl::new(
            output_tys,
            output_effs,
            methods,
            dictionary_value,
            dictionary_type,
            true,
            None,
        )
        .with_associated_const_values(associated_const_values);
        let key = BlanketTraitImplKey::new(trait_id, sub_key);
        self.add_blanket_struct(key, imp)
    }

    /// Add a blanket trait implementation structure, returning its local id.
    pub fn add_blanket_struct(&mut self, key: BlanketTraitImplKey, imp: TraitImpl) -> LocalImplId {
        let id = LocalImplId::from_index(self.data.len());
        self.data.push(imp);
        self.blanket_key_to_id
            .entry(key.trait_id)
            .or_default()
            .insert(key.sub_key, id);
        id
    }

    /// Bundle a set of module functions into a local functions,
    /// a cached dictionary value, and the overall interface hash.
    fn bundle_module_functions(
        functions: Vec<ModuleFunction>,
        fn_collector: &mut FunctionCollector,
        namer: impl Fn(usize) -> Ustr,
    ) -> (Vec<LocalFunctionId>, Vec<Type>) {
        let (methods, tys): (Vec<_>, Vec<_>) = functions
            .into_iter()
            .enumerate()
            .map(|(index, function)| {
                let id = fn_collector.next_id();
                let fn_ty = Type::function_type(function.definition.ty_scheme.ty.clone());
                fn_collector.push(namer(index), function);
                (id, fn_ty)
            })
            .multiunzip();
        (methods, tys)
    }

    /// Bundle a set of pending module functions into local function IDs and interface types.
    fn bundle_pending_module_functions(
        functions: Vec<PendingModuleFunction>,
        fn_collector: &mut PendingFunctionCollector,
        namer: impl Fn(usize) -> Ustr,
    ) -> (Vec<LocalFunctionId>, Vec<Type>) {
        let (methods, tys): (Vec<_>, Vec<_>) = functions
            .into_iter()
            .enumerate()
            .map(|(index, function)| {
                let id = fn_collector.next_id();
                let fn_ty = Type::function_type(function.definition.ty_scheme.ty.clone());
                fn_collector.push(namer(index), function);
                (id, fn_ty)
            })
            .multiunzip();
        (methods, tys)
    }

    pub fn dictionary_ty(
        method_tys: Vec<Type>,
        associated_const_tys: impl IntoIterator<Item = Type>,
    ) -> Type {
        Type::tuple(
            method_tys
                .into_iter()
                .chain(associated_const_tys)
                .collect::<Vec<_>>(),
        )
    }

    pub fn concrete(&self) -> &ConcreteImpls {
        &self.concrete_key_to_id
    }

    pub fn blanket(&self) -> &BlanketImpls {
        &self.blanket_key_to_id
    }

    pub fn get_impl_by_key(&self, key: &TraitKey) -> Option<&TraitImpl> {
        self.get_impl_id_by_key(key)
            .map(|id| self.get_impl_by_local_id(id))
    }

    pub fn get_impl_id_by_key(&self, key: &TraitKey) -> Option<LocalImplId> {
        use TraitKey::*;
        match key {
            Concrete(key) => self.concrete_key_to_id.get(key).copied(),
            Blanket(key) => self
                .blanket_key_to_id
                .get(&key.trait_id)
                .and_then(|m| m.get(&key.sub_key))
                .copied(),
        }
    }

    pub fn get_impl_by_local_id(&self, id: LocalImplId) -> &TraitImpl {
        &self.data[id.as_index()]
    }

    pub fn get_key_by_local_id(&self, id: LocalImplId) -> Option<TraitKey> {
        self.concrete_key_to_id
            .iter()
            .find_map(|(key, &val)| {
                if val == id {
                    Some(TraitKey::Concrete(key.clone()))
                } else {
                    None
                }
            })
            .or_else(|| {
                self.blanket_key_to_id.iter().find_map(|(trait_id, map)| {
                    map.iter().find_map(|(sub_key, &val)| {
                        if val == id {
                            Some(TraitKey::Blanket(BlanketTraitImplKey::new(
                                *trait_id,
                                sub_key.clone(),
                            )))
                        } else {
                            None
                        }
                    })
                })
            })
    }

    pub fn is_empty(&self) -> bool {
        self.concrete_key_to_id.is_empty() && self.blanket_key_to_id.is_empty()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub(crate) fn fmt_with_filter(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
        filter: impl Fn(TraitId, LocalImplId) -> DisplayFilter,
    ) -> std::fmt::Result {
        for (key, id) in &self.concrete_key_to_id {
            let imp = self.get_impl_by_local_id(*id);
            let level = filter(key.trait_id, *id);
            if level == DisplayFilter::Hide {
                continue;
            }
            let subst =
                format_concrete_impl_header(key, &imp.output_tys, &imp.output_effs, f, env)?;
            write!(f, " (#{id})")?;
            if level == DisplayFilter::MethodDefinitions {
                format_impl_fns(key.trait_id, subst, imp, false, f, env)?;
            } else if level == DisplayFilter::MethodCode {
                format_impl_fns(key.trait_id, subst, imp, true, f, env)?;
            }
            writeln!(f)?;
        }
        for (trait_id, impls) in &self.blanket_key_to_id {
            for (sub_key, id) in impls {
                let level = filter(*trait_id, *id);
                if level == DisplayFilter::Hide {
                    continue;
                }
                let imp = self.get_impl_by_local_id(*id);
                let key = BlanketTraitImplKey::new(*trait_id, sub_key.clone());
                format_blanket_impl_header(&key, &imp.output_tys, &imp.output_effs, f, env)?;
                write!(f, " (#{id})")?;
                // For blanket impls, the function types already use the correct type variables,
                // so we don't need to apply any substitution.
                if level == DisplayFilter::MethodDefinitions {
                    format_impl_fns(key.trait_id, InstSubst::default(), imp, false, f, env)?;
                } else if level == DisplayFilter::MethodCode {
                    format_impl_fns(key.trait_id, InstSubst::default(), imp, true, f, env)?;
                }
                writeln!(f)?;
            }
        }
        Ok(())
    }

    pub fn format_impl_header_by_id(
        &self,
        id: LocalImplId,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
    ) -> std::fmt::Result {
        let key = &self
            .get_key_by_local_id(id)
            .expect("local impl id not found");
        let imp = self.get_impl_by_local_id(id);
        format_impl_header_by_key(f, key, imp, env)?;
        Ok(())
    }

    pub fn log_debug_impls_headers(&self, trait_id: TraitId, module_env: ModuleEnv<'_>) {
        let filter = |id: TraitId, _| {
            if id == trait_id {
                DisplayFilter::ImplSignature
            } else {
                DisplayFilter::Hide
            }
        };
        log::debug!("{}", self.format_with(&(module_env, filter)));
    }

    pub fn impl_header_to_string_by_id(
        &self,
        id: LocalImplId,
        module_env: ModuleEnv<'_>,
    ) -> String {
        let filter = |_: TraitId, impl_id| {
            if impl_id == id {
                DisplayFilter::ImplSignature
            } else {
                DisplayFilter::Hide
            }
        };
        format!("{}", self.format_with(&(module_env, filter)))
    }
}

impl FormatWith<ModuleEnv<'_>> for TraitImpls {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        self.fmt_with_filter(f, env, |_, _| DisplayFilter::MethodDefinitions)
    }
}

impl<F> FormatWith<(ModuleEnv<'_>, F)> for TraitImpls
where
    F: Fn(TraitId, LocalImplId) -> DisplayFilter,
{
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, data: &(ModuleEnv<'_>, F)) -> fmt::Result {
        self.fmt_with_filter(f, &data.0, &data.1)
    }
}

pub fn format_concrete_impl(
    key: &ConcreteTraitImplKey,
    imp: &TraitImpl,
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> std::fmt::Result {
    let subst = format_concrete_impl_header(key, &imp.output_tys, &imp.output_effs, f, env)?;
    format_impl_fns(key.trait_id, subst, imp, false, f, env)
}

pub fn format_blanket_impl(
    key: &BlanketTraitImplKey,
    imp: &TraitImpl,
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> std::fmt::Result {
    format_blanket_impl_header(key, &imp.output_tys, &imp.output_effs, f, env)?;
    // For blanket impls, the function types already use the correct type variables,
    // so we don't need to apply any substitution.
    format_impl_fns(key.trait_id, InstSubst::default(), imp, false, f, env)
}

pub fn format_impl_header_by_key(
    f: &mut fmt::Formatter,
    key: &TraitKey,
    imp: &TraitImpl,
    env: &ModuleEnv,
) -> Result<InstSubst, std::fmt::Error> {
    use TraitKey::*;
    match key {
        Concrete(key) => {
            format_concrete_impl_header(key, &imp.output_tys, &imp.output_effs, f, env)
        }
        Blanket(key) => format_blanket_impl_header(key, &imp.output_tys, &imp.output_effs, f, env),
    }
}

pub fn format_blanket_impl_header(
    key: &BlanketTraitImplKey,
    output_tys: &[Type],
    output_effs: &[EffType],
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> Result<InstSubst, std::fmt::Error> {
    let subst = format_impl_header_expanded(
        key.trait_id,
        key.sub_key.ty_var_count,
        &key.sub_key.input_tys,
        output_tys,
        output_effs,
        f,
        env,
    )?;
    let constraints = &key.sub_key.constraints;
    if !constraints.is_empty() {
        write!(f, " where ")?;
        format_constraints_consolidated(constraints, f, env)?;
    }
    Ok(subst)
}

pub fn format_concrete_impl_header(
    key: &ConcreteTraitImplKey,
    output_tys: &[Type],
    output_effs: &[EffType],
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> Result<InstSubst, std::fmt::Error> {
    format_impl_header_expanded(
        key.trait_id,
        0,
        &key.input_tys,
        output_tys,
        output_effs,
        f,
        env,
    )
}

#[allow(clippy::too_many_arguments)]
fn format_impl_header_expanded(
    trait_id: TraitId,
    ty_var_count: u32,
    input_tys: &[Type],
    output_tys: &[Type],
    output_effs: &[EffType],
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> Result<InstSubst, std::fmt::Error> {
    let trait_def = env.trait_def(trait_id);
    write!(f, "impl")?;
    if ty_var_count > 0 {
        fmt_ordered_quantifiers(f, ty_var_count)?;
    }
    if input_tys.len() == 1 && output_tys.is_empty() && output_effs.is_empty() {
        write!(
            f,
            " {} for {}",
            trait_def.name,
            input_tys[0].format_with(env)
        )?;
    } else {
        write!(f, " {} for <", trait_def.name)?;
        write_with_separator_and_format_fn(
            input_tys.iter().zip(trait_def.input_type_names.iter()),
            ", ",
            |(ty, name), f| write!(f, "{} = {}", name, ty.format_with(env)),
            f,
        )?;
        if !output_tys.is_empty() {
            write!(f, " |-> ")?;
            write_with_separator_and_format_fn(
                output_tys.iter().zip(trait_def.output_type_names.iter()),
                ", ",
                |(ty, name), f| write!(f, "{} = {}", name, ty.format_with(env)),
                f,
            )?;
        }
        if !output_effs.is_empty() {
            write!(f, " ! ")?;
            write_with_separator_and_format_fn(
                output_effs.iter().zip(trait_def.output_effect_names.iter()),
                ", ",
                |(eff, name), f| {
                    write!(f, "{name} = ")?;
                    format_effect_binding_value(eff, f)
                },
                f,
            )?;
        }
        write!(f, ">")?;
    }
    let mut subst = InstSubst::default();
    for (i, ty) in input_tys.iter().enumerate() {
        subst.0.insert(TypeVar::new(i as u32), *ty);
    }
    for (i, ty) in output_tys.iter().enumerate() {
        subst
            .0
            .insert(TypeVar::new(i as u32 + input_tys.len() as u32), *ty);
    }
    for (i, eff) in output_effs.iter().enumerate() {
        subst.1.insert(EffectVar::new(i as u32), eff.clone());
    }
    Ok(subst)
}

fn format_impl_fns(
    trait_id: TraitId,
    subst: InstSubst,
    imp: &TraitImpl,
    show_code: bool,
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> std::fmt::Result {
    let trait_def = env.trait_def(trait_id);
    writeln!(f, " {{")?;
    let impl_functions = imp.methods.iter().map(|&id| {
        let function = env.current.get_function_by_id(id).unwrap();
        (function, id)
    });
    for ((name, _), (function, id)) in trait_def.methods.iter().zip(impl_functions) {
        format_impl_fn(*name, function, id, &subst, show_code, f, env)?;
    }
    writeln!(f, "}}")
}

fn format_impl_fn(
    name: Ustr,
    function: &ModuleFunction,
    id: LocalFunctionId,
    subst: &InstSubst,
    show_code: bool,
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> std::fmt::Result {
    let def = &function.definition;
    let ty = def.ty_scheme.ty.instantiate_simple(subst);
    write!(f, "    fn {name}")?;
    fmt_fn_type_with_arg_names(&ty, &def.arg_names, f, env)?;
    if def.ty_scheme.constraints.is_empty() {
        writeln!(f, " (#{id})")?;
    } else {
        write!(f, " where ")?;
        format_constraints_consolidated(&def.ty_scheme.constraints, f, env)?;
        writeln!(f, " (#{id})")?;
    }
    if show_code {
        function.fmt_code_ind(f, env, 2, 1)?;
    }
    Ok(())
}

pub fn format_impl_header_by_import_slot_id(
    f: &mut fmt::Formatter,
    id: ImportImplSlotId,
    env: &ModuleEnv<'_>,
) -> fmt::Result {
    let slot = env.current.get_import_impl_slot(id).unwrap();
    format_impl_header_by_import_slot(f, slot, env)
}

pub fn format_impl_header_by_import_slot(
    f: &mut fmt::Formatter,
    slot: &ImportImplSlot,
    env: &ModuleEnv<'_>,
) -> fmt::Result {
    let key = &slot.key;
    let imp = &env
        .modules
        .get(slot.module)
        .expect("imported module not found")
        .module
        .as_ref()
        .expect("compiled module not found")
        .get_impl_data_by_trait_key(key)
        .expect("imported trait impl not found");
    format_impl_header_by_key(f, key, imp, env)?;
    Ok(())
}
