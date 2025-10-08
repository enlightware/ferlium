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
    collections::HashMap,
    fmt,
    hash::{DefaultHasher, Hash, Hasher},
    rc::Rc,
};

use derive_new::new;
use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use ustr::Ustr;

use crate::{
    define_id_type,
    format::{FormatWith, write_with_separator_and_format_fn},
    function::{Function, FunctionDefinition, FunctionRc},
    module::{LocalFunction, LocalFunctionId, ModuleEnv, ModuleFunction, ModuleRc},
    r#trait::TraitRef,
    r#type::{Type, TypeSubstitution, TypeVar, fmt_fn_type_with_arg_names},
    type_inference::InstSubstitution,
    type_like::TypeLike,
    type_scheme::{PubTypeConstraint, format_constraints_consolidated},
    value::Value,
};

define_id_type!(
    /// Local trait implementation ID within a module
    LocalImplId
);

define_id_type!(
    /// Import slot ID for cross-module trait references
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

impl FormatWith<ModuleEnv<'_>> for TraitImplId {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        match self {
            TraitImplId::Local(id) => {
                let key = env.current.impls.get_key_by_local_id(*id).unwrap();
                let imp = &env.current.impls.data[id.as_index()];
                write!(f, "local dictionary ")?;
                format_impl_header_by_key(f, &key, imp, env)?;
                write!(f, " (#{id})")
            }
            TraitImplId::Import(id) => {
                let slot = &env.current.import_impl_slots[id.as_index()];
                let module_name = slot.module_name;
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
    /// Name of the module to import from
    pub module_name: Ustr,
    /// The key of the trait impl in that module
    pub key: TraitKey,
    /// Cached resolved dictionary/module and its interface hash - updated during relinking
    /// Note: we must hold the module to keep it alive, as otherwise the FunctionValue inside Value
    /// would have a module field that could fail to upgrade at runtime if the module would have been dropped.
    pub resolved: RefCell<Option<(Value, ModuleRc, u64)>>,
}

/// A vector of traits.
pub type Traits = Vec<TraitRef>;

/// A pair of a trait reference and a list of input types forming a key for a concrete trait implementations.
#[derive(Debug, Clone, PartialEq, Eq, Hash, new)]
pub struct ConcreteTraitImplKey {
    /// The trait we are referring to, currently global
    pub trait_ref: TraitRef,
    /// The input types of the trait implementation.
    pub input_tys: Vec<Type>,
}

/* Use this later instead of trait_ref if we want to identify traits
    by module + name instead of global pointer:
    /// Module that defines the trait
    trait_module: Ustr,
    /// Name of the trait in that module
    trait_name: Ustr,
*/

/// A sub-key for looking up blanket implementations for a given trait.
#[derive(Debug, Clone, PartialEq, Eq, Hash, new)]
pub struct BlanketTraitImplSubKey {
    /// The input types of the trait implementation.
    pub input_tys: Vec<Type>,
    /// Number of type variables in this blanket implementation.
    pub ty_var_count: u32,
    /// The generic constraints necessary to implement the trait.
    pub constraints: Vec<PubTypeConstraint>,
}

/// All necessary information to form a key for a blanket trait implementations.
#[derive(Debug, Clone, PartialEq, Eq, Hash, new)]
pub struct BlanketTraitImplKey {
    /// The trait we are referring to, currently global
    pub trait_ref: TraitRef,
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
    /// Get the trait reference of this key.
    pub fn trait_ref(&self) -> &TraitRef {
        match self {
            TraitKey::Concrete(key) => &key.trait_ref,
            TraitKey::Blanket(key) => &key.trait_ref,
        }
    }
}

/// An implementation of a trait.
#[derive(Debug, Clone, new)]
pub struct TraitImpl {
    /// The output types of the trait.
    pub output_tys: Vec<Type>,
    /// The implemented methods in the module.
    pub methods: Vec<LocalFunctionId>,
    /// Global hash of the trait interface (name and type of methods).
    pub interface_hash: u64,
    /// The implemented methods, in a tuple of first-class functions of the proper types.
    pub dictionary_value: RefCell<Value>,
    /// The type of the dictionary, a tuple of function types.
    /// If the implementation is a blanket one, the key contains the rest of the type scheme.
    pub dictionary_ty: Type,
    /// Visibility, hand-written implementations are public, derived ones are private.
    pub public: bool,
}

/// Collects new local functions to be added to a module when adding trait implementations.
#[derive(Clone, Debug, new)]
pub struct FunctionCollector {
    pub initial_count: usize,
    #[new(default)]
    pub new_elements: Vec<LocalFunction>,
}
impl FunctionCollector {
    fn next_id(&self) -> LocalFunctionId {
        LocalFunctionId::from_index(self.initial_count + self.new_elements.len())
    }
    fn push(&mut self, function: LocalFunction) {
        self.new_elements.push(function);
    }

    pub fn get_function(&self, name: Ustr) -> Option<LocalFunctionId> {
        self.new_elements
            .iter()
            .position(|function| function.name == Some(name))
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

pub(crate) type ConcreteImpls = HashMap<ConcreteTraitImplKey, LocalImplId>;
pub(crate) type BlanketTraitImpls = HashMap<BlanketTraitImplSubKey, LocalImplId>;
pub(crate) type BlanketImpls = HashMap<TraitRef, BlanketTraitImpls>;

/// All trait implementations in a module or in a given context.
#[derive(Clone, Debug, Default)]
pub struct TraitImpls {
    pub(crate) concrete_key_to_id: ConcreteImpls,
    pub(crate) blanket_key_to_id: BlanketImpls,
    pub(crate) data: Vec<TraitImpl>,
}

impl TraitImpls {
    /// Add a concrete trait implementation to this module, with raw functions.
    /// The definition will be retrieved by instantiating the trait method definitions with the given types.
    /// The caller is responsible to ensure that the input and output types match the trait reference
    /// and that the constraints are satisfied.
    pub fn add_concrete_raw(
        &mut self,
        trait_ref: TraitRef,
        input_tys: impl Into<Vec<Type>>,
        output_tys: impl Into<Vec<Type>>,
        functions: impl Into<Vec<Function>>,
        fn_collector: &mut FunctionCollector,
    ) -> LocalImplId {
        let input_tys = input_tys.into();
        let output_tys = output_tys.into();

        // Recover the definitions from the trait reference by instantiating the trait method definitions with the given types.
        let definitions = trait_ref.instantiate_for_tys(&input_tys, &output_tys);

        // Combine them into module functions.
        let functions: Vec<_> = definitions
            .into_iter()
            .zip(functions.into())
            .map(|(def, function)| {
                ModuleFunction::new_without_spans(def, Rc::new(RefCell::new(function)))
            })
            .collect();

        // Add the impl, collecting new functions.
        self.add_concrete(trait_ref, input_tys, output_tys, functions, fn_collector)
    }

    /// Add a concrete trait implementation, with module functions.
    /// The caller is responsible to ensure that the input and output types match the trait reference
    /// and that the constraints are satisfied.
    pub fn add_concrete(
        &mut self,
        trait_ref: TraitRef,
        input_tys: Vec<Type>,
        output_tys: Vec<Type>,
        functions: Vec<ModuleFunction>,
        fn_collector: &mut FunctionCollector,
    ) -> LocalImplId {
        // Minimal validation
        trait_ref.validate_impl_size(&input_tys, &output_tys, functions.len());

        // Add to local functions, collect their IDs and build the overall interface hash.
        let (methods, dictionary_value, dictionary_type, interface_hash) =
            Self::bundle_module_functions(functions, fn_collector);

        // Build and insert the implementation.
        let imp = TraitImpl::new(
            output_tys,
            methods,
            interface_hash,
            RefCell::new(dictionary_value),
            dictionary_type,
            true,
        );
        let key = ConcreteTraitImplKey::new(trait_ref, input_tys);
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

    /// Add a blanket trait implementation structure, returning its local id.
    pub fn add_blanket_struct(&mut self, key: BlanketTraitImplKey, imp: TraitImpl) -> LocalImplId {
        let id = LocalImplId::from_index(self.data.len());
        self.data.push(imp);
        self.blanket_key_to_id
            .entry(key.trait_ref)
            .or_default()
            .insert(key.sub_key, id);
        id
    }

    /// Bundle a set of module functions into a local functions,
    /// a cached dictionary value, and the overall interface hash.
    fn bundle_module_functions(
        functions: Vec<ModuleFunction>,
        fn_collector: &mut FunctionCollector,
    ) -> (Vec<LocalFunctionId>, Value, Type, u64) {
        let mut interface_hasher = DefaultHasher::new();
        let (methods, values, tys): (Vec<_>, Vec<_>, Vec<_>) = functions
            .into_iter()
            .map(|function| {
                let id = fn_collector.next_id();
                let value = Value::PendingFunction(function.code.clone());
                let fn_ty = Type::function_type(function.definition.ty_scheme.ty.clone());
                let local_fn = LocalFunction::new_anonymous(function);
                local_fn.interface_hash.hash(&mut interface_hasher);
                fn_collector.push(local_fn);
                (id, value, fn_ty)
            })
            .multiunzip();
        let hash = interface_hasher.finish();
        let dictionary_value = Value::tuple(values);
        let dictionary_ty = Type::tuple(tys);
        (methods, dictionary_value, dictionary_ty, hash)
    }

    pub fn concrete(&self) -> &ConcreteImpls {
        &self.concrete_key_to_id
    }

    pub fn blanket(&self) -> &BlanketImpls {
        &self.blanket_key_to_id
    }

    pub fn get_impl_by_key(&self, key: &TraitKey) -> Option<&TraitImpl> {
        use TraitKey::*;
        let id = match key {
            Concrete(key) => self.concrete_key_to_id.get(key),
            Blanket(key) => self
                .blanket_key_to_id
                .get(&key.trait_ref)
                .and_then(|m| m.get(&key.sub_key)),
        };
        id.map(|id| self.get_impl_by_local_id(*id))
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
                self.blanket_key_to_id.iter().find_map(|(trait_ref, map)| {
                    map.iter().find_map(|(sub_key, &val)| {
                        if val == id {
                            Some(TraitKey::Blanket(BlanketTraitImplKey::new(
                                trait_ref.clone(),
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

    pub(crate) fn fmt_with_filter(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
        filter: impl Fn(&TraitRef, LocalImplId) -> DisplayFilter,
    ) -> std::fmt::Result {
        for (key, id) in &self.concrete_key_to_id {
            let imp = self.get_impl_by_local_id(*id);
            let level = filter(&key.trait_ref, *id);
            if level == DisplayFilter::Hide {
                continue;
            }
            let subst = format_concrete_impl_header(key, &imp.output_tys, f, env)?;
            write!(f, " (#{id})")?;
            if level == DisplayFilter::MethodDefinitions {
                format_impl_fns(&key.trait_ref, subst, imp, false, f, env)?;
            } else if level == DisplayFilter::MethodCode {
                format_impl_fns(&key.trait_ref, subst, imp, true, f, env)?;
            }
            writeln!(f)?;
        }
        for (trait_ref, impls) in &self.blanket_key_to_id {
            for (sub_key, id) in impls {
                let level = filter(trait_ref, *id);
                if level == DisplayFilter::Hide {
                    continue;
                }
                let imp = self.get_impl_by_local_id(*id);
                let key = BlanketTraitImplKey::new(trait_ref.clone(), sub_key.clone());
                let subst = format_blanket_impl_header(&key, &imp.output_tys, f, env)?;
                write!(f, " (#{id})")?;
                if level == DisplayFilter::MethodDefinitions {
                    format_impl_fns(&key.trait_ref, subst, imp, false, f, env)?;
                } else if level == DisplayFilter::MethodCode {
                    format_impl_fns(&key.trait_ref, subst, imp, true, f, env)?;
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

    pub fn print_impls_headers(&self, trait_ref: &TraitRef, module_env: ModuleEnv<'_>) {
        let filter = |tr: &TraitRef, _| {
            if tr.name == trait_ref.name {
                DisplayFilter::ImplSignature
            } else {
                DisplayFilter::Hide
            }
        };
        println!("{}", self.format_with(&(module_env, filter)));
    }

    pub fn impl_header_to_string_by_id(
        &self,
        id: LocalImplId,
        module_env: ModuleEnv<'_>,
    ) -> String {
        let filter = |_: &TraitRef, impl_id| {
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
    F: Fn(&TraitRef, LocalImplId) -> DisplayFilter,
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
    let subst = format_concrete_impl_header(key, &imp.output_tys, f, env)?;
    format_impl_fns(&key.trait_ref, subst, imp, false, f, env)
}

pub fn format_blanket_impl(
    key: &BlanketTraitImplKey,
    imp: &TraitImpl,
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> std::fmt::Result {
    let subst = format_blanket_impl_header(key, &imp.output_tys, f, env)?;
    format_impl_fns(&key.trait_ref, subst, imp, false, f, env)
}

pub fn format_impl_header_by_key(
    f: &mut fmt::Formatter,
    key: &TraitKey,
    imp: &TraitImpl,
    env: &ModuleEnv,
) -> Result<TypeSubstitution, std::fmt::Error> {
    use TraitKey::*;
    match key {
        Concrete(key) => format_concrete_impl_header(key, &imp.output_tys, f, env),
        Blanket(key) => format_blanket_impl_header(key, &imp.output_tys, f, env),
    }
}

pub fn format_blanket_impl_header(
    key: &BlanketTraitImplKey,
    output_tys: &[Type],
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> Result<TypeSubstitution, std::fmt::Error> {
    let subst = format_concrete_impl_header_expanded(
        &key.trait_ref,
        &key.sub_key.input_tys,
        output_tys,
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
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> Result<TypeSubstitution, std::fmt::Error> {
    format_concrete_impl_header_expanded(&key.trait_ref, &key.input_tys, output_tys, f, env)
}

fn format_concrete_impl_header_expanded(
    trait_ref: &TraitRef,
    input_tys: &[Type],
    output_tys: &[Type],
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
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

fn format_impl_fns(
    trait_ref: &TraitRef,
    subst: TypeSubstitution,
    imp: &TraitImpl,
    show_code: bool,
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> std::fmt::Result {
    let subst = (subst, HashMap::new());
    writeln!(f, " {{")?;
    let impl_functions = imp.methods.iter().map(|id| {
        let function = &env.current.functions[id.as_index()];
        (&function.function, *id)
    });
    for ((name, _), (function, id)) in trait_ref.functions.iter().zip(impl_functions) {
        let def = &function.definition;
        let code = if show_code {
            Some(&function.code)
        } else {
            None
        };
        format_impl_fn(*name, def, id, &subst, code, f, env)?;
    }
    writeln!(f, "}}")
}

fn format_impl_fn(
    name: Ustr,
    def: &FunctionDefinition,
    id: LocalFunctionId,
    subst: &InstSubstitution,
    fn_code: Option<&FunctionRc>,
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> std::fmt::Result {
    let ty = def.ty_scheme.ty.instantiate(subst);
    write!(f, "    fn {name}")?;
    fmt_fn_type_with_arg_names(&ty, &def.arg_names, f, env)?;
    if def.ty_scheme.constraints.is_empty() {
        writeln!(f, " (#{id})")?;
    } else {
        write!(f, " where ")?;
        format_constraints_consolidated(&def.ty_scheme.constraints, f, env)?;
        writeln!(f, " (#{id})")?;
    }
    if let Some(fn_code) = fn_code {
        fn_code.borrow().format_ind(f, env, 2, 1)?;
    }
    Ok(())
}

pub fn format_impl_header_by_import_slot_id(
    f: &mut fmt::Formatter,
    id: ImportImplSlotId,
    env: &ModuleEnv<'_>,
) -> fmt::Result {
    let slot = &env.current.import_impl_slots[id.as_index()];
    format_impl_header_by_import_slot(f, slot, env)
}

pub fn format_impl_header_by_import_slot(
    f: &mut fmt::Formatter,
    slot: &ImportImplSlot,
    env: &ModuleEnv<'_>,
) -> fmt::Result {
    let key = &slot.key;
    let module_name = slot.module_name;
    let impls = &env
        .others
        .modules
        .get(&module_name)
        .expect("imported module not found")
        .impls;
    let imp = impls
        .get_impl_by_key(key)
        .expect("imported trait impl not found");
    format_impl_header_by_key(f, key, imp, env)?;
    Ok(())
}
