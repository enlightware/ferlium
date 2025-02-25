// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{collections::HashMap, fmt, ops::Deref, rc::Rc};

use crate::{
    containers::SVec2,
    function::{Function, FunctionDefinition},
    r#trait::{TraitImpl, TraitRef},
    value::Value,
    Location,
};
use ustr::{ustr, Ustr};

use crate::{
    containers::{find_key_for_value_property, B},
    format::FormatWith,
    function::FunctionRc,
    r#type::{BareNativeType, Type, TypeAliases},
};

pub type Traits = Vec<TraitRef>;

/// A pair of a trait reference and a list of input types forming a key for trait implementations.
pub type TraitImplKey = (TraitRef, Vec<Type>);

/// All trait implementations in a module
#[derive(Clone, Debug, Default)]
pub struct Impls(HashMap<TraitImplKey, TraitImpl>);
impl Impls {
    /// Add a trait implementation to this module.
    pub fn add(
        &mut self,
        trait_ref: TraitRef,
        input_tys: impl Into<Vec<Type>>,
        output_tys: impl Into<Vec<Type>>,
        functions: impl Into<Vec<Function>>,
    ) {
        let input_tys = input_tys.into();
        let output_tys = output_tys.into();
        let functions: SVec2<_> = functions.into().into_iter().map(Value::function).collect();
        assert_eq!(
            trait_ref.input_type_count.get(),
            input_tys.len() as u32,
            "Mismatched input type count with implementing trait {}.",
            trait_ref.name,
        );
        assert_eq!(
            trait_ref.output_type_count,
            output_tys.len() as u32,
            "Mismatched output type count with implementing trait {}.",
            trait_ref.name,
        );
        assert_eq!(
            trait_ref.functions.len(),
            functions.len(),
            "Mismatched function count with implementing trait {}.",
            trait_ref.name,
        );
        let functions = Value::tuple(functions);
        let impl_ = TraitImpl {
            output_tys,
            functions,
        };
        let key = (trait_ref, input_tys);
        self.0.insert(key, impl_);
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}
impl FromIterator<(TraitImplKey, TraitImpl)> for Impls {
    fn from_iter<I: IntoIterator<Item = (TraitImplKey, TraitImpl)>>(iter: I) -> Self {
        Self(HashMap::from_iter(iter))
    }
}
impl Deref for Impls {
    type Target = HashMap<TraitImplKey, TraitImpl>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A module function argument span, with the span of the optional type ascription.
pub type ModuleFunctionArgSpan = (Location, Option<(Location, bool)>);

/// If the module function is from code, this struct contains the spans of the function.
#[derive(Debug, Clone)]
pub struct ModuleFunctionSpans {
    pub name: Location,
    pub args: Vec<ModuleFunctionArgSpan>,
    pub args_span: Location,
    pub ret_ty: Option<(Location, bool)>,
    pub span: Location,
}

/// A function inside a module.
#[derive(Debug, Clone)]
pub struct ModuleFunction {
    pub definition: FunctionDefinition,
    pub code: FunctionRc,
    pub spans: Option<ModuleFunctionSpans>,
}

pub type FunctionsMap = HashMap<Ustr, ModuleFunction>;

#[derive(Debug, Clone)]
pub struct UseSome {
    module: Ustr,
    symbols: Vec<Ustr>,
}

/// A use directive
#[derive(Debug, Clone)]
pub enum Use {
    /// Use all symbols from a module
    All(Ustr),
    /// Use only some symbols from a module
    Some(UseSome),
}

pub type Uses = Vec<Use>;

/// A module is a collection of traits, functions, type aliases and use statements.
#[derive(Clone, Debug, Default)]
pub struct Module {
    pub traits: Traits,
    pub impls: Impls,
    pub functions: FunctionsMap,
    pub types: TypeAliases,
    pub uses: Uses,
    pub source: Option<String>,
}

impl Module {
    /// Extend this module with other, consuming it.
    pub fn extend(&mut self, other: Self) {
        self.functions.extend(other.functions);
        self.types.extend(other.types);
        self.uses.extend(other.uses);
    }

    /// Return whether this module has no compiled content.
    pub fn is_empty(&self) -> bool {
        self.traits.is_empty()
            && self.impls.is_empty()
            && self.functions.is_empty()
            && self.types.is_empty()
            && self.uses.is_empty()
    }

    /// Return the trait implementations in this module.
    pub fn impls(&self) -> &Impls {
        &self.impls
    }

    /// Return the type for the source pos, if any.
    pub fn type_at(&self, pos: usize) -> Option<Type> {
        for (_, function) in self.functions.iter() {
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
            module.functions.get(&ustr(name))
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
        getter: &impl Fn(&'a str, &'a Module) -> Option<T>,
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

    /// Look-up a function by name in this module only.
    pub fn get_local_function<'a>(&'a self, name: &str) -> Option<&'a ModuleFunction> {
        self.functions.get(&ustr(name))
    }

    fn format_with_modules(&self, f: &mut fmt::Formatter, modules: &Modules) -> fmt::Result {
        let env = ModuleEnv::new(self, modules);
        if !self.types.is_empty() {
            writeln!(f, "Types:")?;
            for (name, ty) in self.types.iter() {
                writeln!(f, "  {}: {}", name, ty.format_with(&env))?;
            }
            writeln!(f)?;
        }
        if !self.functions.is_empty() {
            writeln!(f, "Functions:")?;
            for (name, function) in self.functions.iter() {
                function
                    .definition
                    .fmt_with_name_and_module_env(f, name, &env)?;
                function.code.borrow().format_ind(f, &env, 1)?;
            }
            writeln!(f)?;
        }
        if !self.uses.is_empty() {
            writeln!(f, "Uses:")?;
            for use_module in self.uses.iter() {
                match use_module {
                    Use::All(module) => writeln!(f, "  {}: *", module)?,
                    Use::Some(use_some) => {
                        write!(f, "  {}:", use_some.module)?;
                        for symbol in use_some.symbols.iter() {
                            write!(f, " {}", symbol)?;
                        }
                        writeln!(f)?;
                    }
                }
            }
        }
        Ok(())
    }
}

impl fmt::Display for FormatWith<'_, Module, Modules> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.format_with_modules(f, self.data)
    }
}

pub type Modules = HashMap<Ustr, Rc<Module>>;

#[derive(Clone, Copy)]
pub struct ModuleEnv<'m> {
    pub(crate) current: &'m Module,
    pub(crate) others: &'m Modules,
}

impl<'m> ModuleEnv<'m> {
    pub fn new(current: &'m Module, others: &'m Modules) -> Self {
        Self { current, others }
    }

    pub fn type_name(&self, ty: Type) -> Option<String> {
        self.current.types.get_name(ty).map_or_else(
            || {
                self.others.iter().find_map(|(mod_name, module)| {
                    module.types.get_name(ty).map(|ty_name| {
                        if self.current.uses(*mod_name, ty_name) {
                            ty_name.to_string()
                        } else {
                            format!("{mod_name}::{ty_name}")
                        }
                    })
                })
            },
            |name| Some(name.to_string()),
        )
    }

    pub fn bare_native_name(&self, native: &B<dyn BareNativeType>) -> Option<String> {
        self.current.types.get_bare_native_name(native).map_or_else(
            || {
                self.others.iter().find_map(|(mod_name, module)| {
                    module.types.get_bare_native_name(native).map(|ty_name| {
                        if self.current.uses(*mod_name, ty_name) {
                            ty_name.to_string()
                        } else {
                            format!("{mod_name}::{ty_name}")
                        }
                    })
                })
            },
            |name| Some(name.to_string()),
        )
    }

    pub fn function_name(&self, func: &FunctionRc) -> Option<String> {
        fn compare(module: &ModuleFunction, function: &FunctionRc) -> bool {
            Rc::ptr_eq(&module.code, function)
        }
        // FIXME: this needs update
        find_key_for_value_property(&self.current.functions, func, compare).map_or_else(
            || {
                self.others.iter().find_map(|(mod_name, module)| {
                    find_key_for_value_property(&module.functions, func, compare).map(|func_name| {
                        if self.current.uses(*mod_name, *func_name) {
                            func_name.to_string()
                        } else {
                            format!("{mod_name}::{func_name}")
                        }
                    })
                })
            },
            |name| Some(name.to_string()),
        )
    }

    pub fn collect_trait_impls(&self) -> Impls {
        self.current
            .impls
            .iter()
            .chain(
                self.others
                    .iter()
                    .flat_map(|(_, module)| module.impls.iter()),
            )
            .map(|(key, trait_impl)| ((key.0.clone(), key.1.clone()), trait_impl.clone()))
            .collect()
    }
}

/// Format a type with a module environment
pub trait FmtWithModuleEnv {
    fn format_with<'a>(&'a self, env: &'a ModuleEnv<'a>) -> FormatWithModuleEnv<'a, Self> {
        FormatWithModuleEnv {
            value: self,
            data: env,
        }
    }

    fn fmt_with_module_env(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result;
}

pub type FormatWithModuleEnv<'a, T> = FormatWith<'a, T, ModuleEnv<'a>>;

impl<T: FmtWithModuleEnv> fmt::Display for FormatWithModuleEnv<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value.fmt_with_module_env(f, self.data)
    }
}
