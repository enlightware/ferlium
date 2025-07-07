// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    cell::{Ref, RefMut},
    collections::HashMap,
    fmt,
    rc::Rc,
};

use crate::{
    function::FunctionDefinition,
    ir::Node,
    r#trait::TraitRef,
    trait_solver::{TraitImpls, Traits},
    typing_env::TraitFunctionDescription,
    Location,
};
use itertools::Itertools;
use ustr::{ustr, Ustr};

use crate::{
    containers::{find_key_for_value_property, B},
    format::FormatWith,
    function::FunctionRc,
    r#type::{BareNativeType, Type, TypeAliases},
};

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
impl ModuleFunction {
    pub fn get_node(&self) -> Option<Ref<Node>> {
        let code = self.code.borrow();
        Ref::filter_map(code, |code| code.as_script().map(|s| &s.code)).ok()
    }
    pub fn get_node_mut(&mut self) -> Option<RefMut<Node>> {
        let code = self.code.borrow_mut();
        RefMut::filter_map(code, |code| code.as_script_mut().map(|s| &mut s.code)).ok()
    }
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
    pub impls: TraitImpls,
    pub functions: FunctionsMap,
    pub types: TypeAliases,
    pub uses: Uses,
    pub source: Option<String>,
}

impl Module {
    /// Extend this module with other, consuming it.
    pub fn extend(&mut self, other: Self) {
        self.traits.extend(other.traits);
        self.impls.concrete.extend(other.impls.concrete);
        self.impls.blanket.extend(other.impls.blanket);
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

    /// Look-up a function by name only in this module and return its script node, if it is a script function.
    pub fn get_own_function_node(&mut self, name: Ustr) -> Option<Ref<Node>> {
        self.functions.get(&name)?.get_node()
    }

    /// Look-up a function by name only in this module and return its mutable script node, if it is a script function.
    pub fn get_own_function_node_mut(&mut self, name: Ustr) -> Option<RefMut<Node>> {
        self.functions.get_mut(&name)?.get_node_mut()
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
        if !self.uses.is_empty() {
            writeln!(f, "Uses:")?;
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
        }
        if !self.types.is_empty() {
            writeln!(f, "Types:")?;
            for (name, ty) in self.types.iter() {
                writeln!(f, "  {}: {}", name, ty.format_with(&env))?;
            }
            writeln!(f, "\n")?;
        }
        if !self.traits.is_empty() {
            writeln!(f, "Traits:\n")?;
            for trait_ref in self.traits.iter() {
                writeln!(f, "{}", trait_ref.format_with(&env))?;
            }
            writeln!(f)?;
        }
        if !self.impls.is_empty() {
            writeln!(f, "Trait implementations:\n")?;
            writeln!(f, "{}", self.impls.format_with(&env))?;
        }
        if !self.functions.is_empty() {
            writeln!(f, "Functions:\n")?;
            for (name, function) in self.functions.iter() {
                function
                    .definition
                    .fmt_with_name_and_module_env(f, name, "", &env)?;
                function.code.borrow().format_ind(f, &env, 1, 1)?;
                writeln!(f)?;
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

    /// Get a function from the current module, or other ones, return the name of the module if other.
    pub fn get_function(&'m self, name: &'m str) -> Option<(Option<Ustr>, &'m ModuleFunction)> {
        self.get_module_member(name, &|name, module| module.functions.get(&ustr(name)))
    }

    /// Get the trait reference associated to a trait name.
    pub fn get_trait_ref(&'m self, path: &'m str) -> Option<TraitRef> {
        self.get_module_member(path, &|name, module| {
            module.traits.iter().find_map(|trait_ref| {
                if trait_ref.name == name {
                    Some(trait_ref.clone())
                } else {
                    None
                }
            })
        })
        .map(|(_, t)| t)
    }

    /// Get a trait function from the current module, or other ones, return the name of the module if other.
    pub fn get_trait_function(
        &'m self,
        path: &'m str,
    ) -> Option<(Option<Ustr>, TraitFunctionDescription<'m>)> {
        self.get_module_member(path, &|name, module| {
            module.traits.iter().find_map(|trait_ref| {
                trait_ref
                    .functions
                    .iter()
                    .enumerate()
                    .find_map(|(index, function)| {
                        if function.0 == name {
                            Some((trait_ref.clone(), index, &function.1))
                        } else {
                            None
                        }
                    })
            })
        })
    }

    /// Get a member of a module, by first looking in the current module, and then in others, considering the path.
    fn get_module_member<T>(
        &'m self,
        path: &'m str,
        getter: &impl Fn(/*name*/ &'m str, /*current*/ &'m Module) -> Option<T>,
    ) -> Option<(Option<Ustr>, T)> {
        self.current
            .get_member(path, self.others, getter)
            .or_else(|| {
                let path = path.split("::").next_tuple();
                if let Some(path) = path {
                    let (module_name, function_name) = path;
                    let module_name = ustr(module_name);
                    self.others
                        .get(&module_name)
                        .and_then(|module| module.get_member(function_name, self.others, getter))
                } else {
                    None
                }
            })
    }

    /// Collect all trait implementations from this module and the others.
    pub fn collect_trait_impls(&self) -> TraitImpls {
        let mut combined = self.current.impls.clone();
        for module in self.others.values() {
            fn clone_entry<K: Clone, V: Clone>((k, v): (&K, &V)) -> (K, V) {
                (k.clone(), v.clone())
            }
            combined
                .concrete
                .extend(module.impls.concrete.iter().map(clone_entry));
            combined
                .blanket
                .extend(module.impls.blanket.iter().map(clone_entry));
        }
        combined
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
