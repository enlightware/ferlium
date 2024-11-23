use std::{collections::HashMap, fmt, rc::Rc};

use crate::Location;
use ustr::Ustr;

use crate::{
    containers::{find_key_for_value_property, B},
    format::FormatWith,
    function::FunctionRc,
    r#type::{BareNativeType, FnType, Type, TypeAliases},
    type_scheme::TypeScheme,
};

/// If the module function is from code, this struct contains the spans of the function.
#[derive(Debug, Clone)]
pub struct ModuleFunctionSpans {
    pub name: Location,
    pub args: Vec<Location>,
    pub args_span: Location,
    pub span: Location,
}

/// A function inside a module.
#[derive(Debug, Clone)]
pub struct ModuleFunction {
    pub code: FunctionRc,
    pub ty_scheme: TypeScheme<FnType>,
    pub spans: Option<ModuleFunctionSpans>,
    pub arg_names: Vec<Ustr>,
    pub doc: Option<String>,
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

/// A module is a collection of functions, type aliases and use statements.
#[derive(Clone, Debug, Default)]
pub struct Module {
    pub functions: FunctionsMap,
    pub types: TypeAliases,
    pub uses: Uses,
    pub source: Option<String>,
}

impl Module {
    /// Extend this module with other, consuming it
    pub fn extend(&mut self, other: Self) {
        self.functions.extend(other.functions);
        self.types.extend(other.types);
        self.uses.extend(other.uses);
    }

    pub fn is_empty(&self) -> bool {
        self.functions.is_empty() && self.types.is_empty() && self.uses.is_empty()
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

    /// Return whether this module uses sym_name from mod_name
    pub fn uses(&self, mod_name: Ustr, sym_name: Ustr) -> bool {
        self.uses.iter().any(|u| match u {
            Use::All(module) => *module == mod_name,
            Use::Some(some) => some.module == mod_name && some.symbols.contains(&sym_name),
        })
    }

    /// Look-up a function by name in this module or in any of the modules this module uses.
    pub fn get_function<'a>(
        &'a self,
        name: &str,
        others: &'a Modules,
    ) -> Option<&'a ModuleFunction> {
        let name = Ustr::from(name);
        self.functions.get(&name).or_else(|| {
            self.uses.iter().find_map(|use_module| match use_module {
                Use::All(module) => others.get(module)?.functions.get(&name),
                Use::Some(use_some) => {
                    if use_some.symbols.contains(&name) {
                        others.get(&use_some.module)?.functions.get(&name)
                    } else {
                        None
                    }
                }
            })
        })
    }

    /// Look-up a function by name in this module only.
    pub fn get_local_function<'a>(&'a self, name: &str) -> Option<&'a ModuleFunction> {
        self.functions.get(&Ustr::from(name))
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
                // function.ty_scheme.format_quantifiers(f)?; write!(f, ". ")?;
                if let Some(doc) = &function.doc {
                    writeln!(f, "/// {}", doc)?;
                }
                if function.ty_scheme.is_just_type_and_effects() {
                    writeln!(f, "fn {name} {}", function.ty_scheme.ty.format_with(&env))?;
                } else {
                    writeln!(
                        f,
                        "fn {name} {} {}",
                        function.ty_scheme.ty.format_with(&env),
                        function.ty_scheme.display_constraints_rust_style(&env),
                    )?;
                }
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
}

/// Format a type with a module environment
pub trait FmtWithModuleEnv {
    fn format_with<'a>(&'a self, env: &'a ModuleEnv<'a>) -> FormatWithModuleEnv<'_, Self> {
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
