use std::collections::HashMap;

use ustr::Ustr;

use crate::{
    containers::iterable_to_string,
    function::{FunctionDescriptionRc, FunctionsMap},
    r#type::TypeAliases,
};

#[derive(Debug, Clone)]
pub(crate) struct UseSome {
    module: Ustr,
    symbols: Vec<Ustr>,
}

/// A use directive
#[derive(Debug, Clone)]
pub(crate) enum Use {
    /// Use all symbols from a module
    All(Ustr),
    /// Use only some symbols from a module
    Some(UseSome),
}

pub(crate) type Uses = Vec<Use>;

/// A module is a collection of functions, type aliases and use statements.
#[derive(Clone, Debug, Default)]
pub struct Module {
    pub(crate) functions: FunctionsMap,
    pub(crate) types: TypeAliases,
    pub(crate) uses: Uses,
}

impl Module {
    pub fn extend(&mut self, other: Self) {
        self.functions.extend(other.functions);
        self.types.extend(other.types);
        self.uses.extend(other.uses);
    }

    pub fn is_empty(&self) -> bool {
        self.functions.is_empty() && self.types.is_empty() && self.uses.is_empty()
    }

    /// Look-up a function by name in this module or in any of the modules this module uses.
    pub fn get_function(&self, name: Ustr, others: &Modules) -> Option<FunctionDescriptionRc> {
        self.functions.get(&name).cloned().or_else(|| {
            self.uses.iter().find_map(|use_module| match use_module {
                Use::All(module) => others.get(module)?.functions.get(&name).cloned(),
                Use::Some(use_some) => {
                    if use_some.symbols.contains(&name) {
                        others.get(&use_some.module)?.functions.get(&name).cloned()
                    } else {
                        None
                    }
                }
            })
        })
    }
}

impl std::fmt::Display for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.types.is_empty() {
            writeln!(f, "Types:")?;
            for (name, ty) in self.types.iter() {
                writeln!(f, "  {}: {}", name, ty)?;
            }
        }
        if !self.functions.is_empty() {
            writeln!(f, "Functions:")?;
            for (name, f_descr) in self.functions.iter() {
                let f_descr = f_descr.borrow();
                writeln!(
                    f,
                    "  fn {name}({}) -> {}",
                    iterable_to_string(f_descr.ty.args.iter(), ", "),
                    f_descr.ty.ret
                )?;
                f_descr.code.format_ind(f, 2)?;
            }
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

pub type Modules = HashMap<Ustr, Module>;
