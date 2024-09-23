use itertools::Itertools;
use lrpar::Span;
use ustr::Ustr;

use crate::{
    module::{ModuleEnv, ModuleFunction},
    mutability::MutType,
    r#type::{FnArgType, Type},
};

/// A local variable within a typing environment.
#[derive(Clone, Debug)]
pub struct Local {
    pub name: Ustr,
    pub mutable: MutType,
    pub ty: Type,
    pub span: Span,
}

impl Local {
    pub fn new(name: Ustr, mutable: MutType, ty: Type, span: Span) -> Self {
        Self {
            name,
            mutable,
            ty,
            span,
        }
    }

    pub fn new_var(name: Ustr, ty: Type, span: Span) -> Self {
        Self {
            name,
            mutable: MutType::mutable(),
            ty,
            span,
        }
    }

    pub fn new_let(name: Ustr, ty: Type, span: Span) -> Self {
        Self {
            name,
            mutable: MutType::constant(),
            ty,
            span,
        }
    }

    pub fn as_fn_arg_type(&self) -> FnArgType {
        FnArgType::new(self.ty, self.mutable)
    }
}

/// A typing environment, mapping local variable names to types.
pub struct TypingEnv<'m> {
    pub(crate) locals: Vec<Local>,
    pub(crate) module_env: ModuleEnv<'m>,
}

impl<'m> TypingEnv<'m> {
    pub fn new(locals: Vec<Local>, module_env: ModuleEnv<'m>) -> Self {
        Self { locals, module_env }
    }

    pub fn get_locals_and_drop(self) -> Vec<Local> {
        self.locals
    }

    pub fn has_variable_name(&self, name: Ustr) -> bool {
        self.locals.iter().any(|local| local.name == name)
    }

    pub fn get_variable_index_and_type_scheme(&self, name: &str) -> Option<(usize, Type, MutType)> {
        self.locals
            .iter()
            .rev()
            .position(|local| local.name == name)
            .map(|rev_index| self.locals.len() - 1 - rev_index)
            .map(|index| (index, self.locals[index].ty, self.locals[index].mutable))
    }

    pub fn get_function(&'m self, name: Ustr) -> Option<&'m ModuleFunction> {
        self.module_env
            .current
            .get_function(&name, self.module_env.others)
            .or_else(|| {
                let path = name.as_str().split("::").next_tuple();
                if let Some(path) = path {
                    let (module_name, function_name) = path;
                    self.module_env
                        .others
                        .get(&Ustr::from(module_name))
                        .and_then(|module| {
                            module.get_function(function_name, self.module_env.others)
                        })
                } else {
                    None
                }
            })
    }
}
