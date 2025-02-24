// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use itertools::Itertools;
use ustr::{ustr, Ustr};

use crate::{
    function::FunctionDefinition,
    module::{Module, ModuleEnv, ModuleFunction},
    mutability::MutType,
    r#trait::TraitRef,
    r#type::{FnArgType, Type},
    Location,
};

/// A trait function description as result of a lookup in the typing environment.
/// The tuple contains the trait reference, the index of the function in the trait, and the function definition.
pub type TraitFunctionDescription<'a> = (TraitRef, usize, &'a FunctionDefinition);

/// A local variable within a typing environment.
#[derive(Clone, Debug)]
pub struct Local {
    pub name: Ustr,
    pub mutable: MutType,
    pub ty: Type,
    pub span: Location,
}

impl Local {
    pub fn new(name: Ustr, mutable: MutType, ty: Type, span: Location) -> Self {
        Self {
            name,
            mutable,
            ty,
            span,
        }
    }

    pub fn new_var(name: Ustr, ty: Type, span: Location) -> Self {
        Self {
            name,
            mutable: MutType::mutable(),
            ty,
            span,
        }
    }

    pub fn new_let(name: Ustr, ty: Type, span: Location) -> Self {
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

    /// Get a function from the current module, or other ones, return the name of the module if other.
    pub fn get_function(&'m self, name: &'m str) -> Option<(Option<Ustr>, &'m ModuleFunction)> {
        self.get_module_member(name, &|name, module| module.functions.get(&ustr(name)))
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
        self.module_env
            .current
            .get_member(path, self.module_env.others, getter)
            .or_else(|| {
                let path = path.split("::").next_tuple();
                if let Some(path) = path {
                    let (module_name, function_name) = path;
                    let module_name = ustr(module_name);
                    self.module_env.others.get(&module_name).and_then(|module| {
                        module.get_member(function_name, self.module_env.others, getter)
                    })
                } else {
                    None
                }
            })
    }
}
