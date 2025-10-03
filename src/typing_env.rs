use std::cell::RefCell;

use derive_new::new;
use itertools::Itertools;
// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use ustr::{ustr, Ustr};

use crate::{
    function::FunctionDefinition,
    module::FunctionId,
    module::ModuleEnv,
    module::{ImportFunctionSlot, ImportFunctionSlotId, ImportFunctionTarget, Module},
    mutability::MutType,
    r#trait::TraitRef,
    r#type::{FnArgType, Type},
    Location,
};

/// A trait function description as result of a lookup in the typing environment.
/// The tuple contains the trait reference, the index of the function in the trait, and the function definition.
pub type TraitFunctionDescription<'a> = (TraitRef, usize, &'a FunctionDefinition);

/// A local variable within a typing environment.
#[derive(Clone, Debug, new)]
pub struct Local {
    pub name: Ustr,
    pub mutable: MutType,
    pub ty: Type,
    pub span: Location,
}

impl Local {
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
#[derive(new)]
pub struct TypingEnv<'m> {
    /// The local variables existing in this environment.
    pub(crate) locals: Vec<Local>,
    /// The extra import slots that can be filled during type checking.
    pub(crate) new_import_slots: &'m mut Vec<ImportFunctionSlot>,
    /// The program and the module we are currently compiling.
    pub(crate) module_env: ModuleEnv<'m>,
    /// The expected return type of the enclosing function (for type-checking `return` statements).
    pub(crate) expected_return_ty: Option<(Type, Location)>,
}

impl<'m> TypingEnv<'m> {
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

    fn import_function(&mut self, module_name: Ustr, function_name: Ustr) -> ImportFunctionSlotId {
        let existing_slots = &self.module_env.current.import_fn_slots;
        existing_slots
            .iter()
            .position(|slot| slot.module_name == module_name &&
                matches!(slot.target, ImportFunctionTarget::NamedFunction(name) if name == function_name)
            )
            .map(|index| ImportFunctionSlotId(index as u32))
            .unwrap_or_else(|| {
                let slot_index = (existing_slots.len() + self.new_import_slots.len()) as u32;
                self.new_import_slots.push(ImportFunctionSlot {
                    module_name,
                    target: ImportFunctionTarget::NamedFunction(function_name),
                    resolved: RefCell::new(None),
                });
                ImportFunctionSlotId(slot_index)
            })
    }

    pub fn get_function(
        &mut self,
        path: &str,
    ) -> Option<(&FunctionDefinition, FunctionId, Option<Ustr>)> {
        if path.is_empty() {
            return None;
        }
        // Resolve the symbol in the module environment, to (Option<module name>, function name)
        let split_path = path.split("::").collect_vec();
        let fn_name = split_path.last().unwrap();
        let is_local = split_path.len() == 1
            || (split_path.len() == 2 && self.module_env.within_std && split_path[0] == "std");
        let key = if is_local {
            let get_fn = |name: &str, m: &Module| {
                let name = ustr(name);
                if m.function_name_to_id.contains_key(&name) {
                    Some(name)
                } else {
                    None
                }
            };
            self.module_env
                .current
                .get_member(fn_name, self.module_env.others, &get_fn)
        } else if split_path.len() == 2 {
            let module_name = ustr(split_path[0]);
            self.module_env
                .others
                .get(&module_name)
                .and_then(|m| {
                    if m.function_name_to_id.contains_key(&ustr(fn_name)) {
                        Some(ustr(fn_name))
                    } else {
                        None
                    }
                })
                .map(|function_name| (Some(module_name), function_name))
        } else {
            None
        };

        // Create the ProgramFunction from the resolved key
        let (module_name_opt, function_name) = key?;
        Some(if let Some(module_name) = module_name_opt {
            let id = self.import_function(module_name, function_name);
            let definition = &self
                .module_env
                .others
                .get(&module_name)?
                .get_own_function(function_name)?
                .definition;
            (definition, FunctionId::Import(id), Some(module_name))
        } else {
            let id = *self
                .module_env
                .current
                .function_name_to_id
                .get(&function_name)
                .unwrap();
            let index = id.0 as usize;
            let local_fn = &self.module_env.current.functions[index];
            (&local_fn.function.definition, FunctionId::Local(id), None)
        })
    }

    pub fn other_module_name(&self, function: FunctionId) -> Option<Ustr> {
        match function {
            FunctionId::Local(_) => None,
            FunctionId::Import(id) => self
                .module_env
                .current
                .import_fn_slots
                .get(id.0 as usize)
                .map(|slot| slot.module_name),
        }
    }
}
