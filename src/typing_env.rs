// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use ustr::{Ustr, ustr};

use crate::{
    Location, ast,
    error::InternalCompilationError,
    function::FunctionDefinition,
    module::{
        self, FunctionId, ImportFunctionSlot, ImportFunctionSlotId, ImportFunctionTarget,
        LocalFunctionId, Module, ModuleEnv, ModuleFunction, ModuleId,
    },
    mutability::MutType,
    std::STD_MODULE_ID,
    r#trait::TraitRef,
    r#type::{FnArgType, Type},
};

use derive_new::new;

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

pub type GetFunctionData<'a> = (&'a FunctionDefinition, FunctionId, Option<ModuleId>);

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
    /// Newly-created module functions from lambdas
    pub(crate) lambda_functions: &'m mut Vec<ModuleFunction>,
    /// The next index for a new module function created from a lambda
    pub(crate) base_local_function_index: u32,
}

impl<'m> TypingEnv<'m> {
    pub fn current_module_id(&self) -> ModuleId {
        self.module_env.current.module_id()
    }

    pub fn get_locals_and_drop(self) -> Vec<Local> {
        self.locals
    }

    pub fn collect_lambda_module_function(&mut self, function: ModuleFunction) -> LocalFunctionId {
        let base_index = self.base_local_function_index;
        let index = base_index + self.lambda_functions.len() as u32;
        self.lambda_functions.push(function);
        LocalFunctionId(index)
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

    fn import_function(
        &mut self,
        module_id: ModuleId,
        function_name: Ustr,
    ) -> ImportFunctionSlotId {
        self.module_env.current.iter_import_fn_slots()
            .position(|slot| slot.module == module_id &&
                matches!(slot.target, ImportFunctionTarget::NamedFunction(name) if name == function_name)
            )
            .map(|index| ImportFunctionSlotId(index as u32))
            .unwrap_or_else(|| {
                let slot_index = (self.module_env.current.import_fn_slot_count() + self.new_import_slots.len()) as u32;
                self.new_import_slots.push(ImportFunctionSlot {
                    module: module_id,
                    target: ImportFunctionTarget::NamedFunction(function_name),
                });
                ImportFunctionSlotId(slot_index)
            })
    }

    pub fn get_function(
        &mut self,
        path: &ast::Path,
    ) -> Result<Option<GetFunctionData<'_>>, InternalCompilationError> {
        if path.is_empty() {
            return Ok(None);
        }
        // Resolve the symbol in the module environment, to (Option<module path>, function name)
        let segments = &path.segments;
        let fn_name = segments.last().unwrap().0;
        let is_local = segments.len() == 1
            || (segments.len() == 2
                && self.current_module_id() == STD_MODULE_ID
                && segments[0].0 == "std");
        let key = if is_local {
            let get_fn = |name: &str, m: &Module| {
                let name = ustr(name);
                if m.get_local_function_id(name).is_some() {
                    Some(name)
                } else {
                    None
                }
            };
            self.module_env
                .current
                .get_member(&fn_name, self.module_env.modules, &get_fn)?
        } else {
            let module_path = module::Path::from_ast_segments(&segments[..segments.len() - 1]);
            self.module_env
                .modules
                .get_by_name(&module_path)
                .and_then(|(module_id, m)| {
                    if m.get_local_function_id(fn_name).is_some() {
                        Some((Some(module_id), fn_name))
                    } else {
                        None
                    }
                })
        };

        // Create the ProgramFunction from the resolved key
        let (module_id_opt, function_name) = match key {
            Some(k) => k,
            None => return Ok(None),
        };
        Ok(if let Some(module_id) = module_id_opt {
            let id = self.import_function(module_id, function_name);
            let definition = &self
                .module_env
                .modules
                .get(module_id)
                .unwrap()
                .get_function(function_name)
                .unwrap()
                .definition;
            Some((definition, FunctionId::Import(id), Some(module_id)))
        } else {
            let id = self
                .module_env
                .current
                .get_local_function_id(function_name)
                .unwrap();
            let function = self.module_env.current.get_function_by_id(id).unwrap();
            Some((&function.definition, FunctionId::Local(id), None))
        })
    }
}
