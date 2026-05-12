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
    FxHashSet, Location,
    ast::{self, DExprArena},
    compiler::error::{InternalCompilationError, UnsafeFeature},
    hir::NodeArena,
    hir::function::{ArgPassing, FunctionDefinition},
    module::{
        self, FunctionId, ImportFunctionSlot, ImportFunctionSlotId, ImportFunctionTarget,
        LocalDecl, LocalDeclId, LocalFunctionId, Module, ModuleEnv, ModuleFunction, ModuleId,
        TypeDefLookupResult, id::Id,
    },
    std::STD_MODULE_ID,
    types::r#trait::{TraitMethodIndex, TraitRef},
    types::r#type::{Type, TypeSubstitution, TypeVar},
};

use derive_new::new;

/// A trait method description as result of a lookup in the typing environment.
/// The tuple contains the trait reference, the method index in the trait, and the method definition.
pub type TraitMethodDescription<'a> = (TraitRef, TraitMethodIndex, &'a FunctionDefinition);

pub type GetFunctionData<'a> = (
    &'a FunctionDefinition,
    FunctionId,
    Option<ModuleId>,
    Option<&'static [ArgPassing]>,
);

#[derive(Debug, new)]
pub struct LoopFrame {
    pub(crate) result_ty: TypeVar,
    pub(crate) saw_break: bool,
    // pub(crate) label: Option<Ustr>,
}

/// A typing environment, mapping local variable names to types.
#[derive(new)]
#[allow(clippy::too_many_arguments)]
pub struct TypingEnv<'m> {
    /// All local variables in the current function, including those from outer scopes.
    /// The index of a local variable in this vector is its LocalDeclId.
    pub(crate) all_locals: &'m mut Vec<LocalDecl>,
    /// The local variables existing in this environment.
    pub(crate) cur_locals: Vec<LocalDeclId>,
    /// The extra import slots that can be filled during type checking.
    pub(crate) new_import_slots: &'m mut Vec<ImportFunctionSlot>,
    /// The type dependencies that can be filled during type checking.
    pub(crate) new_type_deps: &'m mut FxHashSet<ModuleId>,
    /// The program and the module we are currently compiling.
    pub(crate) module_env: ModuleEnv<'m>,
    /// The expected return type of the enclosing function (for type-checking `return` statements).
    pub(crate) expected_return_ty: Option<(Type, Location)>,
    /// The substitution to use for explicit generic type parameters in current annotations.
    pub(crate) annotation_ty_subst: Option<&'m TypeSubstitution>,
    /// The active loop frames, used for type-checking `soft_break`.
    pub(crate) loop_frames: Vec<LoopFrame>,
    /// Newly-created module functions from lambdas
    pub(crate) lambda_functions: &'m mut Vec<ModuleFunction>,
    /// The next index for a new module function created from a lambda
    pub(crate) base_local_function_index: u32,
    /// The desugared expression arena, used to look up child expression nodes by ID.
    pub(crate) ast_arena: &'m DExprArena,
    /// The HIR node arena, used to allocate HIR nodes during type inference.
    pub(crate) ir_arena: &'m mut NodeArena,
}

impl<'m> TypingEnv<'m> {
    pub fn current_module_id(&self) -> ModuleId {
        self.module_env.current.module_id()
    }

    pub fn get_all_locals_and_drop(self) -> Vec<LocalDecl> {
        std::mem::take(self.all_locals)
    }

    pub fn push_local(&mut self, local: LocalDecl) -> LocalDeclId {
        let id = LocalDecl::push_with_next_slot(self.all_locals, local);
        self.cur_locals.push(id);
        id
    }

    pub fn collect_lambda_module_function(&mut self, function: ModuleFunction) -> LocalFunctionId {
        let base_index = self.base_local_function_index;
        let index = base_index + self.lambda_functions.len() as u32;
        self.lambda_functions.push(function);
        LocalFunctionId(index)
    }

    pub fn has_variable_name(&self, name: Ustr) -> bool {
        self.cur_locals
            .iter()
            .any(|local| self.all_locals[local.as_index()].name.0 == name)
    }

    pub fn get_variable_id(&self, name: &str) -> Option<LocalDeclId> {
        self.cur_locals
            .iter()
            .rev()
            .position(|local| self.all_locals[local.as_index()].name.0 == name)
            .map(|rev_index| self.cur_locals.len() - 1 - rev_index)
            .map(|index| self.cur_locals[index])
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
                .and_then(|(module_id, entry)| {
                    if let Some(module) = entry.module()
                        && module.get_local_function_id(fn_name).is_some()
                    {
                        Some((Some(module_id), fn_name))
                    } else {
                        None
                    }
                })
        };

        // Create the GetFunctionData from the resolved key
        let (module_id_opt, function_name) = match key {
            Some(k) => k,
            None => return Ok(None),
        };
        if self
            .module_env
            .is_unsafe_item_unavailable_in_current_context(module_id_opt, function_name)
        {
            return Err(
                InternalCompilationError::new_unsafe_feature_use_not_allowed(
                    UnsafeFeature::Function(function_name),
                    path.span().unwrap_or_else(Location::new_synthesized),
                ),
            );
        }

        Ok(if let Some(module_id) = module_id_opt {
            let id = self.import_function(module_id, function_name);
            let source_module = self
                .module_env
                .modules
                .get(module_id)
                .unwrap()
                .module
                .as_ref()
                .unwrap();
            let function = source_module.get_function(function_name).unwrap();
            Some((
                &function.definition,
                FunctionId::Import(id),
                Some(module_id),
                function.code.argument_passing(),
            ))
        } else {
            let id = self
                .module_env
                .current
                .get_local_function_id(function_name)
                .unwrap();
            let function = self.module_env.current.get_function_by_id(id).unwrap();
            Some((
                &function.definition,
                FunctionId::Local(id),
                None,
                function.code.argument_passing(),
            ))
        })
    }

    pub fn get_type_def(
        &mut self,
        path: &ast::Path,
    ) -> Result<Option<TypeDefLookupResult>, InternalCompilationError> {
        let result = self.module_env.type_def_for_construction(path)?;
        Ok(result.map(|td| {
            if let Some(module_id) = td.0 {
                self.new_type_deps.insert(module_id);
            }
            td.1
        }))
    }
}
