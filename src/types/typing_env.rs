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
    ast::{self, DExprArena, UstrSpan},
    compiler::{
        CompilationCapabilities,
        error::{InternalCompilationError, UnsafeFeature},
    },
    hir::function::{ArgConvention, CallableDefinition},
    hir::{LoopId, NodeArena, NodeId},
    module::{
        FunctionId, LocalDecl, LocalDeclId, LocalFunctionId, Module, ModuleEnv, ModuleId,
        ProjectionKey, SubscriptDefinition, SubscriptId, SubscriptMember, TraitId,
        TypeDefLookupResult, UModuleFunction, id::Id,
    },
    std::{STD_MODULE_ID, array::array_type as std_array_type},
    types::r#trait::TraitMethodIndex,
    types::{
        r#type::{CallResultConvention, Type, TypeVar},
        type_inference::substitution::InstSubst,
    },
};

use derive_new::new;

/// A trait method description as result of a lookup in the typing environment.
/// The tuple contains the trait id, the method index in the trait, and the method definition.
pub type TraitMethodDescription<'a> = (TraitId, TraitMethodIndex, &'a CallableDefinition);

pub type GetFunctionData<'a> = (
    &'a CallableDefinition,
    FunctionId,
    Option<ModuleId>,
    Option<Vec<ArgConvention>>,
);
pub type GetFunctionWithPathData<'a> = (ast::Path, GetFunctionData<'a>);
pub type GetSubscriptData<'a> = (&'a SubscriptDefinition, SubscriptId, Option<ModuleId>);
pub type GetSubscriptMemberData<'a> = (
    &'a SubscriptDefinition,
    &'a SubscriptMember,
    GetFunctionData<'a>,
);
pub type GetSubscriptMemberWithPathData<'a> = (ast::Path, GetSubscriptMemberData<'a>);

#[derive(Debug, Clone, Copy)]
pub(crate) struct SubscriptMemberTypingContext {
    pub(crate) name: Ustr,
    pub(crate) requires_mutable_place: bool,
    pub(crate) projection_key: Option<ProjectionKey>,
}

#[derive(Debug, new)]
pub struct LoopFrame {
    pub(crate) label: LoopId,
    pub(crate) source_label: Option<UstrSpan>,
    pub(crate) result_ty: TypeVar,
    pub(crate) local_scope_start: usize,
    pub(crate) saw_break: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct YieldTypingContext {
    pub(crate) expected_ty: Type,
    pub(crate) expected_span: Location,
    pub(crate) requires_mutable_place: bool,
    pub(crate) yielded_nodes: Vec<NodeId>,
}

impl YieldTypingContext {
    pub(crate) fn new(
        expected_ty: Type,
        expected_span: Location,
        requires_mutable_place: bool,
    ) -> Self {
        Self {
            expected_ty,
            expected_span,
            requires_mutable_place,
            yielded_nodes: Vec::new(),
        }
    }
}

fn select_subscript_member(
    subscript: &SubscriptDefinition,
    subscript_name: Ustr,
    mut_member: bool,
) -> &SubscriptMember {
    if mut_member {
        subscript.mut_member.as_ref()
    } else {
        subscript.ref_member.as_ref()
    }
    .unwrap_or_else(|| panic!("std subscript {subscript_name} member should be available"))
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
    /// Module dependencies discovered during type checking.
    pub(crate) new_deps: &'m mut FxHashSet<ModuleId>,
    /// The program and the module we are currently compiling.
    pub(crate) module_env: ModuleEnv<'m>,
    /// The expected return type of the enclosing function (for type-checking `return` statements).
    pub(crate) expected_return_ty: Option<(Type, Location)>,
    /// The return convention of the enclosing function.
    pub(crate) expected_return_convention: CallResultConvention,
    /// Source or synthetic name of the function currently being inferred.
    #[new(default)]
    pub(crate) function_name: Option<Ustr>,
    /// Source subscript member currently being inferred.
    #[new(default)]
    pub(crate) subscript_member: Option<SubscriptMemberTypingContext>,
    /// The substitution to use for explicit generic parameters in current annotations.
    pub(crate) annotation_subst: Option<&'m InstSubst>,
    /// The active loop frames, used for type-checking loop control flow.
    pub(crate) loop_frames: Vec<LoopFrame>,
    /// Whether compiler-inserted fuel checks should be emitted for loops.
    pub(crate) fuel_checks_enabled: bool,
    /// Newly-created module functions from lambdas
    pub(crate) lambda_functions: &'m mut Vec<UModuleFunction>,
    /// The next index for a new module function created from a lambda
    pub(crate) base_local_function_index: u32,
    /// The desugared expression arena, used to look up child expression nodes by ID.
    pub(crate) ast_arena: &'m DExprArena,
    /// The HIR node arena, used to allocate HIR nodes during type inference.
    pub(crate) ir_arena: &'m mut NodeArena,
    #[new(default)]
    pub(crate) compilation_capabilities: CompilationCapabilities,
    #[new(default)]
    pub(crate) yield_context: Option<YieldTypingContext>,
}

impl<'m> TypingEnv<'m> {
    pub fn current_module_id(&self) -> ModuleId {
        self.module_env.current.module_id()
    }

    pub fn array_type(&mut self, element_ty: Type) -> Type {
        if self.current_module_id() != STD_MODULE_ID {
            self.new_deps.insert(STD_MODULE_ID);
        }
        std_array_type(element_ty)
    }

    pub fn get_all_locals_and_drop(self) -> Vec<LocalDecl> {
        std::mem::take(self.all_locals)
    }

    pub fn push_local(&mut self, local: LocalDecl) -> LocalDeclId {
        let id = LocalDecl::push_with_next_slot(self.all_locals, local);
        self.cur_locals.push(id);
        id
    }

    pub fn collect_lambda_module_function(&mut self, function: UModuleFunction) -> LocalFunctionId {
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

    fn function_id(&mut self, module_id: ModuleId, function_id: LocalFunctionId) -> FunctionId {
        if module_id != self.current_module_id() {
            self.new_deps.insert(module_id);
        }
        FunctionId::new(module_id, function_id)
    }

    pub fn get_function(
        &mut self,
        path: &ast::Path,
    ) -> Result<Option<GetFunctionData<'_>>, InternalCompilationError> {
        if path.is_empty() {
            return Ok(None);
        }

        let (module_id_opt, function_name) =
            match self.module_env.function_name_with_module(path)? {
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
            let source_module = self
                .module_env
                .modules
                .get(module_id)
                .unwrap()
                .module
                .as_ref()
                .unwrap();
            let id = source_module.get_local_function_id(function_name).unwrap();
            let function = source_module.get_function_by_id(id).unwrap();
            Some((
                &function.definition,
                self.function_id(module_id, id),
                Some(module_id),
                function.code.runtime_argument_passing().map(<[_]>::to_vec),
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
                self.function_id(self.current_module_id(), id),
                None,
                function.code.runtime_argument_passing().map(<[_]>::to_vec),
            ))
        })
    }

    pub fn get_subscript(
        &mut self,
        path: &ast::Path,
    ) -> Result<Option<GetSubscriptData<'_>>, InternalCompilationError> {
        if path.is_empty() {
            return Ok(None);
        }

        let (module_id_opt, subscript_name) =
            match self.module_env.subscript_name_with_module(path)? {
                Some(k) => k,
                None => return Ok(None),
            };
        if self
            .module_env
            .is_unsafe_item_unavailable_in_current_context(module_id_opt, subscript_name)
        {
            return Err(
                InternalCompilationError::new_unsafe_feature_use_not_allowed(
                    UnsafeFeature::Subscript(subscript_name),
                    path.span().unwrap_or_else(Location::new_synthesized),
                ),
            );
        }

        Ok(if let Some(module_id) = module_id_opt {
            let source_module = self
                .module_env
                .modules
                .get(module_id)
                .unwrap()
                .module
                .as_ref()
                .unwrap();
            let id = source_module
                .get_local_subscript_id(subscript_name)
                .expect("resolved subscript should exist");
            let subscript = source_module.get_subscript_by_id(id).unwrap();
            self.new_deps.insert(module_id);
            Some((subscript, SubscriptId::new(module_id, id), Some(module_id)))
        } else {
            let id = self
                .module_env
                .current
                .get_local_subscript_id(subscript_name)
                .expect("resolved subscript should exist");
            let subscript = self.module_env.current.get_subscript_by_id(id).unwrap();
            Some((
                subscript,
                SubscriptId::new(self.current_module_id(), id),
                None,
            ))
        })
    }

    pub fn subscript_owner_module(&self, subscript_id: SubscriptId) -> &Module {
        if subscript_id.module == self.current_module_id() {
            self.module_env.current
        } else {
            self.module_env
                .modules
                .get(subscript_id.module)
                .and_then(|entry| entry.module.as_ref())
                .expect("subscript module should be loaded")
        }
    }

    pub fn get_std_function(
        &mut self,
        function_name: Ustr,
        span: Location,
    ) -> Result<GetFunctionWithPathData<'_>, InternalCompilationError> {
        let path = ast::Path::new(vec![(ustr("std"), span), (function_name, span)]);
        let function = if let Some(id) = self
            .module_env
            .current
            .get_local_function_id(function_name)
            .filter(|_| self.current_module_id() == STD_MODULE_ID)
        {
            let function = self.module_env.current.get_function_by_id(id).unwrap();
            (
                &function.definition,
                self.function_id(self.current_module_id(), id),
                None,
                function.code.runtime_argument_passing().map(<[_]>::to_vec),
            )
        } else {
            let source_module = self
                .module_env
                .modules
                .get(STD_MODULE_ID)
                .unwrap()
                .module
                .as_ref()
                .unwrap();
            let id = source_module
                .get_local_function_id(function_name)
                .unwrap_or_else(|| panic!("std function {function_name} should be available"));
            let function = source_module
                .get_function(function_name)
                .unwrap_or_else(|| panic!("std function {function_name} should be available"));
            (
                &function.definition,
                self.function_id(STD_MODULE_ID, id),
                Some(STD_MODULE_ID),
                function.code.runtime_argument_passing().map(<[_]>::to_vec),
            )
        };
        Ok((path, function))
    }

    pub fn get_std_subscript_member(
        &mut self,
        subscript_name: Ustr,
        mut_member: bool,
        span: Location,
    ) -> Result<GetSubscriptMemberWithPathData<'_>, InternalCompilationError> {
        let path = ast::Path::new(vec![(ustr("std"), span), (subscript_name, span)]);
        let member = if self.current_module_id() == STD_MODULE_ID
            && let Some(subscript) = self.module_env.current.get_subscript(subscript_name)
        {
            let member = select_subscript_member(subscript, subscript_name, mut_member);
            let function = self
                .module_env
                .current
                .get_function_by_id(member.function)
                .expect("std subscript function id should be valid");
            (
                subscript,
                member,
                (
                    &function.definition,
                    self.function_id(self.current_module_id(), member.function),
                    None,
                    function.code.runtime_argument_passing().map(<[_]>::to_vec),
                ),
            )
        } else {
            let source_module = self
                .module_env
                .modules
                .get(STD_MODULE_ID)
                .unwrap()
                .module
                .as_ref()
                .unwrap();
            let subscript = source_module
                .get_subscript(subscript_name)
                .unwrap_or_else(|| panic!("std subscript {subscript_name} should be available"));
            let member = select_subscript_member(subscript, subscript_name, mut_member);
            let function = source_module
                .get_function_by_id(member.function)
                .expect("std subscript function id should be valid");
            (
                subscript,
                member,
                (
                    &function.definition,
                    self.function_id(STD_MODULE_ID, member.function),
                    Some(STD_MODULE_ID),
                    function.code.runtime_argument_passing().map(<[_]>::to_vec),
                ),
            )
        };
        Ok((path, member))
    }

    pub fn get_type_def(
        &mut self,
        path: &ast::Path,
    ) -> Result<Option<TypeDefLookupResult>, InternalCompilationError> {
        let result = self.module_env.type_def_for_construction(path)?;
        Ok(result.map(|td| {
            if let Some(module_id) = td.0 {
                self.new_deps.insert(module_id);
            }
            td.1
        }))
    }
}
