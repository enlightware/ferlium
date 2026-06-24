// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{collections::VecDeque, mem};

use derive_new::new;
use enum_as_inner::EnumAsInner;
use ustr::Ustr;

use crate::module::id::Id;
use crate::std::array::array_value_from_vec;
use crate::std::value::{VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX};
use crate::{
    CompilerSession, FxHashMap, Location, ModuleRegistry, SourceId, SourceTable,
    compiler::error::RuntimeErrorKind,
    format::{FormatWith, write_with_separator},
    hir::function::{ResolvedArgPassing, ResolvedValueArgPassing, TrivialCopy},
    hir::value::{FunctionHiddenArgValue, FunctionValue, NativeValue, NativeValueType, Value},
    module::{
        ELocalDecl as LocalDecl, ExtraParameterId, FunctionId, LocalDebugVisibility, LocalDeclId,
        ModuleFunction, ModuleId, ProjectionIndex, ResolvedLocalClone, ResolvedLocalDrop,
        ResolvedTakeLocalValueMode, ResolvedValueLayout, TraitDictionary, TraitDictionaryEntry,
        TraitDictionaryId, TraitImplId,
    },
    std::buffer,
    types::{
        r#trait::{TraitDictionaryEntryIndex, TraitMethodIndex},
        r#type::{FnArgType, Type, TypeKind, bare_native_type},
    },
};
use crate::{
    Modules,
    hir::{self, CallArgument, ENodeArena, ENodeId, Elaborated, LoopId, NodeKind},
};

pub const DEFAULT_INTERACTIVE_FUEL_LIMIT: usize = 100_000;

/// Either a value or a unique mutable reference to a value.
/// This allows to implement the mutable value semantics.
#[derive(Debug, EnumAsInner)]
pub enum ValOrMut {
    /// A value, itself
    Val(Value),
    /// Runtime trait dictionary metadata.
    Dictionary(TraitDictionaryId),
    /// A shared reference to value storage outside the environment.
    ///
    /// This is used for interpreter-only call setup, for example when cloning a
    /// closure environment without first duplicating it with Rust `Clone`.
    Ref(*const Value),
    /// A mutable reference, index in the environment plus path within the value
    Mut(Place),
}

impl ValOrMut {
    pub fn from_primitive(value: impl NativeValue) -> Self {
        ValOrMut::Val(Value::native(value))
    }

    pub fn into_primitive<T: 'static>(self) -> Option<T> {
        match self {
            ValOrMut::Val(val) => val.into_primitive_ty::<T>(),
            ValOrMut::Dictionary(_) | ValOrMut::Ref(_) | ValOrMut::Mut(_) => None,
        }
    }

    pub fn as_mut_primitive<'a, 'b, T: 'static>(
        &self,
        ctx: &'a mut EvalCtx<'b>,
    ) -> Result<Option<&'a mut T>, RuntimeErrorKind> {
        Ok(match self {
            ValOrMut::Val(_) => None,
            ValOrMut::Dictionary(_) => None,
            ValOrMut::Ref(_) => None,
            ValOrMut::Mut(place) => place.target_mut(ctx)?.as_primitive_ty_mut::<T>(),
        })
    }

    pub fn as_primitive<'a, T: 'static>(
        &'a self,
        ctx: &'a EvalCtx<'_>,
    ) -> Result<Option<&'a T>, RuntimeErrorKind> {
        Ok(match self {
            ValOrMut::Val(val) => val.as_primitive_ty::<T>(),
            ValOrMut::Dictionary(_) => None,
            ValOrMut::Ref(value) => {
                // SAFETY: `Ref` entries are only installed for the duration of a
                // synchronous interpreter call, and the environment frame is
                // truncated before the borrowed storage can go away.
                unsafe { &**value }.as_primitive_ty::<T>()
            }
            ValOrMut::Mut(place) => place.target_ref(ctx)?.as_primitive_ty::<T>(),
        })
    }

    pub fn as_value_ref<'a>(&'a self, ctx: &'a EvalCtx<'_>) -> Result<&'a Value, RuntimeErrorKind> {
        Ok(match self {
            ValOrMut::Val(value) => {
                if matches!(value, Value::Uninit) {
                    panic!("attempted to read an uninitialized value");
                }
                value
            }
            ValOrMut::Dictionary(_) => panic!("attempted to read a trait dictionary as a Value"),
            ValOrMut::Ref(value) => {
                // SAFETY: see `ValOrMut::as_primitive`.
                unsafe { &**value }
            }
            ValOrMut::Mut(place) => place.target_ref(ctx)?,
        })
    }

    pub fn as_place(&self) -> &Place {
        match self {
            ValOrMut::Val(_) | ValOrMut::Dictionary(_) | ValOrMut::Ref(_) => {
                panic!("Cannot get a place from a value")
            }
            ValOrMut::Mut(place) => place,
        }
    }

    pub(crate) fn discard_storage(self) {
        if let ValOrMut::Val(value) = self {
            value.discard_storage();
        }
    }
}

/// Draining iterator that discards unconsumed owned argument storage on drop.
pub(crate) struct ValOrMutArgs {
    args: std::vec::IntoIter<ValOrMut>,
}

impl ValOrMutArgs {
    pub(crate) fn new(args: Vec<ValOrMut>) -> Self {
        Self {
            args: args.into_iter(),
        }
    }

    pub(crate) fn next(&mut self) -> Option<ValOrMut> {
        self.args.next()
    }
}

impl Drop for ValOrMutArgs {
    fn drop(&mut self) {
        for arg in self.args.by_ref() {
            arg.discard_storage();
        }
    }
}

impl FormatWith<EvalCtx<'_>> for ValOrMut {
    fn fmt_with(&self, f: &mut std::fmt::Formatter<'_>, data: &EvalCtx<'_>) -> std::fmt::Result {
        match self {
            ValOrMut::Val(_) => write!(f, "value"),
            ValOrMut::Dictionary(_) => write!(f, "dictionary metadata"),
            ValOrMut::Ref(_) => write!(f, "ref. value"),
            ValOrMut::Mut(place) => {
                write!(f, "mut. ref. {}", place.format_with(data))
            }
        }
    }
}

fn evidence_arg_to_val_or_mut(arg: FunctionHiddenArgValue) -> ValOrMut {
    match arg {
        FunctionHiddenArgValue::TraitDictionary(dictionary) => ValOrMut::Dictionary(dictionary),
        FunctionHiddenArgValue::FieldIndex(index) => ValOrMut::Val(Value::native(index)),
    }
}

/// Along with the Rust native stack, corresponds to the Zinc Abstract Machine of Caml language family
/// with the addition of Mutable Value Semantics through references to earlier stack frames
pub struct EvalCtx<'a> {
    /// all values or mutable references of all stack frames
    pub environment: Vec<ValOrMut>,
    /// base of current stack frame in `environment`
    pub frame_base: usize,
    /// hidden dictionary/evidence parameters for all stack frames
    extra_parameters: Vec<FunctionHiddenArgValue>,
    /// base of current stack frame in `extra_parameters`
    extra_frame_base: usize,
    /// current function call depth
    pub call_depth: usize,
    /// maximum function call depth
    pub call_depth_limit: usize,
    /// maximum number of values in the evaluation environment
    pub stack_limit: usize,
    /// remaining execution fuel; `None` means fuel checks are disabled
    pub fuel_remaining: Option<usize>,
    /// id of the current module for import slot resolution
    pub module_id: ModuleId,
    /// whether the current function returns a place result
    returns_place: bool,
    /// Per-run cache for layout lookups repeated by hot `TrivialCopy` call edges.
    trivial_copy_layout_cache: FxHashMap<(ModuleId, Type), ResolvedValueLayout>,
    /// session holding sources and other modules for error reporting and import resolution
    compiler_session: &'a CompilerSession,
}

impl<'a> EvalCtx<'a> {
    const DEFAULT_CALL_DEPTH_LIMIT: usize = 128;
    const DEFAULT_STACK_LIMIT: usize = 65_536;

    pub fn new(module_id: ModuleId, compiler_session: &'a CompilerSession) -> EvalCtx<'a> {
        Self::with_environment(module_id, Vec::new(), compiler_session)
    }

    fn reserve_current_frame_slots(&mut self, locals: &[LocalDecl]) {
        if let Some(max_slot) = locals.iter().map(|local| local.slot.as_index()).max() {
            self.ensure_environment_slot(self.frame_base + max_slot);
        }
    }

    /// Get the compiler session.
    pub fn compiler_session(&self) -> &'a CompilerSession {
        self.compiler_session
    }

    pub fn set_fuel(&mut self, fuel: usize) {
        self.fuel_remaining = Some(fuel);
    }

    pub fn set_fuel_limit(&mut self, fuel_limit: Option<usize>) {
        self.fuel_remaining = fuel_limit;
    }

    pub fn disable_fuel(&mut self) {
        self.fuel_remaining = None;
    }

    pub fn check_fuel(&mut self, span: Location) -> EvalControlFlowResult {
        let Some(fuel) = &mut self.fuel_remaining else {
            return cont(Value::unit());
        };
        if *fuel == 0 {
            Err(RuntimeError::new(
                RuntimeErrorKind::FuelExhausted,
                Some(span),
            ))
        } else {
            *fuel -= 1;
            cont(Value::unit())
        }
    }

    pub fn check_call_depth(&mut self, span: Location) -> EvalControlFlowResult {
        if self.call_depth >= self.call_depth_limit {
            Err(RuntimeError::new(
                RuntimeErrorKind::CallDepthLimitExceeded {
                    limit: self.call_depth_limit,
                },
                Some(span),
            ))
        } else {
            cont(Value::unit())
        }
    }

    /// Error out if growing the evaluation environment to `prospective_len` would reach the stack limit.
    /// `span` is `None` at call-frame entry, where the call site is attached as a backtrace frame by the caller instead.
    fn check_stack_limit(
        &self,
        prospective_len: usize,
        span: Option<Location>,
    ) -> Result<(), RuntimeError> {
        if prospective_len >= self.stack_limit {
            return Err(RuntimeError::new(
                RuntimeErrorKind::StackLimitExceeded {
                    limit: self.stack_limit,
                },
                span,
            ));
        }
        Ok(())
    }

    pub fn pop_environment_entry(&mut self) -> Option<ValOrMut> {
        self.environment.pop()
    }

    pub fn pop_environment_entry_discard(&mut self) {
        if let Some(entry) = self.pop_environment_entry() {
            entry.discard_storage();
        }
    }

    pub fn truncate_environment_storage(&mut self, len: usize) {
        while self.environment.len() > len {
            self.pop_environment_entry_discard();
        }
    }

    pub(crate) fn assert_no_owned_local_leaks_before_truncate(
        &self,
        locals: &[LocalDecl],
        len: usize,
        span: Location,
    ) {
        #[cfg(debug_assertions)]
        {
            for local in locals.iter().filter(|local| local.owns_storage()) {
                let index = self.frame_base + local.slot.as_index();
                if index < len || index >= self.environment.len() {
                    continue;
                }
                match &self.environment[index] {
                    ValOrMut::Val(Value::Uninit) => {}
                    ValOrMut::Val(_) => {
                        panic!(
                            "owned local `{}` left initialized at scope exit before environment \
                             truncation at {:?}; missing block cleanup or move",
                            local.name.0, span,
                        );
                    }
                    ValOrMut::Dictionary(_) | ValOrMut::Ref(_) | ValOrMut::Mut(_) => {}
                }
            }
        }
        #[cfg(not(debug_assertions))]
        let _ = (locals, len, span);
    }

    fn ensure_environment_slot(&mut self, index: usize) {
        while self.environment.len() <= index {
            self.environment.push(ValOrMut::Val(Value::uninit()));
        }
    }

    fn set_environment_entry(&mut self, index: usize, value: ValOrMut) {
        self.ensure_environment_slot(index);
        let old = mem::replace(&mut self.environment[index], value);
        old.discard_storage();
    }

    pub fn with_environment(
        module: ModuleId,
        environment: Vec<ValOrMut>,
        compiler_session: &'a CompilerSession,
    ) -> EvalCtx<'a> {
        EvalCtx {
            environment,
            frame_base: 0,
            extra_parameters: Vec::new(),
            extra_frame_base: 0,
            call_depth: 0,
            call_depth_limit: Self::DEFAULT_CALL_DEPTH_LIMIT,
            stack_limit: Self::DEFAULT_STACK_LIMIT,
            fuel_remaining: None,
            module_id: module,
            returns_place: false,
            trivial_copy_layout_cache: FxHashMap::default(),
            compiler_session,
        }
    }

    /// Get a function's code and module for a FunctionId at runtime.
    pub fn get_module_function(&self, function: FunctionId) -> &ModuleFunction {
        let module = self.compiler_session.expect_fresh_module(function.module);
        module.get_function_by_id(function.function).unwrap()
    }

    fn function_value_visible_argument_types(
        &self,
        function_value: &FunctionValue,
    ) -> Vec<FnArgType> {
        // Dynamic calls must use the actual callee signature. A dictionary
        // method value can have surface type `(A, A) -> R` while its runtime
        // `FunctionValue` points at a concrete method such as `Ord<int>::cmp`.
        self.get_module_function(function_value.function)
            .definition
            .ty_scheme
            .ty
            .args
            .clone()
    }

    /// Resolve a module-relative impl reference to a canonical runtime dictionary ID.
    pub fn get_dictionary_id(&self, dictionary: TraitImplId) -> TraitDictionaryId {
        TraitDictionaryId::new(dictionary.module, dictionary.impl_id)
    }

    pub fn dictionary_value(&self, dictionary: TraitDictionaryId) -> &TraitDictionary {
        let module = self
            .compiler_session
            .expect_fresh_module(dictionary.module_id);
        &module
            .get_impl_data(dictionary.impl_id)
            .unwrap_or_else(|| panic!("trait dictionary impl not found: {:?}", dictionary))
            .dictionary_value
    }

    /// Call a function value along containing its module context.
    pub fn call_function_value(
        &mut self,
        function_value: &FunctionValue,
        arguments: Vec<ValOrMut>,
        location: Location,
    ) -> EvalControlFlowResult {
        let function_id = function_value.function;

        let closure_env_dictionary = function_value
            .closure_env_value_dictionary
            .as_ref()
            .cloned();
        let closure_env_temp = if function_value.closure_env_len == 0 {
            None
        } else {
            let dictionary = closure_env_dictionary
                .expect("closures with captured values must carry a Value dictionary");
            let closure_env = call_value_clone_for_temp(
                self,
                dictionary,
                ValOrMut::Ref(&function_value.closure_env as *const Value),
                location,
            )?;
            let index = self.environment.len();
            self.environment.push(ValOrMut::Val(closure_env));
            Some(index)
        };

        let arguments = if function_value.closure_env_len == 0 {
            arguments
        } else {
            let mut prepared = Vec::with_capacity(function_value.closure_env_len + arguments.len());
            if let Some(target) = closure_env_temp {
                prepared.extend((0..function_value.closure_env_len).map(|index| {
                    ValOrMut::Mut(Place {
                        target,
                        path: vec![index as isize],
                    })
                }));
            }
            prepared.extend(arguments);
            prepared
        };

        let result = self
            .call_function(function_id, function_value.hidden_args.clone(), arguments)
            .map_err(|err| err.with_frame(function_id, location));

        if let Some(target) = closure_env_temp {
            let drop_result = call_value_drop_for_temp(
                self,
                closure_env_dictionary.expect("closure environment dictionary disappeared"),
                ValOrMut::Mut(Place {
                    target,
                    path: Vec::new(),
                }),
                location,
            );
            self.pop_environment_entry_discard();
            let result = match (result, drop_result) {
                (Ok(result), Ok(_)) => Ok(result),
                (Ok(result), Err(err)) => {
                    if let Some(value) = result.into_transfer_value() {
                        value.discard_storage();
                    }
                    Err(err)
                }
                (Err(err), _) => Err(err),
            };
            return result;
        }

        result
    }

    /// Call a function by its id, this will look up the function and its module.
    pub fn call_function_id(
        &mut self,
        function_id: FunctionId,
        arguments: Vec<ValOrMut>,
        location: Location,
    ) -> EvalControlFlowResult {
        self.call_function_id_with_extra(function_id, Vec::new(), arguments, location)
    }

    /// Call a function by its id with hidden dictionary/evidence parameters.
    pub fn call_function_id_with_extra(
        &mut self,
        function_id: FunctionId,
        extra_arguments: Vec<FunctionHiddenArgValue>,
        arguments: Vec<ValOrMut>,
        location: Location,
    ) -> EvalControlFlowResult {
        self.call_resolved_function_with_extra(function_id, extra_arguments, arguments, location)
    }

    /// Calls the function `local_id` of `module_id` directly, taking the target module explicitly
    /// rather than resolving it from the ambient `self.module_id`.
    ///
    /// This is the entry point for callers that already know the callee's module (such as the SSA
    /// interpreter, whose IR is fully module-resolved): `call_function` rotates `self.module_id` in
    /// and out around the call internally, so the caller never has to save/restore the ambient
    /// module itself.
    pub fn call_resolved_function_with_extra(
        &mut self,
        function_id: FunctionId,
        extra_arguments: Vec<FunctionHiddenArgValue>,
        arguments: Vec<ValOrMut>,
        location: Location,
    ) -> EvalControlFlowResult {
        self.call_function(function_id, extra_arguments, arguments)
            .map_err(|err| err.with_frame(function_id, location))
    }

    fn call_resolved_accessor_until_yield_with_extra(
        &mut self,
        function_id: FunctionId,
        extra_arguments: Vec<FunctionHiddenArgValue>,
        arguments: Vec<ValOrMut>,
        location: Location,
    ) -> Result<(SuspendedAccessor, Place), RuntimeError> {
        self.call_accessor_until_yield(function_id, extra_arguments, arguments)
            .map_err(|err| err.with_frame(function_id, location))
    }

    fn call_accessor_until_yield(
        &mut self,
        function_id: FunctionId,
        extra_arguments: Vec<FunctionHiddenArgValue>,
        arguments: Vec<ValOrMut>,
    ) -> Result<(SuspendedAccessor, Place), RuntimeError> {
        self.check_stack_limit(self.environment.len(), None)?;
        let local_id = function_id.function;
        let mut module_id = function_id.module;
        mem::swap(&mut self.module_id, &mut module_id);

        let module = self.compiler_session.expect_fresh_module(self.module_id);
        let function_data = module.get_function_by_id(local_id).unwrap();
        let script = function_data
            .code
            .as_script()
            .expect("WithYielded accessor must be a script function");
        let locals = &function_data.locals;
        let arena = &module.hir_arena;
        let previous_returns_place = mem::replace(
            &mut self.returns_place,
            function_data.definition.returns_place(),
        );
        let old_extra_frame_base = self.extra_frame_base;
        let extra_start = self.extra_parameters.len();
        self.extra_frame_base = extra_start;
        self.extra_parameters
            .extend(extra_arguments.iter().copied());

        let old_frame_base = self.frame_base;
        let frame_base = self.environment.len();
        self.frame_base = frame_base;
        self.environment.extend(arguments);
        self.call_depth += 1;

        let result = eval_node_with_ctx(arena, script.entry_node_id, self, locals);
        match result {
            Ok(ControlFlow::Transfer(ControlTransfer::Yield(place))) => {
                self.frame_base = old_frame_base;
                self.extra_frame_base = old_extra_frame_base;
                self.returns_place = previous_returns_place;
                mem::swap(&mut self.module_id, &mut module_id);
                Ok((
                    SuspendedAccessor {
                        function: function_id,
                        frame_base,
                        old_frame_base,
                        previous_returns_place,
                        old_extra_frame_base,
                        extra_start,
                    },
                    place,
                ))
            }
            Ok(result) => {
                self.call_depth -= 1;
                self.truncate_environment_storage(frame_base);
                self.extra_parameters.truncate(extra_start);
                self.frame_base = old_frame_base;
                self.extra_frame_base = old_extra_frame_base;
                self.returns_place = previous_returns_place;
                mem::swap(&mut self.module_id, &mut module_id);
                match result {
                    ControlFlow::Continue(value) => {
                        value.discard_storage();
                        panic!("WithYielded accessor returned without yielding")
                    }
                    ControlFlow::Transfer(transfer) => {
                        if let Some(value) = transfer.into_value() {
                            value.discard_storage();
                        }
                        panic!("WithYielded accessor exited before yielding")
                    }
                }
            }
            Err(err) => {
                let cleanup = drop_frame_owned_locals_on_error(
                    self,
                    locals,
                    arena[script.entry_node_id].span,
                );
                self.call_depth -= 1;
                self.truncate_environment_storage(frame_base);
                self.extra_parameters.truncate(extra_start);
                self.frame_base = old_frame_base;
                self.extra_frame_base = old_extra_frame_base;
                self.returns_place = previous_returns_place;
                mem::swap(&mut self.module_id, &mut module_id);
                cleanup?;
                Err(err)
            }
        }
    }

    fn resume_suspended_accessor_epilogue(
        &mut self,
        suspension: SuspendedAccessor,
        location: Location,
    ) -> EvalControlFlowResult {
        self.resume_suspended_accessor_epilogue_inner(suspension)
            .map_err(|err| err.with_frame(suspension.function, location))
    }

    fn resume_suspended_accessor_epilogue_inner(
        &mut self,
        suspension: SuspendedAccessor,
    ) -> EvalControlFlowResult {
        let caller_frame_base = self.frame_base;
        let caller_module_id = self.module_id;
        let caller_returns_place = self.returns_place;
        let caller_extra_frame_base = self.extra_frame_base;

        self.frame_base = suspension.frame_base;
        self.module_id = suspension.function.module;
        self.returns_place = false;
        self.extra_frame_base = suspension.extra_start;

        let module = self
            .compiler_session
            .expect_fresh_module(suspension.function.module);
        let function_data = module
            .get_function_by_id(suspension.function.function)
            .unwrap();
        let script = function_data
            .code
            .as_script()
            .expect("WithYielded accessor must be a script function");
        let yield_node_id = script
            .yield_node_id
            .expect("WithYielded accessor script must record its yield node");
        let locals = &function_data.locals;
        let arena = &module.hir_arena;

        let result =
            eval_epilogue_after_yield(arena, script.entry_node_id, yield_node_id, self, locals);
        let cleanup = if result.is_err() {
            drop_frame_owned_locals_on_error(self, locals, arena[yield_node_id].span)
        } else {
            Ok(())
        };

        self.call_depth -= 1;
        self.truncate_environment_storage(suspension.frame_base);
        self.extra_parameters.truncate(suspension.extra_start);
        self.frame_base = suspension.old_frame_base;
        self.extra_frame_base = suspension.old_extra_frame_base;
        self.returns_place = suspension.previous_returns_place;

        self.frame_base = caller_frame_base;
        self.module_id = caller_module_id;
        self.returns_place = caller_returns_place;
        self.extra_frame_base = caller_extra_frame_base;

        cleanup?;
        result
    }

    /// Call a function along with its correct module context.
    fn call_function(
        &mut self,
        function_id: FunctionId,
        extra_arguments: Vec<FunctionHiddenArgValue>,
        arguments: Vec<ValOrMut>,
    ) -> EvalControlFlowResult {
        self.check_stack_limit(self.environment.len(), None)?;
        let local_id = function_id.function;
        let mut module_id = function_id.module;
        // Use the new module for the duration of the function call.
        mem::swap(&mut self.module_id, &mut module_id);

        // Call the function.
        let module = self.compiler_session.expect_fresh_module(self.module_id);
        let function_data = module.get_function_by_id(local_id).unwrap();
        let locals = &function_data.locals;
        let previous_returns_place = mem::replace(
            &mut self.returns_place,
            function_data.definition.returns_place(),
        );
        let is_script = function_data.code.as_script().is_some();
        let old_extra_frame_base = is_script.then_some(self.extra_frame_base);
        let extra_start = is_script.then_some(self.extra_parameters.len());
        if let Some(extra_start) = extra_start {
            self.extra_frame_base = extra_start;
            self.extra_parameters
                .extend(extra_arguments.iter().copied());
        }
        let arguments = if is_script || extra_arguments.is_empty() {
            arguments
        } else {
            let mut prepared = Vec::with_capacity(extra_arguments.len() + arguments.len());
            prepared.extend(extra_arguments.into_iter().map(evidence_arg_to_val_or_mut));
            prepared.extend(arguments);
            prepared
        };
        let result = function_data.code.call(arguments, self, locals);
        if let Some(extra_start) = extra_start {
            self.extra_parameters.truncate(extra_start);
        }
        if let Some(old_extra_frame_base) = old_extra_frame_base {
            self.extra_frame_base = old_extra_frame_base;
        }
        self.returns_place = previous_returns_place;

        // Restore the previous module.
        mem::swap(&mut self.module_id, &mut module_id);

        // Return the call result.
        result
    }
}

/// A place in the environment (absolute position), with a path to a compound value
/// This behaves like a global address to a Value given our Mutable Value Semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Place {
    // index of target variable, absolute in the environment, to allow to access parent frames
    pub target: usize,
    // path within the compound value located at `target`
    pub path: Vec<isize>,
}

/// Internal runtime marker returned by addressor-place functions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlaceResult(Place);

impl NativeValueType for PlaceResult {}

impl PlaceResult {
    pub(crate) fn new(place: Place) -> Self {
        Self(place)
    }

    fn into_place(self) -> Place {
        self.0
    }

    /// Returns the place this addressor result denotes.
    pub fn place(&self) -> &Place {
        &self.0
    }
}

#[derive(Debug, Clone, Copy)]
struct SuspendedAccessor {
    function: FunctionId,
    frame_base: usize,
    old_frame_base: usize,
    previous_returns_place: bool,
    old_extra_frame_base: usize,
    extra_start: usize,
}

fn invalid_buffer_index(index: isize, len: usize) -> RuntimeErrorKind {
    RuntimeErrorKind::InvalidArgument(format!(
        "Buffer index {index} is out of bounds for buffer of length {len}"
    ))
}

impl Place {
    /// Return a path and an index of a variable in the environment that is for sure a Value
    fn resolved_path_and_index(&self, ctx: &EvalCtx) -> (VecDeque<isize>, usize) {
        let mut path = self.path.iter().copied().collect::<VecDeque<_>>();
        let mut index = self.target;
        loop {
            match &ctx.environment[index] {
                ValOrMut::Val(_target) => {
                    break;
                }
                ValOrMut::Dictionary(_) => {
                    panic!("cannot mutably access trait dictionary metadata");
                }
                ValOrMut::Ref(_) => {
                    panic!("cannot mutably access shared reference storage");
                }
                ValOrMut::Mut(place) => {
                    index = place.target;
                    for &index in place.path.iter().rev() {
                        path.push_front(index);
                    }
                }
            };
        }
        (path, index)
    }

    fn resolved(&self, ctx: &EvalCtx) -> Self {
        let (path, target) = self.resolved_path_and_index(ctx);
        Self {
            target,
            path: path.into_iter().collect(),
        }
    }

    /// Get a mutable reference to the target value
    pub fn target_mut<'c>(&self, ctx: &'c mut EvalCtx) -> Result<&'c mut Value, RuntimeErrorKind> {
        let (path, index) = self.resolved_path_and_index(ctx);
        let mut target = ctx.environment[index].as_val_mut().unwrap();
        for &index in path.iter() {
            use Value::*;
            target = match target {
                Tuple(tuple) => tuple.get_mut(index as usize).unwrap(),
                Variant(variant) if index == 0 => &mut variant.value,
                Native(primitive) => {
                    let buffer = primitive
                        .as_mut()
                        .as_mut_any()
                        .downcast_mut::<buffer::Buffer>()
                        .unwrap();
                    let len = buffer.capacity();
                    match buffer.get_mut_signed(index) {
                        Some(target) => target,
                        None => {
                            return Err(invalid_buffer_index(index, len));
                        }
                    }
                }
                Uninit => panic!("cannot access a field of an uninitialized value"),
                Variant(_) => panic!("Cannot access a variant payload with a non-zero index"),
                _ => panic!("Cannot access a non-compound value"),
            };
        }
        Ok(target)
    }

    pub(crate) fn target_ref_allow_uninit<'c>(
        &self,
        ctx: &'c EvalCtx,
    ) -> Result<&'c Value, RuntimeErrorKind> {
        let mut path = self.path.iter().copied().collect::<VecDeque<_>>();
        let mut index = self.target;
        let mut target = loop {
            match &ctx.environment[index] {
                ValOrMut::Val(target) => break target,
                ValOrMut::Dictionary(_) => {
                    panic!("cannot read trait dictionary metadata as a Value")
                }
                ValOrMut::Ref(target) => {
                    // SAFETY: see `ValOrMut::as_primitive`.
                    break unsafe { &**target };
                }
                ValOrMut::Mut(place) => {
                    index = place.target;
                    for &index in place.path.iter().rev() {
                        path.push_front(index);
                    }
                }
            };
        };
        for &index in path.iter() {
            use Value::*;
            target = match target {
                Tuple(tuple) => tuple.get(index as usize).unwrap(),
                Variant(variant) if index == 0 => &variant.value,
                Native(primitive) => {
                    let buffer = NativeValue::as_any(primitive.as_ref())
                        .downcast_ref::<buffer::Buffer>()
                        .unwrap();
                    let len = buffer.capacity();
                    match buffer.get_signed(index) {
                        Some(target) => target,
                        None => {
                            return Err(invalid_buffer_index(index, len));
                        }
                    }
                }
                Uninit => panic!("cannot read a field of an uninitialized value"),
                Variant(_) => panic!("Cannot access a variant payload with a non-zero index"),
                _ => panic!("Cannot access a non-compound value"),
            };
        }
        Ok(target)
    }

    /// Get a shared reference to the target value
    pub fn target_ref<'c>(&self, ctx: &'c EvalCtx) -> Result<&'c Value, RuntimeErrorKind> {
        let target = self.target_ref_allow_uninit(ctx)?;
        if matches!(target, Value::Uninit) {
            panic!("attempted to read an uninitialized value");
        }
        Ok(target)
    }
}

impl FormatWith<EvalCtx<'_>> for Place {
    fn fmt_with(&self, f: &mut std::fmt::Formatter<'_>, data: &EvalCtx<'_>) -> std::fmt::Result {
        let Place { target, path } = self;
        let ctx = data;
        let relative_index = *target as isize - ctx.frame_base as isize;
        write!(f, "@{relative_index}")?;
        if !path.is_empty() {
            write!(f, ".")?;
        }
        write_with_separator(path, ".", f)?;
        if relative_index < 0 {
            write!(f, " (in a previous frame)")?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum ControlFlow<V> {
    Continue(V),
    Transfer(ControlTransfer),
}

#[derive(Debug)]
pub enum ControlTransfer {
    Return(Value),
    Yield(Place),
    Break { label: LoopId, value: Value },
    Continue { label: LoopId },
}
impl<V> ControlFlow<V> {
    fn map_continue<U>(self, f: impl FnOnce(V) -> U) -> ControlFlow<U> {
        match self {
            ControlFlow::Continue(value) => ControlFlow::Continue(f(value)),
            ControlFlow::Transfer(transfer) => ControlFlow::Transfer(transfer),
        }
    }

    fn into_transfer_value(self) -> Option<Value> {
        match self {
            ControlFlow::Continue(_) => None,
            ControlFlow::Transfer(transfer) => transfer.into_value(),
        }
    }
}

impl ControlTransfer {
    fn into_value(self) -> Option<Value> {
        match self {
            ControlTransfer::Return(value) | ControlTransfer::Break { value, .. } => Some(value),
            ControlTransfer::Yield(_) | ControlTransfer::Continue { .. } => None,
        }
    }
}

fn unreachable_continue<T, U>(_: T) -> U {
    unreachable!("continue value is handled before propagating control transfer")
}

impl ControlFlow<Value> {
    pub fn into_value(self) -> Value {
        match self {
            ControlFlow::Continue(value) => value,
            ControlFlow::Transfer(ControlTransfer::Return(value)) => value,
            ControlFlow::Transfer(
                ControlTransfer::Yield(_)
                | ControlTransfer::Break { .. }
                | ControlTransfer::Continue { .. },
            ) => {
                panic!("control transfer escaped its target")
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct BacktraceFrame {
    function_id: FunctionId,
    call_site: Location,
}
impl BacktraceFrame {
    fn fmt_with_suspended_at(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        data: &(&SourceTable, &Modules),
        suspended_at: Option<Location>,
    ) -> std::fmt::Result {
        let (source_table, modules) = data;
        let module = modules
            .get(self.function_id.module)
            .unwrap()
            .module
            .as_ref()
            .unwrap();
        let function_module_path = modules
            .get_name(self.function_id.module)
            .map(|name| format!("{name}"))
            .unwrap_or_else(|| format!("#{}", self.function_id.module));
        let function_name = module
            .get_function_name_by_id(self.function_id.function)
            .map(|name| name.to_string())
            .unwrap_or_else(|| format!("#{}", self.function_id.function));
        write!(f, "{function_module_path}::{function_name}")?;
        write!(f, " at {}", self.call_site.format_with(source_table))?;
        if let Some(suspended_at) = suspended_at
            && let Some(function) = module.get_function_by_id(self.function_id.function)
        {
            let locals = function
                .debug_info
                .locals_at_source(suspended_at, LocalDebugVisibility::User);
            if !locals.is_empty() {
                write!(f, "\n     locals: ")?;
                write_with_separator(locals.iter().map(|local| local.name), ", ", f)?;
            }
        }
        Ok(())
    }
}
impl FormatWith<(&SourceTable, &Modules)> for BacktraceFrame {
    fn fmt_with(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        data: &(&SourceTable, &Modules),
    ) -> std::fmt::Result {
        self.fmt_with_suspended_at(f, data, None)
    }
}

impl FormatWith<(&SourceTable, ModuleRegistry<'_>)> for BacktraceFrame {
    fn fmt_with(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        data: &(&SourceTable, ModuleRegistry<'_>),
    ) -> std::fmt::Result {
        self.fmt_with_suspended_at(f, &(data.0, data.1.raw()), None)
    }
}

/// A runtime error that occurred during evaluation and is propagated upwards.
#[derive(Debug, Clone, new)]
pub struct RuntimeError {
    /// The kind of the error.
    pub(crate) kind: RuntimeErrorKind,
    /// The location where the error occurred, None if in native code.
    pub(crate) location: Option<Location>,
    /// The call stack at the time of the error.
    #[new(default)]
    pub(crate) backtrace: Vec<BacktraceFrame>,
}
impl RuntimeError {
    pub fn new_native(kind: RuntimeErrorKind) -> Self {
        Self {
            kind,
            location: None,
            backtrace: Vec::new(),
        }
    }

    pub fn with_frame(self, function_id: FunctionId, location: Location) -> Self {
        let mut backtrace = self.backtrace;
        backtrace.push(BacktraceFrame {
            function_id,
            call_site: location,
        });
        Self {
            kind: self.kind,
            location: self.location,
            backtrace,
        }
    }

    pub fn kind(&self) -> RuntimeErrorKind {
        self.kind.clone()
    }

    pub fn location(&self) -> Option<Location> {
        self.location
    }

    pub fn backtrace(&self) -> &Vec<BacktraceFrame> {
        &self.backtrace
    }

    pub fn top_most_location_in(&self, source_id: SourceId) -> Option<Location> {
        if let Some(location) = self.location
            && location.source_id == source_id
        {
            return Some(location);
        }
        for frame in &self.backtrace {
            if frame.call_site.source_id == source_id {
                return Some(frame.call_site);
            }
        }
        None
    }
}

impl FormatWith<(&SourceTable, &Modules)> for RuntimeError {
    fn fmt_with(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        data: &(&SourceTable, &Modules),
    ) -> std::fmt::Result {
        write!(f, "Execution error: {}", self.kind)?;
        if let Some(location) = &self.location {
            write!(f, " at {}", location.format_with(data.0))?;
        }
        writeln!(f)?;
        if !self.backtrace.is_empty() {
            writeln!(f, "stack backtrace:")?;
            let mut suspended_at = self.location;
            for (i, frame) in self.backtrace.iter().enumerate() {
                write!(f, "  {i}: ")?;
                frame.fmt_with_suspended_at(f, data, suspended_at)?;
                writeln!(f)?;
                suspended_at = Some(frame.call_site);
            }
        }
        Ok(())
    }
}

impl FormatWith<(&SourceTable, ModuleRegistry<'_>)> for RuntimeError {
    fn fmt_with(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        data: &(&SourceTable, ModuleRegistry<'_>),
    ) -> std::fmt::Result {
        self.fmt_with(f, &(data.0, data.1.raw()))
    }
}

/// The result of evaluating an HIR node, either a control flow action or a runtime error.
pub type EvalControlFlowResult = Result<ControlFlow<Value>, RuntimeError>;

/// The result of evaluating an HIR node, either a value or a runtime error.
pub type EvalResult = Result<Value, RuntimeError>;

pub fn cont(value: Value) -> EvalControlFlowResult {
    Ok(ControlFlow::Continue(value))
}

pub fn ret(value: Value) -> EvalControlFlowResult {
    Ok(ControlFlow::Transfer(ControlTransfer::Return(value)))
}

/// Helper macro to evaluate a node and propagate Return, or extract Continue value.
/// Usage: eval_or_return!(node.eval_with_ctx(ctx))
/// Returns early with Return, or provides the unwrapped Value.
macro_rules! eval_or_return {
    ($expr:expr) => {
        match $expr? {
            ControlFlow::Continue(val) => val,
            ControlFlow::Transfer(transfer) => return Ok(ControlFlow::Transfer(transfer)),
        }
    };
}

/// Evaluate this node and return the result.
pub fn eval_node(
    arena: &ENodeArena,
    node_id: ENodeId,
    module_id: ModuleId,
    locals: &[LocalDecl],
    compiler_session: &CompilerSession,
) -> EvalControlFlowResult {
    let mut ctx = EvalCtx::new(module_id, compiler_session);
    eval_node_with_ctx(arena, node_id, &mut ctx, locals)
}

/// Evaluate this node given the environment and return the result.
pub fn eval_node_with_ctx(
    arena: &ENodeArena,
    node_id: ENodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    use NodeKind::*;
    let node = &arena[node_id];
    match &node.kind {
        Immediate(immediate) => cont(immediate.clone().into_value()),
        Uninit => cont(Value::uninit()),
        BuildClosure(build_closure) => eval_build_closure(arena, build_closure, ctx, locals),
        Apply(app) => eval_apply(arena, app, node.span, ctx, locals),
        CloneClosureEnv(node) => {
            eval_clone_closure_env(arena, node, arena[node_id].span, ctx, locals)
        }
        DropClosureEnv(node) => {
            eval_drop_closure_env(arena, node, arena[node_id].span, ctx, locals)
        }
        CloneValue(node) => eval_clone_value(arena, node, arena[node_id].span, ctx, locals),
        StaticApply(app) => eval_static_apply(arena, app, node.span, ctx, locals),
        TraitMethodApply(_)
        | GetTraitMethod(_)
        | GetTraitAssociatedConst(_)
        | GetTraitDictionary(_) => {
            panic!("unelaborated trait operation should not be executed");
        }
        GetFunction(get_fn) => cont(Value::function(get_fn.function)),
        GetDictionary(_) | LoadDictionary(_) => {
            panic!("dictionary metadata should not be evaluated as a Value")
        }
        CheckCallDepth => ctx.check_call_depth(node.span),
        CheckFuel => ctx.check_fuel(node.span),
        LoadFieldIndex(node) => cont(Value::native(field_index_from_extra_parameter(
            ctx,
            node.extra_parameter,
        ))),
        GetDictionaryMethod(node) => eval_get_dictionary_method(arena, node, ctx),
        GetDictionaryAssociatedConst(node) => {
            eval_get_dictionary_associated_const(arena, node, ctx)
        }
        CallDictionaryMethod(node) => {
            eval_call_dictionary_method(arena, node, arena[node_id].span, ctx, locals)
        }
        StoreLocal(node) => eval_store_local(arena, node, arena[node_id].span, ctx, locals),
        TakeLocalValue(node) => eval_take_local_value(node, arena[node_id].span, ctx, locals),
        LoadLocal(node) => eval_load_local(arena, node_id, node, ctx, locals),
        Return(node) => eval_return(arena, *node, ctx, locals),
        Yield(node) => eval_yield(arena, *node, ctx, locals),
        WithYielded(node) => eval_with_yielded(arena, node, arena[node_id].span, ctx, locals),
        WithPlace(node) => eval_with_place(arena, node, ctx, locals),
        Block(block) => eval_block(arena, block, ctx, locals),
        Assign(assignment) => eval_assign(arena, node_id, assignment, ctx, locals),
        Tuple(nodes) | Record(nodes) => eval_tuple(arena, nodes, ctx, locals),
        Project(node) => eval_project(arena, node_id, node.value, node.index, ctx, locals),
        FieldAccess(_) => panic!("field access should not be executed after elaboration"),
        ProjectAt(node) => eval_project_at(arena, node_id, node.value, node.index, ctx, locals),
        Variant(node) => eval_variant(arena, node.tag, node.payload, ctx, locals),
        ExtractTag(node) => eval_extract_tag(arena, *node, ctx, locals),
        Array(nodes) => eval_array(arena, nodes, ctx, locals),
        Case(case) => eval_case(arena, case, ctx, locals),
        Loop(node) => eval_loop(arena, node.label, node.body, ctx, locals),
        Break(node) => {
            let value = eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals));
            Ok(ControlFlow::Transfer(ControlTransfer::Break {
                label: node.label,
                value,
            }))
        }
        Continue(node) => Ok(ControlFlow::Transfer(ControlTransfer::Continue {
            label: node.label,
        })),
    }
}

#[inline(never)]
fn eval_build_closure(
    arena: &ENodeArena,
    build_closure: &hir::BuildClosure<Elaborated>,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let mut hidden_args = Vec::with_capacity(build_closure.dictionary_captures.len());
    for &capture in &build_closure.dictionary_captures {
        hidden_args.push(eval_or_return!(eval_function_hidden_arg_node(
            arena, capture, ctx, locals
        )));
    }
    let captures = eval_or_return!(eval_nodes(arena, &build_closure.captures, ctx, locals));
    let captures_value_dictionary = if let Some(dict) = build_closure.captures_value_dictionary {
        Some(eval_or_return!(eval_dictionary_metadata_node(
            arena, dict, ctx
        )))
    } else {
        None
    };
    // Note: function should be GetFunction or similar immediate - returns not allowed here.
    let function_value =
        eval_node_with_ctx(arena, build_closure.function, ctx, locals)?.into_value();
    let function_value = function_value.into_function().unwrap();
    let function_value = FunctionValue::closure(
        function_value.function,
        hidden_args,
        captures,
        captures_value_dictionary,
    );
    cont(Value::function_value(function_value))
}

fn eval_function_hidden_arg_node(
    arena: &ENodeArena,
    node: ENodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<FunctionHiddenArgValue>, RuntimeError> {
    if let NodeKind::LoadFieldIndex(load) = &arena[node].kind {
        return Ok(ControlFlow::Continue(FunctionHiddenArgValue::FieldIndex(
            field_index_from_extra_parameter(ctx, load.extra_parameter),
        )));
    }
    if let Some(dictionary) = try_dictionary_metadata_node(arena, node, ctx) {
        return Ok(ControlFlow::Continue(
            FunctionHiddenArgValue::TraitDictionary(dictionary),
        ));
    }
    let value = eval_or_return!(eval_node_with_ctx(arena, node, ctx, locals));
    let Some(index) = value.into_primitive_ty::<isize>() else {
        panic!("expected hidden function evidence to be a trait dictionary or field index");
    };
    Ok(ControlFlow::Continue(FunctionHiddenArgValue::FieldIndex(
        index,
    )))
}

fn eval_function_hidden_arg_nodes(
    arena: &ENodeArena,
    nodes: &[ENodeId],
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<Vec<FunctionHiddenArgValue>>, RuntimeError> {
    // Hidden-argument values are Copy (dictionary ids / field indices) and own no storage.
    eval_sequence(
        nodes.iter().copied(),
        nodes.len(),
        |_| {},
        |node| eval_function_hidden_arg_node(arena, node, ctx, locals),
    )
}

fn eval_dictionary_metadata_node(
    arena: &ENodeArena,
    node: ENodeId,
    ctx: &mut EvalCtx,
) -> Result<ControlFlow<TraitDictionaryId>, RuntimeError> {
    if let Some(dictionary) = try_dictionary_metadata_node(arena, node, ctx) {
        return Ok(ControlFlow::Continue(dictionary));
    }
    panic!(
        "expected dictionary metadata node, got {:?}",
        arena[node].kind
    )
}

fn try_dictionary_metadata_node(
    arena: &ENodeArena,
    node: ENodeId,
    ctx: &EvalCtx,
) -> Option<TraitDictionaryId> {
    match &arena[node].kind {
        NodeKind::GetDictionary(get_dict) => Some(ctx.get_dictionary_id(get_dict.dictionary)),
        NodeKind::LoadDictionary(load) => match extra_parameter_value(ctx, load.extra_parameter) {
            FunctionHiddenArgValue::TraitDictionary(dictionary) => Some(dictionary),
            FunctionHiddenArgValue::FieldIndex(_) => {
                panic!("expected dictionary extra parameter")
            }
        },
        _ => None,
    }
}

pub(crate) fn try_dictionary_from_place(place: &Place, ctx: &EvalCtx) -> Option<TraitDictionaryId> {
    let mut path = place.path.iter().copied().collect::<VecDeque<_>>();
    let mut index = place.target;
    loop {
        match &ctx.environment[index] {
            ValOrMut::Dictionary(dictionary) => {
                return path.is_empty().then_some(*dictionary);
            }
            ValOrMut::Mut(place) => {
                index = place.target;
                for &index in place.path.iter().rev() {
                    path.push_front(index);
                }
            }
            ValOrMut::Val(_) | ValOrMut::Ref(_) => return None,
        }
    }
}

fn dictionary_from_extra_parameter(
    ctx: &EvalCtx,
    extra_parameter: ExtraParameterId,
) -> TraitDictionaryId {
    match extra_parameter_value(ctx, extra_parameter) {
        FunctionHiddenArgValue::TraitDictionary(dictionary) => dictionary,
        FunctionHiddenArgValue::FieldIndex(_) => panic!(
            "expected extra parameter {} to contain trait dictionary metadata",
            extra_parameter.as_index()
        ),
    }
}

fn field_index_from_extra_parameter(ctx: &EvalCtx, extra_parameter: ExtraParameterId) -> isize {
    match extra_parameter_value(ctx, extra_parameter) {
        FunctionHiddenArgValue::FieldIndex(index) => index,
        FunctionHiddenArgValue::TraitDictionary(_) => panic!(
            "expected extra parameter {} to contain a field index",
            extra_parameter.as_index()
        ),
    }
}

fn extra_parameter_value(
    ctx: &EvalCtx,
    extra_parameter: ExtraParameterId,
) -> FunctionHiddenArgValue {
    ctx.extra_parameters[ctx.extra_frame_base + extra_parameter.as_index()]
}

fn call_dictionary_method(
    ctx: &mut EvalCtx,
    dictionary: TraitDictionaryId,
    entry_index: TraitDictionaryEntryIndex,
    arguments: Vec<ValOrMut>,
    span: Location,
) -> EvalControlFlowResult {
    let TraitDictionaryEntry::Method(function) =
        ctx.dictionary_value(dictionary).entry(entry_index)
    else {
        panic!("attempted to call a non-method dictionary entry");
    };
    let function_value = FunctionValue::bare(FunctionId::new(dictionary.module_id, function));
    ctx.call_function_value(&function_value, arguments, span)
}

fn eval_get_dictionary_method(
    arena: &ENodeArena,
    node: &hir::GetDictionaryMethod<Elaborated>,
    ctx: &mut EvalCtx,
) -> EvalControlFlowResult {
    let dictionary = eval_or_return!(eval_dictionary_metadata_node(arena, node.dictionary, ctx));
    let TraitDictionaryEntry::Method(function) =
        ctx.dictionary_value(dictionary).entry(node.entry_index)
    else {
        panic!("attempted to get a non-method dictionary entry as a function");
    };
    cont(Value::function(FunctionId::new(
        dictionary.module_id,
        function,
    )))
}

fn eval_get_dictionary_associated_const(
    arena: &ENodeArena,
    node: &hir::GetDictionaryAssociatedConst<Elaborated>,
    ctx: &mut EvalCtx,
) -> EvalControlFlowResult {
    let dictionary = eval_or_return!(eval_dictionary_metadata_node(arena, node.dictionary, ctx));
    let TraitDictionaryEntry::AssociatedConst(value) =
        ctx.dictionary_value(dictionary).entry(node.entry_index)
    else {
        panic!("attempted to get a non-associated-const dictionary entry as a value");
    };
    cont(value.into_value())
}

fn eval_call_dictionary_method(
    arena: &ENodeArena,
    node: &hir::CallDictionaryMethod<Elaborated>,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    eval_call_dictionary_method_with(arena, node, span, ctx, locals, eval_args)
}

fn eval_addressor_place_call_dictionary_method(
    arena: &ENodeArena,
    node: &hir::CallDictionaryMethod<Elaborated>,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    eval_call_dictionary_method_with(arena, node, span, ctx, locals, eval_addressor_place_args)
}

fn eval_call_dictionary_method_with(
    arena: &ENodeArena,
    node: &hir::CallDictionaryMethod<Elaborated>,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
    eval_args_fn: EvalArgsFn,
) -> EvalControlFlowResult {
    let dictionary = eval_or_return!(eval_dictionary_metadata_node(arena, node.dictionary, ctx));
    let temp_start = ctx.environment.len();
    let mut arguments = eval_or_return!(eval_args_fn(
        arena,
        &node.arguments,
        &node.ty.fn_ty.args,
        ctx,
        locals,
    ));
    let result = call_dictionary_method(
        ctx,
        dictionary,
        node.entry_index,
        arguments.take_arguments(),
        span,
    );
    finish_call(ctx, temp_start, result)
}

fn discard_call_result(result: EvalControlFlowResult) -> Result<(), RuntimeError> {
    result?.into_value().discard_storage();
    Ok(())
}

/// Invoke a resolved `Value` method (clone or drop) for a local-dispatch site.
fn call_resolved_value_method(
    ctx: &mut EvalCtx,
    dispatch: ResolvedValueMethod,
    method_index: TraitMethodIndex,
    arguments: Vec<ValOrMut>,
    span: Location,
) -> EvalControlFlowResult {
    match dispatch {
        ResolvedValueMethod::Static(function) => ctx.call_function_id(function, arguments, span),
        ResolvedValueMethod::Dictionary(dict_index) => {
            let dictionary = dictionary_from_extra_parameter(ctx, dict_index);
            call_dictionary_method(
                ctx,
                dictionary,
                TraitDictionaryEntryIndex::from_index(method_index.as_index()),
                arguments,
                span,
            )
        }
    }
}

#[derive(Clone, Copy)]
enum ResolvedValueMethod {
    Static(FunctionId),
    Dictionary(ExtraParameterId),
}

fn clone_value_method_dispatch(clone: &ResolvedLocalClone) -> Option<ResolvedValueMethod> {
    match clone {
        ResolvedLocalClone::TrivialCopy => None,
        ResolvedLocalClone::Static(function) => Some(ResolvedValueMethod::Static(*function)),
        ResolvedLocalClone::Dictionary(dictionary) => {
            Some(ResolvedValueMethod::Dictionary(*dictionary))
        }
    }
}

fn call_local_drop_dispatch(
    ctx: &mut EvalCtx,
    drop: ResolvedLocalDrop,
    target: Place,
    span: Location,
) -> Result<(), RuntimeError> {
    let dispatch = match drop {
        ResolvedLocalDrop::Skip => return Ok(()),
        ResolvedLocalDrop::Static(function) => ResolvedValueMethod::Static(function),
        ResolvedLocalDrop::Dictionary(dictionary) => ResolvedValueMethod::Dictionary(dictionary),
    };
    discard_call_result(call_resolved_value_method(
        ctx,
        dispatch,
        VALUE_DROP_METHOD_INDEX,
        vec![ValOrMut::Mut(target)],
        span,
    ))
}

fn resolved_local_drop(drop: &ResolvedLocalDrop) -> ResolvedLocalDrop {
    *drop
}

fn resolved_local_clone(clone: &ResolvedLocalClone) -> ResolvedLocalClone {
    *clone
}

pub(crate) fn drop_frame_owned_locals_on_error(
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
    span: Location,
) -> Result<(), RuntimeError> {
    drop_owned_locals_on_error_from(ctx, locals, ctx.frame_base, span)
}

fn drop_owned_locals_on_error_from(
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
    start_environment_index: usize,
    span: Location,
) -> Result<(), RuntimeError> {
    for (index, local) in locals.iter().enumerate().rev() {
        if !local.owns_storage() {
            continue;
        }
        let Some(drop) = local.local_drop() else {
            continue;
        };
        let id = LocalDeclId::from_index(index);
        let target_index = local_environment_index(ctx, locals, id);
        if target_index < start_environment_index {
            continue;
        }
        if target_index >= ctx.environment.len() {
            continue;
        }
        let target = local_place(ctx, locals, id);
        if place_contains_uninit(ctx, &target, span)? {
            continue;
        }
        call_local_drop_dispatch(ctx, resolved_local_drop(drop), target.clone(), span)?;
        discard_value_storage_at_place(ctx, &target, span)?;
    }
    Ok(())
}

/// A trait dictionary handed to a `Value`-trait helper (clone/drop), in either of the two runtime
/// forms the interpreters produce.
///
/// The HIR interpreter resolves dictionaries to interned [`TraitDictionaryId`]s and dispatches
/// methods through the compiler's impl arena. The SSA interpreter — whose IR is meant to lower to a
/// real backend — instead materializes a dictionary as a *witness table*: a `Value::Tuple` of the
/// dictionary's method function values (in entry order) followed by its associated constants,
/// reachable through a [`Place`]. `DictArg` lets the shared `Value` helpers serve both without the
/// SSA backend having to reconstruct an interned id (a compiler-arena handle that does not exist in
/// compiled code).
///
/// A bare [`TraitDictionaryId`] converts into the [`DictArg::Interned`] form, so existing HIR
/// callers pass one unchanged.
pub(crate) enum DictArg {
    /// An interned dictionary resolved through the compiler session (HIR interpreter form).
    Interned(TraitDictionaryId),
    /// A place holding a materialized witness-table tuple (SSA interpreter form).
    Witness(Place),
}

impl From<TraitDictionaryId> for DictArg {
    fn from(dictionary: TraitDictionaryId) -> Self {
        DictArg::Interned(dictionary)
    }
}

impl DictArg {
    /// Dispatches the method at `entry_index` with `arguments`, handling both dictionary forms.
    ///
    /// For the interned form this defers to [`call_dictionary_method`]; for the witness form it
    /// reads the method function value straight out of the tuple at `entry_index` and calls it. A
    /// witness method entry is materialized bare (no captured evidence), exactly as
    /// [`call_dictionary_method`] reconstructs it from an interned dictionary.
    fn call_method(
        &self,
        ctx: &mut EvalCtx,
        entry_index: TraitDictionaryEntryIndex,
        arguments: Vec<ValOrMut>,
        span: Location,
    ) -> EvalControlFlowResult {
        match self {
            DictArg::Interned(dictionary) => {
                call_dictionary_method(ctx, *dictionary, entry_index, arguments, span)
            }
            DictArg::Witness(place) => {
                let method = {
                    let table = place
                        .target_ref(ctx)
                        .map_err(|err| RuntimeError::new(err, Some(span)))?;
                    let entries = table
                        .as_tuple()
                        .expect("an SSA witness-table dictionary is a tuple value");
                    let function = entries[entry_index.as_index()]
                        .as_function()
                        .expect("a witness-table method entry is a function value");
                    FunctionValue::bare(function.function_id, function.module_id)
                };
                ctx.call_function_value(&method, arguments, span)
            }
        }
    }
}

fn call_value_clone_with(
    ctx: &mut EvalCtx,
    source: ValOrMut,
    _span: Location,
    call: impl FnOnce(&mut EvalCtx, Vec<ValOrMut>) -> EvalControlFlowResult,
) -> Result<Value, RuntimeError> {
    Ok(call(ctx, vec![source])?.into_value())
}

pub(crate) fn call_value_clone_for_temp(
    ctx: &mut EvalCtx,
    dictionary: impl Into<DictArg>,
    source: ValOrMut,
    span: Location,
) -> Result<Value, RuntimeError> {
    let dictionary = dictionary.into();
    call_value_clone_with(ctx, source, span, |ctx, arguments| {
        dictionary.call_method(
            ctx,
            TraitDictionaryEntryIndex::from_index(VALUE_CLONE_METHOD_INDEX.as_index()),
            arguments,
            span,
        )
    })
}

pub(crate) fn call_value_clone_to_target(
    ctx: &mut EvalCtx,
    dictionary: impl Into<DictArg>,
    source: ValOrMut,
    target: Place,
    span: Location,
) -> EvalControlFlowResult {
    let target_value = target
        .target_mut(ctx)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    assert!(
        matches!(target_value, Value::Uninit),
        "Value::clone destination slot must be uninitialized"
    );
    let value = call_value_clone_for_temp(ctx, dictionary, source, span)?;
    let target_value = target
        .target_mut(ctx)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    *target_value = value;
    cont(Value::unit())
}

fn call_value_clone_dispatch_for_temp(
    ctx: &mut EvalCtx,
    clone: &ResolvedLocalClone,
    source: ValOrMut,
    span: Location,
) -> Result<Value, RuntimeError> {
    let dispatch = clone_value_method_dispatch(clone)
        .expect("trivial copy should be handled without Value::clone dispatch");
    call_value_clone_with(ctx, source, span, |ctx, arguments| {
        call_resolved_value_method(ctx, dispatch, VALUE_CLONE_METHOD_INDEX, arguments, span)
    })
}

pub(crate) fn call_value_drop_for_temp(
    ctx: &mut EvalCtx,
    dictionary: impl Into<DictArg>,
    target: ValOrMut,
    span: Location,
) -> EvalControlFlowResult {
    let dictionary = dictionary.into();
    let (target_place, temp_index) = match target {
        ValOrMut::Mut(place) => (place, None),
        ValOrMut::Ref(_) => panic!("cannot drop shared reference storage"),
        ValOrMut::Dictionary(_) => panic!("cannot drop trait dictionary metadata as a Value"),
        ValOrMut::Val(value) => {
            let target_index = ctx.environment.len();
            ctx.environment.push(ValOrMut::Val(value));
            let place = Place {
                target: target_index,
                path: Vec::new(),
            };
            (place, Some(target_index))
        }
    };
    let result = discard_call_result(dictionary.call_method(
        ctx,
        TraitDictionaryEntryIndex::from_index(VALUE_DROP_METHOD_INDEX.as_index()),
        vec![ValOrMut::Mut(target_place.clone())],
        span,
    ));
    if result.is_ok() {
        discard_value_storage_at_place(ctx, &target_place, span)?;
    }
    if let Some(target_index) = temp_index {
        let value = ctx.pop_environment_entry().unwrap();
        debug_assert_eq!(target_index, ctx.environment.len());
        if result.is_ok() {
            debug_assert!(matches!(value, ValOrMut::Val(Value::Uninit)));
        } else {
            value.discard_storage();
        }
    }
    result?;
    cont(Value::unit())
}

fn discard_value_storage_at_place(
    ctx: &mut EvalCtx,
    place: &Place,
    span: Location,
) -> Result<(), RuntimeError> {
    let target = place
        .target_mut(ctx)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    let value = mem::replace(target, Value::uninit());
    value.discard_storage();
    Ok(())
}

fn replace_value_storage_at_place(
    ctx: &mut EvalCtx,
    place: &Place,
    value: Value,
    span: Location,
) -> Result<(), RuntimeError> {
    let target = match place.target_mut(ctx) {
        Ok(target) => target,
        Err(err) => {
            value.discard_storage();
            return Err(RuntimeError::new(err, Some(span)));
        }
    };
    let old_value = mem::replace(target, value);
    old_value.discard_storage();
    Ok(())
}

fn place_contains_uninit(
    ctx: &EvalCtx,
    place: &Place,
    span: Location,
) -> Result<bool, RuntimeError> {
    let target = place
        .target_ref_allow_uninit(ctx)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    Ok(matches!(target, Value::Uninit))
}

fn local_environment_index(ctx: &EvalCtx, locals: &[LocalDecl], id: LocalDeclId) -> usize {
    ctx.frame_base + locals[id.as_index()].slot.as_index()
}

fn local_place(ctx: &EvalCtx, locals: &[LocalDecl], id: LocalDeclId) -> Place {
    Place {
        target: local_environment_index(ctx, locals, id),
        path: Vec::new(),
    }
}

#[inline(never)]
fn eval_clone_closure_env(
    arena: &ENodeArena,
    node: &hir::CloneClosureEnv<Elaborated>,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let owned_source;
    let (function, hidden_args, closure_env_ptr, closure_env_len, closure_env_value_dictionary) = {
        let source = if let Some(place) =
            eval_or_return!(try_eval_node_as_place(arena, node.source, ctx, locals))
        {
            place
                .target_ref(ctx)
                .map_err(|err| RuntimeError::new(err, Some(span)))?
                .as_function()
                .unwrap()
        } else {
            owned_source = eval_or_return!(eval_node_with_ctx(arena, node.source, ctx, locals));
            owned_source.as_function().unwrap()
        };

        (
            source.function,
            source.hidden_args.clone(),
            &source.closure_env as *const Value,
            source.closure_env_len,
            source.closure_env_value_dictionary,
        )
    };
    let closure_env = if let Some(dictionary) = closure_env_value_dictionary {
        call_value_clone_for_temp(ctx, dictionary, ValOrMut::Ref(closure_env_ptr), span)?
    } else {
        Value::unit()
    };
    let target_function = FunctionValue {
        function,
        hidden_args,
        closure_env,
        closure_env_len,
        closure_env_value_dictionary,
    };
    cont(Value::function_value(target_function))
}

#[inline(never)]
fn eval_drop_closure_env(
    arena: &ENodeArena,
    node: &hir::DropClosureEnv<Elaborated>,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let target = eval_or_return!(eval_node_as_place(arena, node.target, ctx, locals));
    let captured_env = {
        let target = target
            .target_mut(ctx)
            .map_err(|err| RuntimeError::new(err, Some(span)))?;
        let function = target.as_function_mut().unwrap();
        let dictionary = function.closure_env_value_dictionary;
        dictionary.map(|dictionary| {
            function.closure_env_len = 0;
            function.closure_env_value_dictionary = None;
            (
                dictionary,
                mem::replace(&mut function.closure_env, Value::uninit()),
            )
        })
    };
    let Some((dictionary, captures)) = captured_env else {
        return cont(Value::unit());
    };
    call_value_drop_for_temp(ctx, dictionary, ValOrMut::Val(captures), span)
}

#[inline(never)]
fn eval_clone_value(
    arena: &ENodeArena,
    node: &hir::CloneValue<Elaborated>,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let clone = resolved_local_clone(&node.clone);

    if let ResolvedLocalClone::TrivialCopy = clone {
        let layout = trivial_copy_layout(ctx, arena[node.source].ty, span);
        let temp_start = ctx.environment.len();
        let place = eval_or_return!(eval_node_as_place(arena, node.source, ctx, locals));
        let result = copy_trivial_copy_value_from_place_layout(&place, layout, ctx, span);
        ctx.truncate_environment_storage(temp_start);
        return cont(result?);
    }

    let temp_start = ctx.environment.len();
    let source = match eval_or_return!(try_eval_node_as_place(arena, node.source, ctx, locals)) {
        Some(place) => {
            place
                .target_ref(ctx)
                .map_err(|err| RuntimeError::new(err, Some(arena[node.source].span)))?;
            ValOrMut::Mut(place)
        }
        None => ValOrMut::Val(eval_or_return!(eval_node_with_ctx(
            arena,
            node.source,
            ctx,
            locals
        ))),
    };
    match call_value_clone_dispatch_for_temp(ctx, &clone, source, span) {
        Ok(value) => cont(value),
        Err(err) => {
            ctx.truncate_environment_storage(temp_start);
            Err(err)
        }
    }
}

#[inline(never)]
fn eval_apply(
    arena: &ENodeArena,
    app: &hir::Application<Elaborated>,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    // Evaluate left-to-right: function first, then arguments (matches Rust semantics).
    let owned_function_value;
    let function_value = if let Some(place) =
        eval_or_return!(try_eval_node_as_place(arena, app.function, ctx, locals))
    {
        let function_value = place
            .target_ref(ctx)
            .map_err(|err| RuntimeError::new(err, Some(span)))?
            .as_function()
            .unwrap();
        function_value.as_ref() as *const FunctionValue
    } else {
        owned_function_value =
            eval_or_return!(eval_node_with_ctx(arena, app.function, ctx, locals));
        owned_function_value.as_function().unwrap().as_ref() as *const FunctionValue
    };
    // SAFETY: the pointer either targets `owned_function_value`, kept alive in
    // this stack frame, or environment storage that the borrow checker prevents
    // from being mutably aliased by the call arguments.
    let function_value = unsafe { &*function_value };
    let args_ty = ctx.function_value_visible_argument_types(function_value);
    let temp_start = ctx.environment.len();
    let mut arguments = eval_or_return!(eval_args(arena, &app.arguments, &args_ty, ctx, locals));
    let result = ctx.call_function_value(function_value, arguments.take_arguments(), span);
    finish_call(ctx, temp_start, result)
}

#[inline(never)]
fn eval_static_apply(
    arena: &ENodeArena,
    app: &hir::StaticApplication<Elaborated>,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    eval_static_apply_with(arena, app, span, ctx, locals, eval_args)
}

fn eval_addressor_place_static_apply(
    arena: &ENodeArena,
    app: &hir::StaticApplication<Elaborated>,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    eval_static_apply_with(arena, app, span, ctx, locals, eval_addressor_place_args)
}

/// Strategy for evaluating a static call's visible arguments into a [`PreparedCallArgs`].
type EvalArgsFn = fn(
    &ENodeArena,
    &[CallArgument<Elaborated>],
    &[FnArgType],
    &mut EvalCtx,
    &[LocalDecl],
) -> Result<ControlFlow<PreparedCallArgs>, RuntimeError>;

fn eval_static_apply_with(
    arena: &ENodeArena,
    app: &hir::StaticApplication<Elaborated>,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
    eval_args_fn: EvalArgsFn,
) -> EvalControlFlowResult {
    let temp_start = ctx.environment.len();
    let extra_arguments = eval_or_return!(eval_function_hidden_arg_nodes(
        arena,
        &app.extra_arguments,
        ctx,
        locals,
    ));
    let mut arguments = eval_or_return!(eval_args_fn(
        arena,
        &app.arguments,
        &app.ty.fn_ty.args,
        ctx,
        locals
    ));
    let result = ctx.call_resolved_function_with_extra(
        app.function,
        extra_arguments,
        arguments.take_arguments(),
        span,
    );
    finish_call(ctx, temp_start, result)
}

struct PreparedCallArgs {
    arguments: Vec<ValOrMut>,
}

impl PreparedCallArgs {
    fn new(arguments: Vec<ValOrMut>) -> Self {
        Self { arguments }
    }

    fn take_arguments(&mut self) -> Vec<ValOrMut> {
        std::mem::take(&mut self.arguments)
    }
}

/// Shared post-call cleanup: reclaim argument storage, then yield the call result.
fn finish_call(
    ctx: &mut EvalCtx,
    temp_start: usize,
    result: EvalControlFlowResult,
) -> EvalControlFlowResult {
    ctx.truncate_environment_storage(temp_start);
    result
}

fn eval_addressor_place_args(
    arena: &ENodeArena,
    args: &[CallArgument<Elaborated>],
    args_ty: &[FnArgType],
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<PreparedCallArgs>, RuntimeError> {
    assert_eq!(args.len(), args_ty.len());
    let results = eval_or_return!(eval_sequence(
        args.iter().zip(args_ty),
        args.len(),
        ValOrMut::discard_storage,
        |(arg, ty)| eval_call_arg(arena, arg.value, ty, arg.passing, ctx, locals),
    ));
    Ok(ControlFlow::Continue(PreparedCallArgs::new(results)))
}

fn value_into_addressor_place(value: Value) -> Place {
    value
        .into_primitive_ty::<PlaceResult>()
        .expect("addressor-place function should return internal PlaceResult")
        .into_place()
}

fn control_flow_into_addressor_place(result: ControlFlow<Value>) -> ControlFlow<Place> {
    match result {
        ControlFlow::Continue(value) => ControlFlow::Continue(value_into_addressor_place(value)),
        ControlFlow::Transfer(transfer) => ControlFlow::Transfer(transfer),
    }
}

#[inline(never)]
fn eval_store_local(
    arena: &ENodeArena,
    node: &hir::StoreLocal<Elaborated>,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let local = &locals[node.id.as_index()];
    ctx.check_stack_limit(ctx.environment.len(), Some(span))?;
    let target_index = local_environment_index(ctx, locals, node.id);
    ctx.check_stack_limit(target_index, Some(span))?;
    if let Some(clone) = &local.clone {
        ctx.ensure_environment_slot(target_index);
        let clone = resolved_local_clone(clone);
        if let ResolvedLocalClone::TrivialCopy = clone {
            let value =
                match eval_or_return!(try_eval_node_as_place(arena, node.value, ctx, locals)) {
                    Some(place) => {
                        let layout = trivial_copy_layout(ctx, local.ty, span);
                        copy_trivial_copy_value_from_place_layout(&place, layout, ctx, span)?
                    }
                    None => eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals)),
                };
            ctx.environment[target_index] = ValOrMut::Val(value);
            return cont(Value::unit());
        }
        let source = match eval_or_return!(try_eval_node_as_place(arena, node.value, ctx, locals)) {
            Some(place) => {
                place
                    .target_ref(ctx)
                    .map_err(|err| RuntimeError::new(err, Some(arena[node.value].span)))?;
                ValOrMut::Mut(place)
            }
            None => ValOrMut::Val(eval_or_return!(eval_node_with_ctx(
                arena, node.value, ctx, locals
            ))),
        };
        let arguments = vec![source];
        let dispatch = clone_value_method_dispatch(&clone).expect("trivial copy handled above");
        let value =
            call_resolved_value_method(ctx, dispatch, VALUE_CLONE_METHOD_INDEX, arguments, span)?
                .into_value();
        ctx.environment[target_index] = ValOrMut::Val(value);
    } else if !local.owns_storage() {
        let entry = match eval_or_return!(try_eval_node_as_place(arena, node.value, ctx, locals)) {
            Some(place) => {
                if let Some(dictionary) = try_dictionary_from_place(&place, ctx) {
                    ValOrMut::Dictionary(dictionary)
                } else if let Some(value) =
                    try_copy_trivial_copy_value_from_place(&place, local.ty, ctx, span)?
                {
                    ValOrMut::Val(value)
                } else {
                    ValOrMut::Mut(place)
                }
            }
            None if local.ty == Type::never() => {
                eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals));
                panic!("never-typed local initializer returned normally");
            }
            None if is_dictionary_metadata_node(arena, node.value) => {
                let dictionary =
                    eval_or_return!(eval_dictionary_metadata_node(arena, node.value, ctx));
                ValOrMut::Dictionary(dictionary)
            }
            None if is_function_metadata_node(arena, node.value) => {
                let value = eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals));
                ValOrMut::Val(value)
            }
            None => {
                panic!(
                    "Cannot bind non-owning local '{}' of type {:?} to non-place node: {:?}",
                    local.name.0, local.ty, arena[node.value].kind
                );
            }
        };
        ctx.set_environment_entry(target_index, entry);
    } else {
        let entry = if is_dictionary_metadata_node(arena, node.value) {
            let dictionary = eval_or_return!(eval_dictionary_metadata_node(arena, node.value, ctx));
            ValOrMut::Dictionary(dictionary)
        } else {
            let value = eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals));
            ValOrMut::Val(value)
        };
        ctx.set_environment_entry(target_index, entry);
    }
    cont(Value::unit())
}

#[inline(never)]
fn take_owned_local_value(
    id: LocalDeclId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let index = local_environment_index(ctx, locals, id);
    match mem::replace(&mut ctx.environment[index], ValOrMut::Val(Value::uninit())) {
        ValOrMut::Val(value) => cont(value),
        ValOrMut::Dictionary(_) => panic!("cannot move out of a trait dictionary metadata local"),
        ValOrMut::Ref(_) => panic!("cannot move out of shared reference storage"),
        ValOrMut::Mut(_) => panic!("cannot move out of a mutable reference local"),
    }
}

#[inline(never)]
fn eval_take_local_value(
    node: &hir::TakeLocalValue<hir::Elaborated>,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    match node.mode {
        ResolvedTakeLocalValueMode::MoveOwned => take_owned_local_value(node.id, ctx, locals),
        ResolvedTakeLocalValueMode::CloneBorrowed(ResolvedLocalClone::TrivialCopy) => {
            let local = &locals[node.id.as_index()];
            let layout = trivial_copy_layout(ctx, local.ty, span);
            let place = local_place(ctx, locals, node.id);
            cont(copy_trivial_copy_value_from_place_layout(
                &place, layout, ctx, span,
            )?)
        }
        ResolvedTakeLocalValueMode::CloneBorrowed(clone) => {
            let place = local_place(ctx, locals, node.id);
            place
                .target_ref(ctx)
                .map_err(|err| RuntimeError::new(err, Some(span)))?;
            let value =
                call_value_clone_dispatch_for_temp(ctx, &clone, ValOrMut::Mut(place), span)?;
            cont(value)
        }
    }
}

fn copy_trivial_copy_native_value_typed<T: TrivialCopy + NativeValue>(
    value: &Value,
) -> Option<Value> {
    value
        .as_primitive_ty::<T>()
        .map(|value| Value::native(*value))
}

/// Temporary boxed-interpreter copy for native values known to implement `TrivialCopy`.
///
/// This is not the language contract for `TrivialCopy`: future typed/linear
/// storage should lower `ResolvedLocalClone::TrivialCopy` to a layout-driven memcpy instead.
fn copy_trivial_copy_native_value(value: &Value, ty: Type) -> Option<Value> {
    let ty_data = ty.data();
    if let TypeKind::Native(native) = &*ty_data
        && native.arguments.is_empty()
    {
        if native.bare_ty == bare_native_type::<()>() {
            return copy_trivial_copy_native_value_typed::<()>(value);
        }
        if native.bare_ty == bare_native_type::<bool>() {
            return copy_trivial_copy_native_value_typed::<bool>(value);
        }
        if native.bare_ty == bare_native_type::<isize>() {
            return copy_trivial_copy_native_value_typed::<isize>(value);
        }
    }
    None
}

fn copy_trivial_copy_native_value_with_layout(
    value: &Value,
    layout: ResolvedValueLayout,
) -> Option<Value> {
    if layout == ResolvedValueLayout::native::<()>() {
        return copy_trivial_copy_native_value_typed::<()>(value);
    }
    if layout == ResolvedValueLayout::native::<bool>() {
        return copy_trivial_copy_native_value_typed::<bool>(value);
    }
    if layout == ResolvedValueLayout::native::<isize>() {
        return copy_trivial_copy_native_value_typed::<isize>(value);
    }
    None
}

fn copy_trivial_copy_value_from_place(
    place: &Place,
    ty: Type,
    ctx: &EvalCtx,
    span: Location,
) -> Result<Value, RuntimeError> {
    // Temporary companion to `copy_trivial_copy_native_value` for the boxed-value
    // interpreter. This should collapse into the backend implementation of HIR
    // `ResolvedLocalClone::TrivialCopy` once values are stored in copyable slots.
    try_copy_trivial_copy_value_from_place(place, ty, ctx, span)?.ok_or_else(|| {
        panic!(
            "attempted to materialize non-TrivialCopy local value without Value::clone: type {:?}, place {:?}",
            ty, place
        );
    })
}

fn copy_trivial_copy_value_from_place_layout(
    place: &Place,
    layout: ResolvedValueLayout,
    ctx: &EvalCtx,
    span: Location,
) -> Result<Value, RuntimeError> {
    let value = place
        .target_ref(ctx)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    copy_trivial_copy_native_value_with_layout(value, layout).ok_or_else(|| {
        panic!(
            "attempted to materialize non-native TrivialCopy local value with layout {:?}, place {:?}",
            layout, place
        );
    })
}

fn try_copy_trivial_copy_value_from_place(
    place: &Place,
    ty: Type,
    ctx: &EvalCtx,
    span: Location,
) -> Result<Option<Value>, RuntimeError> {
    // Temporary boxed-value interpreter bridge; see `copy_trivial_copy_native_value`.
    let value = place
        .target_ref(ctx)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    Ok(copy_trivial_copy_native_value(value, ty))
}

#[inline(never)]
fn eval_load_local(
    arena: &ENodeArena,
    node_id: ENodeId,
    node: &hir::LoadLocal,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let place = local_place(ctx, locals, node.id);
    cont(copy_trivial_copy_value_from_place(
        &place,
        locals[node.id.as_index()].ty,
        ctx,
        arena[node_id].span,
    )?)
}

#[inline(never)]
fn eval_return(
    arena: &ENodeArena,
    node: ENodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    if ctx.returns_place {
        let place = match eval_node_as_place(arena, node, ctx, locals)? {
            ControlFlow::Continue(place) => place,
            transfer => return Ok(transfer.map_continue(unreachable_continue)),
        };
        let place = place.resolved(ctx);
        return ret(Value::native(PlaceResult::new(place)));
    }
    ret(eval_or_return!(eval_node_with_ctx(
        arena, node, ctx, locals
    )))
}

#[inline(never)]
fn eval_yield(
    arena: &ENodeArena,
    node: ENodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let place = match eval_node_as_place(arena, node, ctx, locals)? {
        ControlFlow::Continue(place) => place.resolved(ctx),
        transfer => return Ok(transfer.map_continue(unreachable_continue)),
    };
    Ok(ControlFlow::Transfer(ControlTransfer::Yield(place)))
}

#[inline(never)]
fn eval_with_yielded(
    arena: &ENodeArena,
    node: &hir::WithYielded<Elaborated>,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    ctx.reserve_current_frame_slots(locals);
    let temp_start = ctx.environment.len();
    let (suspension, yielded_place) = eval_or_return!(eval_accessor_until_yield(
        arena,
        node.accessor,
        span,
        ctx,
        locals
    ));

    let binding_index = local_environment_index(ctx, locals, node.binding);
    ctx.set_environment_entry(binding_index, ValOrMut::Mut(yielded_place));
    let body_result = eval_node_with_ctx(arena, node.body, ctx, locals);
    ctx.set_environment_entry(binding_index, ValOrMut::Val(Value::uninit()));

    let epilogue_result = ctx.resume_suspended_accessor_epilogue(suspension, span);
    ctx.truncate_environment_storage(temp_start);
    combine_with_yielded_body_and_epilogue(body_result, epilogue_result)
}

fn eval_accessor_until_yield(
    arena: &ENodeArena,
    accessor: ENodeId,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<(SuspendedAccessor, Place)>, RuntimeError> {
    let NodeKind::StaticApply(app) = &arena[accessor].kind else {
        panic!("WithYielded accessor must be a static accessor call");
    };
    let temp_start = ctx.environment.len();
    let extra_arguments =
        match eval_function_hidden_arg_nodes(arena, &app.extra_arguments, ctx, locals)? {
            ControlFlow::Continue(arguments) => arguments,
            ControlFlow::Transfer(transfer) => {
                ctx.truncate_environment_storage(temp_start);
                return Ok(ControlFlow::Transfer(transfer));
            }
        };
    let mut arguments = match eval_args(arena, &app.arguments, &app.ty.fn_ty.args, ctx, locals)? {
        ControlFlow::Continue(arguments) => arguments,
        ControlFlow::Transfer(transfer) => {
            ctx.truncate_environment_storage(temp_start);
            return Ok(ControlFlow::Transfer(transfer));
        }
    };
    match ctx.call_resolved_accessor_until_yield_with_extra(
        app.function,
        extra_arguments,
        arguments.take_arguments(),
        span,
    ) {
        Ok(suspension) => Ok(ControlFlow::Continue(suspension)),
        Err(err) => {
            ctx.truncate_environment_storage(temp_start);
            Err(err)
        }
    }
}

fn combine_with_yielded_body_and_epilogue(
    body_result: EvalControlFlowResult,
    epilogue_result: EvalControlFlowResult,
) -> EvalControlFlowResult {
    match (body_result, epilogue_result) {
        (Ok(body), Ok(ControlFlow::Continue(value))) => {
            value.discard_storage();
            Ok(body)
        }
        (Ok(body), Ok(epilogue @ ControlFlow::Transfer(_))) => {
            discard_control_flow_value(epilogue);
            Ok(body)
        }
        (Ok(body), Err(err)) => {
            discard_control_flow_value(body);
            Err(err)
        }
        (Err(err), Ok(ControlFlow::Continue(value))) => {
            value.discard_storage();
            Err(err)
        }
        (Err(err), Ok(epilogue @ ControlFlow::Transfer(_))) => {
            discard_control_flow_value(epilogue);
            Err(err)
        }
        (Err(_), Err(epilogue_err)) => Err(epilogue_err),
    }
}

#[inline(never)]
fn eval_with_place(
    arena: &ENodeArena,
    node: &hir::WithPlace<Elaborated>,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    eval_with_bound_place(arena, node, ctx, locals, |ctx| {
        eval_node_with_ctx(arena, node.body, ctx, locals)
    })
}

fn eval_with_bound_place<T>(
    arena: &ENodeArena,
    node: &hir::WithPlace<Elaborated>,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
    body: impl FnOnce(&mut EvalCtx) -> Result<ControlFlow<T>, RuntimeError>,
) -> Result<ControlFlow<T>, RuntimeError> {
    ctx.reserve_current_frame_slots(locals);
    let temp_start = ctx.environment.len();
    let place = match try_eval_node_as_place(arena, node.place, ctx, locals)? {
        ControlFlow::Continue(Some(place)) => place,
        ControlFlow::Continue(None) => {
            panic!("WithPlace input must evaluate to a place");
        }
        ControlFlow::Transfer(transfer) => return Ok(ControlFlow::Transfer(transfer)),
    };

    let binding_index = local_environment_index(ctx, locals, node.binding);
    ctx.set_environment_entry(binding_index, ValOrMut::Mut(place));
    let body_result = body(ctx);
    ctx.set_environment_entry(binding_index, ValOrMut::Val(Value::uninit()));
    ctx.truncate_environment_storage(temp_start);
    body_result
}

#[inline(never)]
fn try_eval_with_place_as_place(
    arena: &ENodeArena,
    node: &hir::WithPlace<Elaborated>,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<Option<Place>>, RuntimeError> {
    let body_result =
        eval_with_bound_place(
            arena,
            node,
            ctx,
            locals,
            |ctx| match try_eval_node_as_place(arena, node.body, ctx, locals)? {
                ControlFlow::Continue(place) => Ok(ControlFlow::Continue(
                    place.map(|place| place.resolved(ctx)),
                )),
                ControlFlow::Transfer(transfer) => Ok(ControlFlow::Transfer(transfer)),
            },
        );
    if let Ok(ControlFlow::Continue(None)) = body_result {
        panic!("WithPlace body must evaluate to a place");
    }
    body_result
}

fn discard_control_flow_value(flow: ControlFlow<Value>) {
    match flow {
        ControlFlow::Continue(value) => value.discard_storage(),
        ControlFlow::Transfer(transfer) => {
            if let Some(value) = transfer.into_value() {
                value.discard_storage();
            }
        }
    }
}

fn eval_epilogue_after_yield(
    arena: &ENodeArena,
    node_id: ENodeId,
    yield_node_id: ENodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    if node_id == yield_node_id {
        return cont(Value::unit());
    }
    match &arena[node_id].kind {
        NodeKind::Block(block) => {
            eval_block_epilogue_after_yield(arena, block, yield_node_id, ctx, locals)
        }
        _ => panic!("yield epilogue replay only supports block-structured accessor bodies"),
    }
}

fn eval_block_epilogue_after_yield(
    arena: &ENodeArena,
    block: &hir::Block<Elaborated>,
    yield_node_id: ENodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let Some(yield_index) = block
        .body
        .iter()
        .position(|node| node_contains_yield(arena, *node, yield_node_id))
    else {
        panic!("yield node is not contained in accessor body");
    };

    let yield_container = block.body[yield_index];
    if yield_container != yield_node_id {
        match eval_epilogue_after_yield(arena, yield_container, yield_node_id, ctx, locals) {
            Ok(ControlFlow::Continue(value)) => value.discard_storage(),
            Ok(transfer) => {
                drop_cleanup_locals(ctx, locals, &block.cleanup, arena[yield_container].span)?;
                return Ok(transfer);
            }
            Err(err) => {
                drop_cleanup_locals(ctx, locals, &block.cleanup, arena[yield_container].span)?;
                return Err(err);
            }
        }
    }

    let mut last_value: Option<Value> = None;
    for node in block.body.iter().skip(yield_index + 1) {
        match eval_node_with_ctx(arena, *node, ctx, locals) {
            Err(err) => {
                if let Some(value) = last_value.take() {
                    value.discard_storage();
                }
                drop_cleanup_locals(ctx, locals, &block.cleanup, arena[*node].span)?;
                return Err(err);
            }
            Ok(ControlFlow::Continue(value)) => {
                if let Some(old_value) = last_value.replace(value) {
                    old_value.discard_storage();
                }
            }
            Ok(transfer) => {
                if let Some(value) = last_value.take() {
                    value.discard_storage();
                }
                drop_cleanup_locals(ctx, locals, &block.cleanup, arena[*node].span)?;
                return Ok(transfer);
            }
        }
    }

    let span = block
        .body
        .last()
        .map(|node| arena[*node].span)
        .unwrap_or_else(Location::new_synthesized);
    drop_cleanup_locals(ctx, locals, &block.cleanup, span)?;
    cont(last_value.unwrap_or_else(Value::unit))
}

fn node_contains_yield(arena: &ENodeArena, node_id: ENodeId, yield_node_id: ENodeId) -> bool {
    if node_id == yield_node_id {
        return true;
    }
    match &arena[node_id].kind {
        NodeKind::Block(block) => block
            .body
            .iter()
            .any(|child| node_contains_yield(arena, *child, yield_node_id)),
        _ => false,
    }
}

#[inline(never)]
fn eval_block(
    arena: &ENodeArena,
    block: &hir::Block<Elaborated>,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    if !block.cleanup.is_empty() {
        return eval_block_with_cleanup(arena, &block.body, ctx, locals, &block.cleanup);
    }
    let nodes = &block.body;
    let env_size = ctx.environment.len();
    let mut last_value: Option<Value> = None;
    for node in nodes.iter() {
        match eval_node_with_ctx(arena, *node, ctx, locals) {
            Err(err) => {
                if let Some(value) = last_value.take() {
                    value.discard_storage();
                }
                ctx.assert_no_owned_local_leaks_before_truncate(
                    locals,
                    env_size,
                    arena[*node].span,
                );
                ctx.truncate_environment_storage(env_size);
                return Err(err);
            }
            Ok(ControlFlow::Continue(val)) => {
                if let Some(old_value) = last_value.replace(val) {
                    old_value.discard_storage();
                }
            }
            Ok(transfer) => {
                if let Some(value) = last_value.take() {
                    value.discard_storage();
                }
                if matches!(transfer, ControlFlow::Transfer(ControlTransfer::Yield(_))) {
                    return Ok(transfer);
                }
                ctx.assert_no_owned_local_leaks_before_truncate(
                    locals,
                    env_size,
                    arena[*node].span,
                );
                ctx.truncate_environment_storage(env_size);
                return Ok(transfer);
            }
        }
    }
    let span = nodes
        .last()
        .map(|node| arena[*node].span)
        .unwrap_or_else(Location::new_synthesized);
    ctx.assert_no_owned_local_leaks_before_truncate(locals, env_size, span);
    ctx.truncate_environment_storage(env_size);
    cont(last_value.unwrap_or_else(Value::unit))
}

fn drop_cleanup_locals(
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
    drops: &[LocalDeclId],
    span: Location,
) -> Result<(), RuntimeError> {
    for id in drops.iter().rev() {
        let local = &locals[id.as_index()];
        let Some(drop) = local.local_drop() else {
            continue;
        };
        let target_index = local_environment_index(ctx, locals, *id);
        if target_index >= ctx.environment.len() {
            continue;
        }
        let target = local_place(ctx, locals, *id);
        if place_contains_uninit(ctx, &target, span)? {
            continue;
        }
        call_local_drop_dispatch(ctx, resolved_local_drop(drop), target.clone(), span)?;
        discard_value_storage_at_place(ctx, &target, span)?;
    }
    Ok(())
}

fn eval_block_with_cleanup(
    arena: &ENodeArena,
    nodes: &[ENodeId],
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
    cleanup_drops: &[LocalDeclId],
) -> EvalControlFlowResult {
    let env_size = ctx.environment.len();
    let mut last_value: Option<Value> = None;
    for node in nodes.iter() {
        match eval_node_with_ctx(arena, *node, ctx, locals) {
            Err(err) => {
                if let Some(value) = last_value.take() {
                    value.discard_storage();
                }
                let cleanup = drop_cleanup_locals(ctx, locals, cleanup_drops, arena[*node].span);
                if let Err(err) = cleanup {
                    ctx.truncate_environment_storage(env_size);
                    return Err(err);
                }
                ctx.assert_no_owned_local_leaks_before_truncate(
                    locals,
                    env_size,
                    arena[*node].span,
                );
                ctx.truncate_environment_storage(env_size);
                return Err(err);
            }
            Ok(ControlFlow::Continue(val)) => {
                if let Some(old_value) = last_value.replace(val) {
                    old_value.discard_storage();
                }
            }
            Ok(transfer) => {
                if let Some(value) = last_value.take() {
                    value.discard_storage();
                }
                if matches!(transfer, ControlFlow::Transfer(ControlTransfer::Yield(_))) {
                    return Ok(transfer);
                }
                let cleanup = drop_cleanup_locals(ctx, locals, cleanup_drops, arena[*node].span);
                if let Err(err) = cleanup {
                    ctx.truncate_environment_storage(env_size);
                    return Err(err);
                }
                ctx.assert_no_owned_local_leaks_before_truncate(
                    locals,
                    env_size,
                    arena[*node].span,
                );
                ctx.truncate_environment_storage(env_size);
                return Ok(transfer);
            }
        }
    }
    let span = nodes
        .last()
        .map(|node| arena[*node].span)
        .unwrap_or_else(Location::new_synthesized);
    let cleanup = drop_cleanup_locals(ctx, locals, cleanup_drops, span);
    if let Err(err) = cleanup {
        ctx.truncate_environment_storage(env_size);
        return Err(err);
    }
    ctx.assert_no_owned_local_leaks_before_truncate(locals, env_size, span);
    ctx.truncate_environment_storage(env_size);
    cont(last_value.unwrap_or_else(Value::unit))
}

#[inline(never)]
fn eval_assign(
    arena: &ENodeArena,
    node_id: ENodeId,
    assignment: &hir::Assignment<Elaborated>,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    // Evaluate left-to-right: place first, then value (matches Rust semantics).
    let place = eval_or_return!(eval_node_as_place(arena, assignment.place, ctx, locals));
    let value = eval_or_return!(eval_node_with_ctx(arena, assignment.value, ctx, locals));
    let span = arena[node_id].span;
    if let Some(drop) = &assignment.drop
        && !place_contains_uninit(ctx, &place, span)?
        && let Err(err) =
            call_local_drop_dispatch(ctx, resolved_local_drop(drop), place.clone(), span)
    {
        value.discard_storage();
        return Err(err);
    }
    replace_value_storage_at_place(ctx, &place, value, span)?;
    cont(Value::unit())
}

#[inline(never)]
fn eval_tuple(
    arena: &ENodeArena,
    nodes: &[ENodeId],
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    // Note: record values are stored as tuples.
    let values = eval_or_return!(eval_nodes(arena, nodes, ctx, locals));
    cont(Value::tuple(values))
}

#[inline(never)]
fn eval_project(
    arena: &ENodeArena,
    node_id: ENodeId,
    data: ENodeId,
    index: ProjectionIndex,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let index = index.as_index();
    if let Some(mut place) = eval_or_return!(try_eval_node_as_place(arena, data, ctx, locals)) {
        place.path.push(index as isize);
        if place_resolution_depends_on_addressor_place(arena, data) {
            if let Some(value) = try_copy_trivial_copy_value_from_place(
                &place,
                arena[node_id].ty,
                ctx,
                arena[node_id].span,
            )? {
                return cont(value);
            }
        } else {
            return cont(copy_trivial_copy_value_from_place(
                &place,
                arena[node_id].ty,
                ctx,
                arena[node_id].span,
            )?);
        }
    }
    let value = eval_or_return!(eval_node_with_ctx(arena, data, ctx, locals));
    cont(
        value
            .into_projected_value(index)
            .unwrap_or_else(|| panic!("Cannot project from a non-compound value")),
    )
}

#[inline(never)]
fn eval_project_at(
    arena: &ENodeArena,
    node_id: ENodeId,
    data: ENodeId,
    index: ExtraParameterId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    if let Some(mut place) = eval_or_return!(try_eval_node_as_place(arena, data, ctx, locals)) {
        let index = field_index_from_extra_parameter(ctx, index);
        place.path.push(index);
        if place_resolution_depends_on_addressor_place(arena, data) {
            if let Some(value) = try_copy_trivial_copy_value_from_place(
                &place,
                arena[node_id].ty,
                ctx,
                arena[node_id].span,
            )? {
                return cont(value);
            }
        } else {
            return cont(copy_trivial_copy_value_from_place(
                &place,
                arena[node_id].ty,
                ctx,
                arena[node_id].span,
            )?);
        }
    }
    let value = eval_or_return!(eval_node_with_ctx(arena, data, ctx, locals));
    let index = field_index_from_extra_parameter(ctx, index);
    cont(
        value
            .into_tuple_element(index as usize)
            .unwrap_or_else(|| panic!("Cannot access field from a non-compound value")),
    )
}

fn place_resolution_depends_on_addressor_place(arena: &ENodeArena, node_id: ENodeId) -> bool {
    match &arena[node_id].kind {
        NodeKind::Apply(app) => app.ty.returns_place(),
        NodeKind::StaticApply(app) => app.ty.returns_place(),
        NodeKind::CallDictionaryMethod(call) => call.ty.returns_place(),
        NodeKind::Project(node) => place_resolution_depends_on_addressor_place(arena, node.value),
        NodeKind::ProjectAt(node) => place_resolution_depends_on_addressor_place(arena, node.value),
        NodeKind::WithPlace(node) => place_resolution_depends_on_addressor_place(arena, node.place),
        NodeKind::Block(block) => block
            .body
            .last()
            .is_some_and(|node| place_resolution_depends_on_addressor_place(arena, *node)),
        _ => false,
    }
}

#[inline(never)]
fn eval_variant(
    arena: &ENodeArena,
    tag: Ustr,
    payload: ENodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let value = eval_or_return!(eval_node_with_ctx(arena, payload, ctx, locals));
    cont(Value::raw_variant(tag, value))
}

#[inline(never)]
fn eval_extract_tag(
    arena: &ENodeArena,
    node: ENodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    if let Some(place) = eval_or_return!(try_eval_node_as_place(arena, node, ctx, locals)) {
        let value = place
            .target_ref(ctx)
            .map_err(|err| RuntimeError::new(err, Some(arena[node].span)))?;
        let variant = value.as_variant().unwrap();
        let tag = variant.tag_as_isize();
        return cont(Value::native(tag));
    }
    let value = eval_or_return!(eval_node_with_ctx(arena, node, ctx, locals));
    let variant = value.into_variant().unwrap();
    cont(Value::native(variant.tag_as_isize()))
}

#[inline(never)]
fn eval_array(
    arena: &ENodeArena,
    nodes: &[ENodeId],
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let values = eval_or_return!(eval_nodes(arena, nodes, ctx, locals));
    cont(array_value_from_vec(values))
}

fn eval_case(
    arena: &ENodeArena,
    case: &hir::Case<Elaborated>,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let value = if let Some(place) =
        eval_or_return!(try_eval_node_as_place(arena, case.value, ctx, locals))
    {
        place
            .target_ref(ctx)
            .map_err(|err| RuntimeError::new(err, Some(arena[case.value].span)))?
            .to_literal_value()
    } else {
        eval_or_return!(eval_node_with_ctx(arena, case.value, ctx, locals)).to_literal_value()
    };
    let value = value.unwrap_or_else(|| {
        panic!(
            "Case evaluated a non-literal scrutinee. This HIR should have been rejected before evaluation."
        )
    });
    for (alternative, node) in &case.alternatives {
        if value == *alternative {
            return eval_node_with_ctx(arena, *node, ctx, locals);
        }
    }
    eval_node_with_ctx(arena, case.default, ctx, locals)
}

#[inline(never)]
fn eval_loop(
    arena: &ENodeArena,
    label: LoopId,
    body: ENodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    loop {
        match eval_node_with_ctx(arena, body, ctx, locals)? {
            ControlFlow::Continue(value) => value.discard_storage(),
            ControlFlow::Transfer(ControlTransfer::Return(value)) => {
                return Ok(ControlFlow::Transfer(ControlTransfer::Return(value)));
            }
            ControlFlow::Transfer(ControlTransfer::Yield(place)) => {
                return Ok(ControlFlow::Transfer(ControlTransfer::Yield(place)));
            }
            ControlFlow::Transfer(ControlTransfer::Break {
                label: break_label,
                value,
            }) if break_label == label => return cont(value),
            ControlFlow::Transfer(ControlTransfer::Break {
                label: break_label,
                value,
            }) => {
                return Ok(ControlFlow::Transfer(ControlTransfer::Break {
                    label: break_label,
                    value,
                }));
            }
            ControlFlow::Transfer(ControlTransfer::Continue {
                label: continue_label,
            }) if continue_label == label => {}
            ControlFlow::Transfer(ControlTransfer::Continue {
                label: continue_label,
            }) => {
                return Ok(ControlFlow::Transfer(ControlTransfer::Continue {
                    label: continue_label,
                }));
            }
        }
    }
}

/// Evaluate a node that must produce a place in the environment.
pub fn eval_node_as_place(
    arena: &ENodeArena,
    node_id: ENodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<Place>, RuntimeError> {
    match eval_or_return!(try_eval_node_as_place(arena, node_id, ctx, locals)) {
        Some(place) => Ok(ControlFlow::Continue(place)),
        None => panic!("Cannot resolve a non-place node: {:?}", arena[node_id].kind),
    }
}

/// Evaluate each item in order, collecting the `Continue` values.
/// On a `Return` or error, `discard` each already-collected value before propagating.
fn eval_sequence<I, T>(
    items: impl IntoIterator<Item = I>,
    capacity: usize,
    discard: impl Fn(T),
    mut eval: impl FnMut(I) -> Result<ControlFlow<T>, RuntimeError>,
) -> Result<ControlFlow<Vec<T>>, RuntimeError> {
    let mut results = Vec::with_capacity(capacity);
    for item in items {
        match eval(item) {
            Ok(ControlFlow::Continue(value)) => results.push(value),
            Ok(transfer) => {
                results.into_iter().for_each(discard);
                return Ok(transfer.map_continue(unreachable_continue));
            }
            Err(err) => {
                results.into_iter().for_each(discard);
                return Err(err);
            }
        }
    }
    Ok(ControlFlow::Continue(results))
}

fn eval_nodes(
    arena: &ENodeArena,
    nodes: &[ENodeId],
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<Vec<Value>>, RuntimeError> {
    eval_sequence(
        nodes.iter().copied(),
        nodes.len(),
        Value::discard_storage,
        |node| eval_node_with_ctx(arena, node, ctx, locals),
    )
}

fn eval_call_arg(
    arena: &ENodeArena,
    arg: ENodeId,
    arg_ty: &FnArgType,
    passing: ResolvedArgPassing,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<ValOrMut>, RuntimeError> {
    match passing {
        ResolvedArgPassing::MutableRef => eval_node_as_place(arena, arg, ctx, locals)
            .map(|result| result.map_continue(ValOrMut::Mut)),
        ResolvedArgPassing::Value(ResolvedValueArgPassing::SharedRef) => {
            match try_eval_node_as_place(arena, arg, ctx, locals) {
                Ok(ControlFlow::Continue(Some(place))) => {
                    Ok(ControlFlow::Continue(ValOrMut::Mut(place)))
                }
                Ok(ControlFlow::Continue(None)) if is_dictionary_metadata_node(arena, arg) => {
                    eval_dictionary_metadata_node(arena, arg, ctx)
                        .map(|result| result.map_continue(ValOrMut::Dictionary))
                }
                Ok(ControlFlow::Continue(None)) => {
                    panic!(
                        "shared-reference call argument should have been materialized as a local"
                    )
                }
                Ok(transfer) => Ok(transfer.map_continue(unreachable_continue)),
                Err(err) => Err(err),
            }
        }
        ResolvedArgPassing::Value(ResolvedValueArgPassing::TrivialCopy)
            if is_dictionary_metadata_node(arena, arg) =>
        {
            eval_dictionary_metadata_node(arena, arg, ctx)
                .map(|result| result.map_continue(ValOrMut::Dictionary))
        }
        ResolvedArgPassing::Value(ResolvedValueArgPassing::TrivialCopy) => {
            let layout = trivial_copy_layout(ctx, arg_ty.ty, arena[arg].span);
            eval_trivial_copy_arg(arena, arg, layout, ctx, locals)
        }
    }
}

fn trivial_copy_layout(ctx: &mut EvalCtx<'_>, ty: Type, span: Location) -> ResolvedValueLayout {
    if let Some(layout) = ctx.trivial_copy_layout_cache.get(&(ctx.module_id, ty)) {
        return *layout;
    }
    let layout = ctx
        .compiler_session()
        .value_layout(ctx.module_id, ty, span)
        .unwrap_or_else(|_| {
            panic!(
                "missing TrivialCopy layout for {} at {}",
                ty.format_with(&ctx.compiler_session().module_env()),
                span.format_with(ctx.compiler_session().source_table())
            )
        });
    ctx.trivial_copy_layout_cache
        .insert((ctx.module_id, ty), layout);
    layout
}

fn eval_args(
    arena: &ENodeArena,
    args: &[CallArgument<Elaborated>],
    args_ty: &[FnArgType],
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<PreparedCallArgs>, RuntimeError> {
    let temp_start = ctx.environment.len();
    let mut results = Vec::with_capacity(args.len());
    assert_eq!(args.len(), args_ty.len());
    for (arg, ty) in args.iter().zip(args_ty) {
        let result = eval_call_arg(arena, arg.value, ty, arg.passing, ctx, locals);
        match result {
            Ok(ControlFlow::Continue(arg)) => results.push(arg),
            Ok(transfer) => {
                for result in results {
                    result.discard_storage();
                }
                ctx.truncate_environment_storage(temp_start);
                return Ok(transfer.map_continue(unreachable_continue));
            }
            Err(err) => {
                for result in results {
                    result.discard_storage();
                }
                ctx.truncate_environment_storage(temp_start);
                return Err(err);
            }
        }
    }
    Ok(ControlFlow::Continue(PreparedCallArgs::new(results)))
}

fn eval_trivial_copy_arg(
    arena: &ENodeArena,
    arg: ENodeId,
    layout: ResolvedValueLayout,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<ValOrMut>, RuntimeError> {
    let temp_start = ctx.environment.len();
    match try_eval_node_as_place(arena, arg, ctx, locals) {
        Ok(ControlFlow::Continue(Some(place))) => {
            let value =
                copy_trivial_copy_value_from_place_layout(&place, layout, ctx, arena[arg].span);
            ctx.truncate_environment_storage(temp_start);
            Ok(ControlFlow::Continue(ValOrMut::Val(value?)))
        }
        Ok(ControlFlow::Continue(None)) => eval_node_with_ctx(arena, arg, ctx, locals)
            .map(|result| result.map_continue(ValOrMut::Val)),
        Ok(transfer) => Ok(transfer.map_continue(unreachable_continue)),
        Err(err) => Err(err),
    }
}

fn is_dictionary_metadata_node(arena: &ENodeArena, node: ENodeId) -> bool {
    matches!(
        arena[node].kind,
        NodeKind::GetDictionary(_) | NodeKind::LoadDictionary(_)
    )
}

fn is_function_metadata_node(arena: &ENodeArena, node: ENodeId) -> bool {
    matches!(
        arena[node].kind,
        NodeKind::GetFunction(_) | NodeKind::GetDictionaryMethod(_)
    )
}

/// Evaluate a node as a place when the HIR shape permits it.
fn try_eval_node_as_place(
    arena: &ENodeArena,
    node_id: ENodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<Option<Place>>, RuntimeError> {
    let node = &arena[node_id];
    use NodeKind::*;
    Ok(ControlFlow::Continue(Some(match &node.kind {
        Project(node) => {
            let Some(mut place) =
                eval_or_return!(try_eval_node_as_place(arena, node.value, ctx, locals))
            else {
                return Ok(ControlFlow::Continue(None));
            };
            place.path.push(node.index.as_index() as isize);
            place
        }
        ProjectAt(node) => {
            let Some(mut place) =
                eval_or_return!(try_eval_node_as_place(arena, node.value, ctx, locals))
            else {
                return Ok(ControlFlow::Continue(None));
            };
            let index = field_index_from_extra_parameter(ctx, node.index);
            place.path.push(index);
            place
        }
        Apply(app) if app.ty.returns_place() => {
            let result = eval_apply(arena, app, node.span, ctx, locals)?;
            return Ok(control_flow_into_addressor_place(result).map_continue(Some));
        }
        StaticApply(app) if app.ty.returns_place() => {
            let result = eval_addressor_place_static_apply(arena, app, node.span, ctx, locals)?;
            return Ok(control_flow_into_addressor_place(result).map_continue(Some));
        }
        CallDictionaryMethod(call) if call.ty.returns_place() => {
            let result =
                eval_addressor_place_call_dictionary_method(arena, call, node.span, ctx, locals)?;
            return Ok(control_flow_into_addressor_place(result).map_continue(Some));
        }
        CloneValue(node)
            if matches!(
                node.clone,
                ResolvedLocalClone::Static(_) | ResolvedLocalClone::Dictionary(_)
            ) =>
        {
            return try_eval_node_as_place(arena, node.source, ctx, locals);
        }
        Block(block) => {
            let place = eval_or_return!(try_eval_nodes_as_place(arena, &block.body, ctx, locals));
            if !block.cleanup.is_empty() {
                // Addressor-place helpers may need temporaries to compute the final place.
                // The returned place must not point into these cleanup locals.
                drop_cleanup_locals(ctx, locals, &block.cleanup, node.span)?;
            }
            return Ok(ControlFlow::Continue(place));
        }
        WithPlace(node) => {
            return try_eval_with_place_as_place(arena, node, ctx, locals);
        }
        LoadLocal(node) => {
            // By using frame_base here, we allow to access parent frames
            // when the Place is used in a child function.
            local_place(ctx, locals, node.id)
        }
        _ => return Ok(ControlFlow::Continue(None)),
    })))
}

fn try_eval_nodes_as_place(
    arena: &ENodeArena,
    nodes: &[ENodeId],
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<Option<Place>>, RuntimeError> {
    let Some(place_index) = nodes
        .iter()
        .rposition(|node| !matches!(arena[*node].kind, NodeKind::StoreLocal(_)))
    else {
        return Ok(ControlFlow::Continue(None));
    };
    if !node_may_resolve_to_place(arena, nodes[place_index]) {
        return Ok(ControlFlow::Continue(None));
    }
    for &node in &nodes[..place_index] {
        eval_or_return!(eval_node_with_ctx(arena, node, ctx, locals));
    }
    try_eval_node_as_place(arena, nodes[place_index], ctx, locals)
}

fn node_may_resolve_to_place(arena: &ENodeArena, node_id: ENodeId) -> bool {
    match &arena[node_id].kind {
        NodeKind::LoadLocal(_) => true,
        NodeKind::Project(node) => node_may_resolve_to_place(arena, node.value),
        NodeKind::ProjectAt(node) => node_may_resolve_to_place(arena, node.value),
        NodeKind::Apply(app) => app.ty.returns_place(),
        NodeKind::StaticApply(app) => app.ty.returns_place(),
        NodeKind::CallDictionaryMethod(call) => call.ty.returns_place(),
        NodeKind::CloneValue(node)
            if matches!(
                node.clone,
                ResolvedLocalClone::Static(_) | ResolvedLocalClone::Dictionary(_)
            ) =>
        {
            node_may_resolve_to_place(arena, node.source)
        }
        NodeKind::WithPlace(node) => node_may_resolve_to_place(arena, node.body),
        NodeKind::Block(block) => nodes_may_resolve_to_place(arena, &block.body),
        _ => false,
    }
}

fn nodes_may_resolve_to_place(arena: &ENodeArena, nodes: &[ENodeId]) -> bool {
    nodes
        .iter()
        .rposition(|node| !matches!(arena[*node].kind, NodeKind::StoreLocal(_)))
        .is_some_and(|place_index| node_may_resolve_to_place(arena, nodes[place_index]))
}

#[cfg(test)]
mod tests {
    use std::{
        fmt,
        sync::atomic::{AtomicUsize, Ordering},
    };

    use crate::{
        CompilerSession, Location,
        compiler::error::RuntimeErrorKind,
        containers::{SVec2, b},
        eval::{
            ControlFlow, ControlTransfer, EvalCtx, RuntimeError,
            combine_with_yielded_body_and_epilogue, cont, eval_args, eval_node, eval_nodes, ret,
        },
        hir::{
            self, CallArgument, ENode, ENodeArena, Elaborated, LoopId, NodeKind,
            function::{
                CallableDefinition, ResolvedArgPassing, ResolvedValueArgPassing, ScriptFunction,
            },
            hir_syn,
            value::{LiteralValue, NativeDisplay, Value},
        },
        module::{
            LocalDecl, LocalDeclId, LocalFunctionId, Module, ModuleFunction, ModuleId, Path,
            PendingLocalDrop, ResolvedLocalDrop, id::Id,
        },
        std::math::{Int, int_type},
        types::{
            effects::EffType,
            mutability::MutType,
            r#type::{CallResultConvention, FnArgType, FnType, Type},
            type_scheme::TypeScheme,
        },
    };
    use ustr::ustr;

    static EVAL_DROP_TRACKED_COUNT: AtomicUsize = AtomicUsize::new(0);

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    struct EvalDropTracked;

    impl Drop for EvalDropTracked {
        fn drop(&mut self) {
            EVAL_DROP_TRACKED_COUNT.fetch_add(1, Ordering::Relaxed);
        }
    }

    impl NativeDisplay for EvalDropTracked {
        fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "<eval-drop-tracked>")
        }
    }

    fn reset_eval_drop_tracked_count() {
        EVAL_DROP_TRACKED_COUNT.store(0, Ordering::Relaxed);
    }

    fn eval_drop_tracked_type() -> Type {
        crate::cached_primitive_ty!(EvalDropTracked)
    }

    fn eval_args_test_session() -> (CompilerSession, ModuleId) {
        let mut session = CompilerSession::new();
        let module_id = ModuleId::from_index(2);
        let path = Path::single_str("$eval_args_test");
        let module = Module::new(module_id, path.clone());
        let registered = session.register_module(path, module);
        assert_eq!(registered, module_id);
        (session, module_id)
    }

    fn eval_drop_tracked_count() -> usize {
        EVAL_DROP_TRACKED_COUNT.load(Ordering::Relaxed)
    }

    #[test]
    fn with_yielded_body_value_wins_over_epilogue_transfer() {
        let result = combine_with_yielded_body_and_epilogue(
            cont(Value::native(1 as Int)),
            ret(Value::native(2 as Int)),
        )
        .expect("epilogue transfer should not fail body result");

        let ControlFlow::Continue(value) = result else {
            panic!("expected body value to win over epilogue transfer");
        };
        assert_eq!(value.into_primitive_ty::<Int>(), Some(1));
    }

    #[test]
    fn with_yielded_body_error_wins_over_epilogue_transfer() {
        let result = combine_with_yielded_body_and_epilogue(
            Err(RuntimeError::new_native(RuntimeErrorKind::Aborted(Some(
                "body".into(),
            )))),
            ret(Value::native(2 as Int)),
        );

        let err = result.expect_err("expected body error to win over epilogue transfer");
        assert_eq!(
            err.kind,
            RuntimeErrorKind::Aborted(Some("body".to_string()))
        );
    }

    fn local(name: &str, mut_ty: MutType, ty: Type, span: Location) -> LocalDecl {
        LocalDecl::new((ustr(name), span), mut_ty, ty, None, span)
    }

    fn owned_local(name: &str, mut_ty: MutType, ty: Type, span: Location) -> LocalDecl {
        let mut local = local(name, mut_ty, ty, span);
        local.set_owned_storage(PendingLocalDrop::Resolved(ResolvedLocalDrop::Skip));
        local
    }

    fn function_definition(
        fn_ty: FnType,
        arg_names: impl IntoIterator<Item = &'static str>,
    ) -> CallableDefinition {
        CallableDefinition::new(
            TypeScheme::new_infer_quantifiers(fn_ty),
            arg_names.into_iter().map(ustr).collect(),
            None,
        )
    }

    fn log_epilogue_accessor_function(
        arena: &mut ENodeArena,
        marker: Int,
        scratch_value: Int,
        span: Location,
    ) -> (ModuleFunction, FnType) {
        let int_ty = int_type();
        let accessor_log = LocalDeclId::from_index(0);
        let accessor_scratch = LocalDeclId::from_index(1);

        let scratch_value = node(arena, hir_syn::native(scratch_value), int_ty, span);
        let store_scratch = node(
            arena,
            hir_syn::store_local_to(scratch_value, accessor_scratch),
            Type::unit(),
            span,
        );
        let load_scratch = node(arena, hir_syn::load_local(accessor_scratch), int_ty, span);
        let yield_scratch = node(arena, hir_syn::yield_(load_scratch), Type::never(), span);
        let load_log = node(arena, hir_syn::load_local(accessor_log), int_ty, span);
        let marker = node(arena, hir_syn::native(marker), int_ty, span);
        let assign_log = node(
            arena,
            hir_syn::assign(load_log, marker, None),
            Type::unit(),
            span,
        );
        let accessor_entry = node(
            arena,
            NodeKind::Block(b(hir::Block {
                body: b(SVec2::from_vec(vec![
                    store_scratch,
                    yield_scratch,
                    assign_log,
                ])),
                cleanup: vec![accessor_scratch],
            })),
            Type::unit(),
            span,
        );

        let accessor_fn_ty = FnType::new(
            vec![FnArgType::new(int_ty, MutType::mutable())],
            int_ty,
            EffType::empty(),
        );
        let mut accessor_locals = vec![
            local("log", MutType::mutable(), int_ty, span),
            owned_local("scratch", MutType::mutable(), int_ty, span),
        ];
        LocalDecl::assign_sequential_slots(&mut accessor_locals);
        let accessor_locals = accessor_locals
            .into_iter()
            .map(LocalDecl::into_elaborated)
            .collect::<Vec<_>>();
        let accessor_function = ModuleFunction::new_elaborated(
            function_definition(accessor_fn_ty.clone(), ["log"]),
            b(ScriptFunction {
                entry_node_id: accessor_entry,
                yield_node_id: Some(yield_scratch),
                runtime_arg_count: 1,
            }),
            vec![ResolvedArgPassing::MutableRef],
            None,
            accessor_locals,
        );
        (accessor_function, accessor_fn_ty)
    }

    fn node(
        arena: &mut ENodeArena,
        kind: NodeKind<Elaborated>,
        ty: Type,
        span: Location,
    ) -> hir::ENodeId {
        arena.alloc(ENode::new(kind, ty, EffType::empty(), span))
    }

    #[test]
    fn with_yielded_runs_body_then_accessor_epilogue() {
        let span = Location::new_synthesized();
        let int_ty = int_type();
        let mut arena = ENodeArena::default();
        let test_module_id = ModuleId::from_index(2);

        let accessor_log = LocalDeclId::from_index(0);
        let accessor_scratch = LocalDeclId::from_index(1);
        let caller_log = LocalDeclId::from_index(0);
        let caller_result = LocalDeclId::from_index(1);
        let caller_binding = LocalDeclId::from_index(2);

        let value_41 = node(&mut arena, hir_syn::native(41 as Int), int_ty, span);
        let value_2 = node(&mut arena, hir_syn::native(2 as Int), int_ty, span);
        let store_scratch = node(
            &mut arena,
            hir_syn::store_local_to(value_41, accessor_scratch),
            Type::unit(),
            span,
        );
        let load_scratch = node(
            &mut arena,
            hir_syn::load_local(accessor_scratch),
            int_ty,
            span,
        );
        let yield_scratch = node(
            &mut arena,
            hir_syn::yield_(load_scratch),
            Type::never(),
            span,
        );
        let load_accessor_log = node(&mut arena, hir_syn::load_local(accessor_log), int_ty, span);
        let assign_log = node(
            &mut arena,
            hir_syn::assign(load_accessor_log, value_2, None),
            Type::unit(),
            span,
        );
        let accessor_entry = node(
            &mut arena,
            NodeKind::Block(b(hir::Block {
                body: b(SVec2::from_vec(vec![
                    store_scratch,
                    yield_scratch,
                    assign_log,
                ])),
                cleanup: vec![accessor_scratch],
            })),
            Type::unit(),
            span,
        );

        let value_0 = node(&mut arena, hir_syn::native(0 as Int), int_ty, span);
        let store_caller_log = node(
            &mut arena,
            hir_syn::store_local_to(value_0, caller_log),
            Type::unit(),
            span,
        );
        let load_caller_log_for_arg =
            node(&mut arena, hir_syn::load_local(caller_log), int_ty, span);
        let accessor_fn_ty = FnType::new(
            vec![FnArgType::new(int_ty, MutType::mutable())],
            int_ty,
            EffType::empty(),
        );
        let accessor_id = LocalFunctionId::from_index(0);
        let accessor_call = node(
            &mut arena,
            hir_syn::static_apply_with_result_convention(
                crate::module::FunctionId::new(test_module_id, accessor_id),
                accessor_fn_ty.clone(),
                CallResultConvention::YIELDED_ONCE,
                vec![CallArgument {
                    value: load_caller_log_for_arg,
                    passing: ResolvedArgPassing::MutableRef,
                }],
                span,
            ),
            int_ty,
            span,
        );
        let load_binding = node(
            &mut arena,
            hir_syn::load_local(caller_binding),
            int_ty,
            span,
        );
        let load_caller_result_place =
            node(&mut arena, hir_syn::load_local(caller_result), int_ty, span);
        let store_body_result = node(
            &mut arena,
            hir_syn::assign(load_caller_result_place, load_binding, None),
            Type::unit(),
            span,
        );
        let with_yielded = node(
            &mut arena,
            hir_syn::with_yielded(accessor_call, caller_binding, store_body_result),
            Type::unit(),
            span,
        );
        let load_caller_result = node(&mut arena, hir_syn::load_local(caller_result), int_ty, span);
        let load_caller_log = node(&mut arena, hir_syn::load_local(caller_log), int_ty, span);
        let tuple = node(
            &mut arena,
            hir_syn::tuple([load_caller_result, load_caller_log]),
            Type::tuple([int_ty, int_ty]),
            span,
        );
        let caller_entry = node(
            &mut arena,
            NodeKind::Block(b(hir::Block {
                body: b(SVec2::from_vec(vec![store_caller_log, with_yielded, tuple])),
                cleanup: vec![caller_log, caller_result],
            })),
            Type::tuple([int_ty, int_ty]),
            span,
        );

        let mut accessor_locals = vec![
            local("log", MutType::mutable(), int_ty, span),
            owned_local("scratch", MutType::mutable(), int_ty, span),
        ];
        LocalDecl::assign_sequential_slots(&mut accessor_locals);
        let accessor_locals = accessor_locals
            .into_iter()
            .map(LocalDecl::into_elaborated)
            .collect::<Vec<_>>();
        let accessor_function = ModuleFunction::new_elaborated(
            function_definition(accessor_fn_ty, ["log"]),
            b(ScriptFunction {
                entry_node_id: accessor_entry,
                yield_node_id: Some(yield_scratch),
                runtime_arg_count: 1,
            }),
            vec![ResolvedArgPassing::MutableRef],
            None,
            accessor_locals,
        );

        let mut caller_locals = vec![
            owned_local("log", MutType::mutable(), int_ty, span),
            owned_local("result", MutType::mutable(), int_ty, span),
            local("$yielded", MutType::mutable(), int_ty, span),
        ];
        LocalDecl::assign_sequential_slots(&mut caller_locals);
        let caller_locals = caller_locals
            .into_iter()
            .map(LocalDecl::into_elaborated)
            .collect::<Vec<_>>();

        let path = Path::single_str("$with_yielded_test");
        let mut module = Module::new(test_module_id, path.clone());
        module.hir_arena = arena;
        let registered_accessor = module.add_function(ustr("accessor"), accessor_function);
        assert_eq!(registered_accessor, accessor_id);

        let mut session = CompilerSession::new();
        let module_id = session.register_module(path, module);
        let module = session.expect_fresh_module(module_id);
        let result = eval_node(
            &module.hir_arena,
            caller_entry,
            module_id,
            &caller_locals,
            &session,
        )
        .unwrap()
        .into_value();

        let mut values = result.into_tuple().expect("caller should return a tuple");
        assert_eq!(values[0].as_primitive_ty::<Int>(), Some(&(41 as Int)));
        assert_eq!(values[1].as_primitive_ty::<Int>(), Some(&(2 as Int)));
        while let Some(value) = values.pop() {
            value.discard_storage();
        }
    }

    #[test]
    fn with_yielded_runs_accessor_epilogue_when_body_returns() {
        reset_eval_drop_tracked_count();
        let span = Location::new_synthesized();
        let int_ty = int_type();
        let mut arena = ENodeArena::default();
        let test_module_id = ModuleId::from_index(2);

        let accessor_scratch = LocalDeclId::from_index(0);
        let caller_binding = LocalDeclId::from_index(0);

        let value_41 = node(&mut arena, hir_syn::native(41 as Int), int_ty, span);
        let store_scratch = node(
            &mut arena,
            hir_syn::store_local_to(value_41, accessor_scratch),
            Type::unit(),
            span,
        );
        let load_scratch = node(
            &mut arena,
            hir_syn::load_local(accessor_scratch),
            int_ty,
            span,
        );
        let yield_scratch = node(
            &mut arena,
            hir_syn::yield_(load_scratch),
            Type::never(),
            span,
        );
        let epilogue_tracked = node(
            &mut arena,
            hir_syn::native(EvalDropTracked),
            eval_drop_tracked_type(),
            span,
        );
        let accessor_entry = node(
            &mut arena,
            NodeKind::Block(b(hir::Block {
                body: b(SVec2::from_vec(vec![
                    store_scratch,
                    yield_scratch,
                    epilogue_tracked,
                ])),
                cleanup: vec![accessor_scratch],
            })),
            eval_drop_tracked_type(),
            span,
        );

        let accessor_id = LocalFunctionId::from_index(0);
        let accessor_fn_ty = FnType::new(vec![], int_ty, EffType::empty());
        let accessor_call = node(
            &mut arena,
            hir_syn::static_apply_with_result_convention(
                crate::module::FunctionId::new(test_module_id, accessor_id),
                accessor_fn_ty.clone(),
                CallResultConvention::YIELDED_ONCE,
                Vec::new(),
                span,
            ),
            int_ty,
            span,
        );
        let unit = node(&mut arena, hir_syn::native(()), Type::unit(), span);
        let body_return = node(&mut arena, hir_syn::return_(unit), Type::never(), span);
        let with_yielded = node(
            &mut arena,
            hir_syn::with_yielded(accessor_call, caller_binding, body_return),
            Type::never(),
            span,
        );

        let mut accessor_locals = vec![owned_local("scratch", MutType::mutable(), int_ty, span)];
        LocalDecl::assign_sequential_slots(&mut accessor_locals);
        let accessor_locals = accessor_locals
            .into_iter()
            .map(LocalDecl::into_elaborated)
            .collect::<Vec<_>>();
        let accessor_function = ModuleFunction::new_elaborated(
            function_definition(accessor_fn_ty, []),
            b(ScriptFunction {
                entry_node_id: accessor_entry,
                yield_node_id: Some(yield_scratch),
                runtime_arg_count: 0,
            }),
            Vec::new(),
            None,
            accessor_locals,
        );

        let mut caller_locals = vec![local("$yielded", MutType::mutable(), int_ty, span)];
        LocalDecl::assign_sequential_slots(&mut caller_locals);
        let caller_locals = caller_locals
            .into_iter()
            .map(LocalDecl::into_elaborated)
            .collect::<Vec<_>>();

        let path = Path::single_str("$with_yielded_return_test");
        let mut module = Module::new(test_module_id, path.clone());
        module.hir_arena = arena;
        let registered_accessor = module.add_function(ustr("accessor"), accessor_function);
        assert_eq!(registered_accessor, accessor_id);

        let mut session = CompilerSession::new();
        let module_id = session.register_module(path, module);
        let module = session.expect_fresh_module(module_id);
        let result = eval_node(
            &module.hir_arena,
            with_yielded,
            module_id,
            &caller_locals,
            &session,
        )
        .unwrap();

        let ControlFlow::Transfer(ControlTransfer::Return(value)) = result else {
            panic!("expected body return to propagate");
        };
        assert!(value.as_primitive_ty::<()>().is_some());
        value.discard_storage();
        assert_eq!(eval_drop_tracked_count(), 1);
    }

    #[test]
    fn nested_with_yielded_runs_epilogues_lifo() {
        let span = Location::new_synthesized();
        let int_ty = int_type();
        let mut arena = ENodeArena::default();
        let test_module_id = ModuleId::from_index(2);

        let caller_log = LocalDeclId::from_index(0);
        let outer_binding = LocalDeclId::from_index(1);
        let inner_binding = LocalDeclId::from_index(2);

        let outer_id = LocalFunctionId::from_index(0);
        let inner_id = LocalFunctionId::from_index(1);
        let (outer_function, outer_fn_ty) = log_epilogue_accessor_function(&mut arena, 4, 41, span);
        let (inner_function, inner_fn_ty) = log_epilogue_accessor_function(&mut arena, 3, 42, span);

        let value_0 = node(&mut arena, hir_syn::native(0 as Int), int_ty, span);
        let store_log = node(
            &mut arena,
            hir_syn::store_local_to(value_0, caller_log),
            Type::unit(),
            span,
        );
        let outer_log_arg = node(&mut arena, hir_syn::load_local(caller_log), int_ty, span);
        let outer_call = node(
            &mut arena,
            hir_syn::static_apply(
                crate::module::FunctionId::new(test_module_id, outer_id),
                outer_fn_ty,
                vec![CallArgument {
                    value: outer_log_arg,
                    passing: ResolvedArgPassing::MutableRef,
                }],
                span,
            ),
            int_ty,
            span,
        );
        let inner_log_arg = node(&mut arena, hir_syn::load_local(caller_log), int_ty, span);
        let inner_call = node(
            &mut arena,
            hir_syn::static_apply(
                crate::module::FunctionId::new(test_module_id, inner_id),
                inner_fn_ty,
                vec![CallArgument {
                    value: inner_log_arg,
                    passing: ResolvedArgPassing::MutableRef,
                }],
                span,
            ),
            int_ty,
            span,
        );
        let unit = node(&mut arena, hir_syn::native(()), Type::unit(), span);
        let inner_with_yielded = node(
            &mut arena,
            hir_syn::with_yielded(inner_call, inner_binding, unit),
            Type::unit(),
            span,
        );
        let outer_with_yielded = node(
            &mut arena,
            hir_syn::with_yielded(outer_call, outer_binding, inner_with_yielded),
            Type::unit(),
            span,
        );
        let load_log = node(&mut arena, hir_syn::load_local(caller_log), int_ty, span);
        let caller_entry = node(
            &mut arena,
            NodeKind::Block(b(hir::Block {
                body: b(SVec2::from_vec(vec![
                    store_log,
                    outer_with_yielded,
                    load_log,
                ])),
                cleanup: vec![caller_log],
            })),
            int_ty,
            span,
        );

        let mut caller_locals = vec![
            owned_local("log", MutType::mutable(), int_ty, span),
            local("$outer_yielded", MutType::mutable(), int_ty, span),
            local("$inner_yielded", MutType::mutable(), int_ty, span),
        ];
        LocalDecl::assign_sequential_slots(&mut caller_locals);
        let caller_locals = caller_locals
            .into_iter()
            .map(LocalDecl::into_elaborated)
            .collect::<Vec<_>>();

        let path = Path::single_str("$with_yielded_lifo_test");
        let mut module = Module::new(test_module_id, path.clone());
        module.hir_arena = arena;
        assert_eq!(module.add_function(ustr("outer"), outer_function), outer_id);
        assert_eq!(module.add_function(ustr("inner"), inner_function), inner_id);

        let mut session = CompilerSession::new();
        let module_id = session.register_module(path, module);
        let module = session.expect_fresh_module(module_id);
        let result = eval_node(
            &module.hir_arena,
            caller_entry,
            module_id,
            &caller_locals,
            &session,
        )
        .unwrap()
        .into_value();

        assert_eq!(result.as_primitive_ty::<Int>(), Some(&(4 as Int)));
    }

    #[test]
    fn eval_nodes_discards_partial_values_on_return() {
        reset_eval_drop_tracked_count();
        let span = Location::new_synthesized();
        let mut arena = ENodeArena::default();
        let tracked = arena.alloc(ENode::new(
            NodeKind::Immediate(LiteralValue::new_native(EvalDropTracked)),
            eval_drop_tracked_type(),
            EffType::empty(),
            span,
        ));
        let unit = arena.alloc(ENode::new(
            NodeKind::Immediate(LiteralValue::new_native(())),
            Type::unit(),
            EffType::empty(),
            span,
        ));
        let return_unit = arena.alloc(ENode::new(
            NodeKind::Return(unit),
            Type::never(),
            EffType::empty(),
            span,
        ));
        let (session, module_id) = eval_args_test_session();
        let mut ctx = EvalCtx::new(module_id, &session);

        let result = eval_nodes(&arena, &[tracked, return_unit], &mut ctx, &[]).unwrap();
        let ControlFlow::Transfer(ControlTransfer::Return(value)) = result else {
            panic!("expected eval_nodes to propagate return");
        };

        assert_eq!(eval_drop_tracked_count(), 1);
        value.discard_storage();
    }

    #[test]
    fn block_discards_previous_value_on_break() {
        reset_eval_drop_tracked_count();
        let span = Location::new_synthesized();
        let label = LoopId::from_index(0);
        let mut arena = ENodeArena::default();
        let tracked = arena.alloc(ENode::new(
            NodeKind::Immediate(LiteralValue::new_native(EvalDropTracked)),
            Type::primitive::<EvalDropTracked>(),
            EffType::empty(),
            span,
        ));
        let unit = arena.alloc(ENode::new(
            NodeKind::Immediate(LiteralValue::new_native(())),
            Type::unit(),
            EffType::empty(),
            span,
        ));
        let break_node = arena.alloc(ENode::new(
            NodeKind::Break(hir::Break { label, value: unit }),
            Type::never(),
            EffType::empty(),
            span,
        ));
        let block = arena.alloc(ENode::new(
            NodeKind::Block(b(hir::Block {
                body: b(SVec2::from_vec(vec![tracked, break_node])),
                cleanup: Vec::new(),
            })),
            Type::never(),
            EffType::empty(),
            span,
        ));
        let session = CompilerSession::new();
        let result = eval_node(&arena, block, ModuleId::from_index(0), &[], &session).unwrap();
        let ControlFlow::Transfer(ControlTransfer::Break { value, .. }) = result else {
            panic!("expected block to propagate break");
        };

        assert_eq!(eval_drop_tracked_count(), 1);
        value.discard_storage();
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "owned local `leaked` left initialized at scope exit")]
    fn debug_scope_truncation_detects_missing_owned_local_cleanup() {
        let span = Location::new_synthesized();
        let leaked = LocalDeclId::from_index(0);
        let mut arena = ENodeArena::default();
        let value = node(&mut arena, hir_syn::native(()), Type::unit(), span);
        let store = node(
            &mut arena,
            hir_syn::store_local_to(value, leaked),
            Type::unit(),
            span,
        );
        let tail = node(&mut arena, hir_syn::native(()), Type::unit(), span);
        let block = node(
            &mut arena,
            NodeKind::Block(b(hir::Block {
                body: b(SVec2::from_vec(vec![store, tail])),
                cleanup: Vec::new(),
            })),
            Type::unit(),
            span,
        );
        let mut locals = [owned_local(
            "leaked",
            MutType::constant(),
            Type::unit(),
            span,
        )];
        LocalDecl::assign_sequential_slots(&mut locals);
        let locals = locals.map(LocalDecl::into_elaborated);
        let session = CompilerSession::new();

        let _ = eval_node(&arena, block, ModuleId::from_index(0), &locals, &session);
    }

    #[test]
    fn break_value_transfer_happens_before_break_is_emitted() {
        let span = Location::new_synthesized();
        let label = LoopId::from_index(0);
        let mut arena = ENodeArena::default();
        let unit = arena.alloc(ENode::new(
            NodeKind::Immediate(LiteralValue::new_native(())),
            Type::unit(),
            EffType::empty(),
            span,
        ));
        let return_unit = arena.alloc(ENode::new(
            NodeKind::Return(unit),
            Type::never(),
            EffType::empty(),
            span,
        ));
        let break_node = arena.alloc(ENode::new(
            NodeKind::Break(hir::Break {
                label,
                value: return_unit,
            }),
            Type::never(),
            EffType::empty(),
            span,
        ));
        let loop_node = arena.alloc(ENode::new(
            NodeKind::Loop(hir::Loop {
                label,
                body: break_node,
            }),
            Type::never(),
            EffType::empty(),
            span,
        ));
        let session = CompilerSession::new();
        let result = eval_node(&arena, loop_node, ModuleId::from_index(0), &[], &session).unwrap();
        let ControlFlow::Transfer(ControlTransfer::Return(value)) = result else {
            panic!("expected return in break value to propagate before break");
        };

        assert!(value.as_primitive_ty::<()>().is_some());
    }

    #[test]
    fn eval_args_discards_partial_values_on_return() {
        reset_eval_drop_tracked_count();
        let span = Location::new_synthesized();
        let mut arena = ENodeArena::default();
        let tracked = arena.alloc(ENode::new(
            NodeKind::Immediate(LiteralValue::new_native(EvalDropTracked)),
            Type::primitive::<EvalDropTracked>(),
            EffType::empty(),
            span,
        ));
        let unit = arena.alloc(ENode::new(
            NodeKind::Immediate(LiteralValue::new_native(())),
            Type::unit(),
            EffType::empty(),
            span,
        ));
        let return_unit = arena.alloc(ENode::new(
            NodeKind::Return(unit),
            Type::never(),
            EffType::empty(),
            span,
        ));
        let (session, module_id) = eval_args_test_session();
        let mut ctx = EvalCtx::new(module_id, &session);
        let arg_tys = [
            FnArgType::new_by_val(eval_drop_tracked_type()),
            FnArgType::new_by_val(Type::unit()),
        ];
        let arguments = [
            CallArgument {
                value: tracked,
                passing: ResolvedArgPassing::Value(ResolvedValueArgPassing::TrivialCopy),
            },
            CallArgument {
                value: return_unit,
                passing: ResolvedArgPassing::Value(ResolvedValueArgPassing::TrivialCopy),
            },
        ];

        let result = eval_args(&arena, &arguments, &arg_tys, &mut ctx, &[]).unwrap();
        let ControlFlow::Transfer(ControlTransfer::Return(value)) = result else {
            panic!("expected eval_args to propagate return");
        };

        assert_eq!(eval_drop_tracked_count(), 1);
        value.discard_storage();
    }

    #[test]
    fn eval_args_discards_partial_values_on_break() {
        reset_eval_drop_tracked_count();
        let span = Location::new_synthesized();
        let label = LoopId::from_index(0);
        let mut arena = ENodeArena::default();
        let tracked = arena.alloc(ENode::new(
            NodeKind::Immediate(LiteralValue::new_native(EvalDropTracked)),
            eval_drop_tracked_type(),
            EffType::empty(),
            span,
        ));
        let unit = arena.alloc(ENode::new(
            NodeKind::Immediate(LiteralValue::new_native(())),
            Type::unit(),
            EffType::empty(),
            span,
        ));
        let break_node = arena.alloc(ENode::new(
            NodeKind::Break(hir::Break { label, value: unit }),
            Type::never(),
            EffType::empty(),
            span,
        ));
        let (session, module_id) = eval_args_test_session();
        let mut ctx = EvalCtx::new(module_id, &session);
        let arg_tys = [
            FnArgType::new_by_val(eval_drop_tracked_type()),
            FnArgType::new_by_val(Type::unit()),
        ];
        let arguments = [
            CallArgument {
                value: tracked,
                passing: ResolvedArgPassing::Value(ResolvedValueArgPassing::TrivialCopy),
            },
            CallArgument {
                value: break_node,
                passing: ResolvedArgPassing::Value(ResolvedValueArgPassing::TrivialCopy),
            },
        ];

        let result = eval_args(&arena, &arguments, &arg_tys, &mut ctx, &[]).unwrap();
        let ControlFlow::Transfer(ControlTransfer::Break { value, .. }) = result else {
            panic!("expected eval_args to propagate break");
        };

        assert_eq!(eval_drop_tracked_count(), 1);
        value.discard_storage();
    }
}
