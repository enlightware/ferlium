// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Boxed storage, call boundaries, and execution limits shared by the HIR and MIR interpreters.

pub mod buffer;

use std::mem;

use enum_as_inner::EnumAsInner;

use crate::{
    CompilerSession, FxHashMap, Location, ModuleRegistry, Modules, SourceId, SourceTable,
    compiler::error::{RuntimeErrorKind, SandboxViolationKind, SourceFailureKind},
    execution::ReferenceInterpreterLimits,
    format::{FormatWith, write_with_separator},
    hir::{
        function::CallArgsStorageGuard,
        native_functions::NativeFailureState,
        value::{
            ClosedTraitDictionary, HiddenEvidenceArgValue, NativeValue, NativeValueType, Value,
        },
    },
    module::{
        CallableOrigin, FunctionId, LocalDebugVisibility, ModuleFunction, ModuleId,
        ResolvedValueLayout, SubscriptId, TraitDictionary,
    },
    place::Place,
    types::r#type::Type,
};

/// Either a value or a unique mutable reference to a value.
/// This allows to implement the mutable value semantics.
#[derive(Debug, EnumAsInner)]
pub enum ValOrMut {
    /// A value, itself
    Val(Value),
    /// Runtime trait dictionary metadata.
    Dictionary(ClosedTraitDictionary),
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
    ) -> Result<Option<&'a mut T>, SourceFailureKind> {
        Ok(match self {
            ValOrMut::Val(_) => None,
            ValOrMut::Dictionary(_) => None,
            ValOrMut::Ref(_) => None,
            ValOrMut::Mut(place) => {
                if let Some(native) = place.native_member(ctx) {
                    let pointer = native.mutable::<T>();
                    // SAFETY: exclusive call-scoped access is established by the place borrow.
                    pointer.map(|pointer| unsafe { &mut *pointer })
                } else {
                    place.boxed_mut(ctx)?.as_primitive_ty_mut::<T>()
                }
            }
        })
    }

    pub fn as_primitive<'a, T: 'static>(
        &'a self,
        ctx: &'a EvalCtx<'_>,
    ) -> Result<Option<&'a T>, SourceFailureKind> {
        if matches!(self, ValOrMut::Dictionary(_)) {
            return Ok(None);
        }
        Ok(self.as_value_ref(ctx)?.as_primitive_ty::<T>())
    }

    /// Borrow an argument without requiring its contents to occupy a boxed `Value` slot.
    pub fn as_value_ref<'a>(
        &'a self,
        ctx: &'a EvalCtx<'_>,
    ) -> Result<ValueRef<'a>, SourceFailureKind> {
        let value = match self {
            ValOrMut::Val(value) => ValueRef::Boxed(value),
            ValOrMut::Dictionary(_) => panic!("attempted to read a trait dictionary as a Value"),
            ValOrMut::Ref(value) => {
                // SAFETY: `Ref` entries exist only for a synchronous interpreter call;
                // their environment frame is truncated before the referent can go away.
                ValueRef::Boxed(unsafe { &**value })
            }
            ValOrMut::Mut(place) => place.target_ref(ctx)?,
        };
        assert!(
            !value.is_uninit(),
            "attempted to read an uninitialized value"
        );
        Ok(value)
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

fn evidence_arg_to_val_or_mut(arg: HiddenEvidenceArgValue) -> ValOrMut {
    match arg {
        HiddenEvidenceArgValue::TraitDictionary(dictionary) => ValOrMut::Dictionary(dictionary),
        HiddenEvidenceArgValue::Subscript(subscript) => {
            ValOrMut::Val(Value::subscript_value(*subscript))
        }
        HiddenEvidenceArgValue::VariantPayloadStorage(storage) => {
            ValOrMut::Val(Value::native(storage.is_indirect()))
        }
    }
}

/// Shared boxed storage and execution-domain state, independent of interpreter frames.
pub struct EvalCtx<'a> {
    /// all values or mutable references of all stack frames
    pub environment: Vec<ValOrMut>,
    /// current function call depth
    pub call_depth: usize,
    /// maximum function call depth
    call_depth_limit: usize,
    /// maximum number of entries in the reference interpreters' shared environment
    pub environment_cell_limit: usize,
    /// remaining execution fuel; `None` means fuel checks are disabled
    fuel_remaining: Option<usize>,
    /// Whether this executor can still safely run Ferlium code.
    execution_state: ExecutionState,
    /// One diagnostic cell for all native calls in this host invocation.
    pub(crate) native_failure: NativeFailureState,
    /// id of the current module for import slot resolution
    pub module_id: ModuleId,
    /// Resolved layouts reused across calls in this execution domain.
    layout_cache: FxHashMap<(ModuleId, Type), ResolvedValueLayout>,
    /// session holding sources and other modules for error reporting and import resolution
    compiler_session: &'a CompilerSession,
}

impl<'a> EvalCtx<'a> {
    pub fn new(module_id: ModuleId, compiler_session: &'a CompilerSession) -> EvalCtx<'a> {
        Self::with_limits(
            module_id,
            compiler_session,
            ReferenceInterpreterLimits::default(),
        )
    }

    pub fn with_limits(
        module_id: ModuleId,
        compiler_session: &'a CompilerSession,
        limits: ReferenceInterpreterLimits,
    ) -> EvalCtx<'a> {
        Self::with_environment_and_limits(module_id, Vec::new(), compiler_session, limits)
    }

    /// Get the compiler session.
    pub fn compiler_session(&self) -> &'a CompilerSession {
        self.compiler_session
    }

    pub fn check_fuel(&mut self, span: Location) -> Result<(), RuntimeError> {
        let Some(fuel) = &mut self.fuel_remaining else {
            return Ok(());
        };
        if *fuel == 0 {
            Err(self.sandbox_violation(SandboxViolationKind::FuelExhausted, Some(span)))
        } else {
            *fuel -= 1;
            Ok(())
        }
    }

    pub fn check_call_depth(&mut self, span: Location) -> Result<(), RuntimeError> {
        if self.call_depth >= self.call_depth_limit {
            Err(self.sandbox_violation(
                SandboxViolationKind::CallDepthLimitExceeded {
                    limit: self.call_depth_limit,
                },
                Some(span),
            ))
        } else {
            Ok(())
        }
    }

    /// Errors if `next_index` is outside the configured environment-cell range.
    ///
    /// Callers pass either `environment.len()` before appending one cell or the concrete local-slot
    /// index they are about to materialize. `span` is `None` at call-frame entry, where the caller
    /// attaches the call site as a backtrace frame.
    pub(crate) fn check_environment_cell_limit(
        &mut self,
        next_index: usize,
        span: Option<Location>,
    ) -> Result<(), RuntimeError> {
        if next_index >= self.environment_cell_limit {
            return Err(self.environment_cell_limit_error(span));
        }
        Ok(())
    }

    pub(crate) fn environment_cell_limit_error(&mut self, span: Option<Location>) -> RuntimeError {
        self.sandbox_violation(
            SandboxViolationKind::EnvironmentCellLimitExceeded {
                limit: self.environment_cell_limit,
            },
            span,
        )
    }

    fn sandbox_violation(
        &mut self,
        kind: SandboxViolationKind,
        location: Option<Location>,
    ) -> RuntimeError {
        let RuntimeError::SandboxViolation(violation) =
            RuntimeError::new_sandbox_violation(kind, location)
        else {
            unreachable!()
        };
        self.execution_state =
            ExecutionState::Poisoned(PoisonReason::SandboxViolation(violation.clone()));
        RuntimeError::SandboxViolation(violation)
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

    pub(crate) fn ensure_environment_slot(&mut self, index: usize) {
        while self.environment.len() <= index {
            self.environment.push(ValOrMut::Val(Value::uninit()));
        }
    }

    pub(crate) fn set_environment_entry(&mut self, index: usize, value: ValOrMut) {
        self.ensure_environment_slot(index);
        let old = mem::replace(&mut self.environment[index], value);
        old.discard_storage();
    }

    pub fn with_environment(
        module: ModuleId,
        environment: Vec<ValOrMut>,
        compiler_session: &'a CompilerSession,
    ) -> EvalCtx<'a> {
        Self::with_environment_and_limits(
            module,
            environment,
            compiler_session,
            ReferenceInterpreterLimits::default(),
        )
    }

    pub fn with_environment_and_limits(
        module: ModuleId,
        environment: Vec<ValOrMut>,
        compiler_session: &'a CompilerSession,
        limits: ReferenceInterpreterLimits,
    ) -> EvalCtx<'a> {
        EvalCtx {
            environment,
            call_depth: 0,
            call_depth_limit: limits.execution.call_depth_limit,
            environment_cell_limit: limits.environment_cell_limit,
            fuel_remaining: limits.execution.fuel_limit,
            execution_state: ExecutionState::Running,
            native_failure: Default::default(),
            module_id: module,
            layout_cache: FxHashMap::default(),
            compiler_session,
        }
    }

    /// Resolves a value layout with per-execution reuse.
    pub(crate) fn value_layout(&mut self, ty: Type, span: Location) -> ResolvedValueLayout {
        if let Some(layout) = self.layout_cache.get(&(self.module_id, ty)) {
            return *layout;
        }
        let layout = self
            .compiler_session()
            .value_layout(self.module_id, ty, span)
            .unwrap_or_else(|_| {
                panic!(
                    "missing runtime layout for {} at {}",
                    ty.format_with(&self.compiler_session().module_env()),
                    span.format_with(self.compiler_session().source_table())
                )
            });
        self.layout_cache.insert((self.module_id, ty), layout);
        layout
    }

    /// Get a function's code and module for a FunctionId at runtime.
    pub fn get_module_function(&self, function: FunctionId) -> &ModuleFunction {
        let module = self.compiler_session.expect_fresh_module(function.module);
        module.get_function_by_id(function.function).unwrap()
    }

    /// Rejects entry into a poisoned execution domain.
    pub(crate) fn ensure_runnable(&self) -> Result<(), RuntimeError> {
        match &self.execution_state {
            ExecutionState::Running => Ok(()),
            ExecutionState::Poisoned(PoisonReason::SandboxViolation(violation)) => {
                Err(RuntimeError::SandboxViolation(violation.clone()))
            }
            ExecutionState::Poisoned(PoisonReason::FailureDuringCleanup(failure)) => Err(
                RuntimeError::FailureDuringCleanup(Box::new(failure.clone())),
            ),
        }
    }

    pub(crate) fn poison(
        &mut self,
        initial: RuntimeError,
        during_cleanup: RuntimeError,
    ) -> RuntimeError {
        self.record_poisoning_error(initial.interrupted_by(during_cleanup))
    }

    pub(crate) fn record_poisoning_error(&mut self, error: RuntimeError) -> RuntimeError {
        self.execution_state = ExecutionState::Poisoned(match &error {
            RuntimeError::Backend(_) => unreachable!("backend errors precede guest execution"),
            RuntimeError::SandboxViolation(violation) => {
                PoisonReason::SandboxViolation(violation.clone())
            }
            RuntimeError::FailureDuringCleanup(failure) => {
                PoisonReason::FailureDuringCleanup((**failure).clone())
            }
            RuntimeError::SourceFailure(_) => {
                panic!("source failure cannot directly poison an execution domain")
            }
        });
        error
    }

    pub fn is_poisoned(&self) -> bool {
        matches!(self.execution_state, ExecutionState::Poisoned(_))
    }

    pub(crate) fn subscript_member_function(
        &self,
        subscript: SubscriptId,
        mut_member: bool,
    ) -> FunctionId {
        let module = self.compiler_session.expect_fresh_module(subscript.module);
        let subscript_def = module
            .get_subscript_by_id(subscript.subscript)
            .expect("subscript value should reference an existing subscript");
        let member = if mut_member {
            subscript_def.mut_member.as_ref()
        } else {
            subscript_def.ref_member.as_ref()
        }
        .expect("subscript application should reference an available member");
        FunctionId::new(subscript.module, member.function)
    }

    pub fn dictionary_value(&self, dictionary: &ClosedTraitDictionary) -> &TraitDictionary {
        let module = self
            .compiler_session
            .expect_fresh_module(dictionary.definition.module_id);
        &module
            .get_impl_data(dictionary.definition.impl_id)
            .unwrap_or_else(|| panic!("trait dictionary impl not found: {:?}", dictionary))
            .dictionary_value
    }

    /// Calls a native or intrinsic entry in its module context; script dispatch belongs to interpreters.
    pub fn call_native(
        &mut self,
        function: FunctionId,
        evidence: Vec<HiddenEvidenceArgValue>,
        arguments: Vec<ValOrMut>,
        location: Location,
    ) -> EvalResult {
        let mut arguments = CallArgsStorageGuard::new(arguments);
        self.ensure_runnable()
            .map_err(|err| err.with_frame(function, location))?;
        let module = self.compiler_session.expect_fresh_module(function.module);
        let metadata = module.get_function_by_id(function.function).unwrap();
        assert!(
            metadata.code.as_script().is_none(),
            "script calls must be dispatched by their interpreter"
        );
        let caller_module = mem::replace(&mut self.module_id, function.module);
        let prepared = if evidence.is_empty() {
            arguments.take()
        } else {
            let mut prepared = Vec::with_capacity(evidence.len() + arguments.args.len());
            prepared.extend(evidence.into_iter().map(evidence_arg_to_val_or_mut));
            prepared.extend(arguments.take());
            prepared
        };
        let result = match metadata.origin {
            CallableOrigin::BufferPrimitive(primitive) => {
                buffer::eval_buffer_primitive(primitive, prepared, self)
            }
            _ => metadata.code.call(prepared, self),
        };
        self.module_id = caller_module;
        result.map_err(|err| err.with_frame(function, location))
    }
}

pub use crate::hir::value::ValueRef;

/// Internal runtime marker returned by addressor-place functions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlaceResult(Place);

impl NativeValueType for PlaceResult {}

impl PlaceResult {
    pub(crate) fn new(place: Place) -> Self {
        Self(place)
    }

    pub(crate) fn into_place(self) -> Place {
        self.0
    }

    /// Returns the place this addressor result denotes.
    pub fn place(&self) -> &Place {
        &self.0
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
            .module()
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

/// An execution error: either a backend failed to start or an outcome escaped a guest invocation.
#[derive(Debug, Clone)]
pub enum RuntimeError {
    /// Backend preparation, unsupported execution contract, or checked-storage failure.
    Backend(String),
    /// A failure declared by the source-level `Fallible` effect.
    SourceFailure(SourceFailure),
    /// A host-enforced limit violation. Guest cleanup must not run after this point.
    SandboxViolation(SandboxViolation),
    /// A second source failure raised while cleaning up an earlier one.
    FailureDuringCleanup(Box<FailureDuringCleanup>),
}

/// Source location and accumulated call stack shared by runtime diagnostics.
#[derive(Debug, Clone)]
pub struct FailureContext {
    location: Option<Location>,
    backtrace: Vec<BacktraceFrame>,
}

/// One source-level failure and its diagnostic context.
#[derive(Debug, Clone)]
pub struct SourceFailure {
    kind: SourceFailureKind,
    context: FailureContext,
}

/// A host-enforced limit violation and the source failure, if any, whose cleanup it interrupted.
#[derive(Debug, Clone)]
pub struct SandboxViolation {
    kind: SandboxViolationKind,
    context: FailureContext,
    interrupted_source_failure: Option<Box<SourceFailure>>,
}

/// The two source failures that made semantic cleanup impossible to complete.
#[derive(Debug, Clone)]
pub struct FailureDuringCleanup {
    initial: SourceFailure,
    during_cleanup: SourceFailure,
}

/// Why an execution domain can no longer run Ferlium code.
#[derive(Debug, Clone)]
pub enum PoisonReason {
    SandboxViolation(SandboxViolation),
    FailureDuringCleanup(FailureDuringCleanup),
}

impl FailureDuringCleanup {
    pub fn initial(&self) -> &SourceFailure {
        &self.initial
    }

    pub fn during_cleanup(&self) -> &SourceFailure {
        &self.during_cleanup
    }
}

impl SourceFailure {
    pub fn kind(&self) -> SourceFailureKind {
        self.kind.clone()
    }

    pub fn location(&self) -> Option<Location> {
        self.context.location
    }

    pub fn backtrace(&self) -> &[BacktraceFrame] {
        &self.context.backtrace
    }

    fn with_frame(mut self, function_id: FunctionId, location: Location) -> Self {
        self.context.backtrace.push(BacktraceFrame {
            function_id,
            call_site: location,
        });
        self
    }
}

impl SandboxViolation {
    pub fn kind(&self) -> SandboxViolationKind {
        self.kind.clone()
    }

    pub fn location(&self) -> Option<Location> {
        self.context.location
    }

    pub fn backtrace(&self) -> &[BacktraceFrame] {
        &self.context.backtrace
    }

    pub fn interrupted_source_failure(&self) -> Option<&SourceFailure> {
        self.interrupted_source_failure.as_deref()
    }

    fn with_frame(mut self, function_id: FunctionId, location: Location) -> Self {
        self.context.backtrace.push(BacktraceFrame {
            function_id,
            call_site: location,
        });
        self
    }
}

#[derive(Debug, Clone)]
enum ExecutionState {
    Running,
    Poisoned(PoisonReason),
}

impl RuntimeError {
    /// Combine an in-flight failure with the error that terminates its cleanup. Executors must
    /// stop guest execution after this result; backing storage can still be reclaimed.
    pub(crate) fn interrupted_by(self, error: Self) -> Self {
        match (self, error) {
            (Self::SourceFailure(initial), Self::SourceFailure(during_cleanup)) => {
                Self::FailureDuringCleanup(Box::new(FailureDuringCleanup {
                    initial,
                    during_cleanup,
                }))
            }
            (Self::SourceFailure(initial), Self::SandboxViolation(mut violation)) => {
                violation
                    .interrupted_source_failure
                    .get_or_insert_with(|| Box::new(initial));
                Self::SandboxViolation(violation)
            }
            (initial, _) if initial.is_poisoning() => initial,
            (_, error) => error,
        }
    }

    pub fn new(kind: SourceFailureKind, location: Option<Location>) -> Self {
        Self::SourceFailure(SourceFailure {
            kind,
            context: FailureContext {
                location,
                backtrace: Vec::new(),
            },
        })
    }

    pub fn new_native(kind: SourceFailureKind) -> Self {
        Self::new(kind, None)
    }

    pub(crate) fn new_sandbox_violation(
        kind: SandboxViolationKind,
        location: Option<Location>,
    ) -> Self {
        Self::SandboxViolation(SandboxViolation {
            kind,
            context: FailureContext {
                location,
                backtrace: Vec::new(),
            },
            interrupted_source_failure: None,
        })
    }

    pub fn with_frame(self, function_id: FunctionId, location: Location) -> Self {
        match self {
            Self::Backend(_) => self,
            Self::SourceFailure(failure) => {
                Self::SourceFailure(failure.with_frame(function_id, location))
            }
            Self::SandboxViolation(violation) => {
                Self::SandboxViolation(violation.with_frame(function_id, location))
            }
            Self::FailureDuringCleanup(failure) => {
                Self::FailureDuringCleanup(Box::new(FailureDuringCleanup {
                    initial: failure.initial.with_frame(function_id, location),
                    during_cleanup: failure.during_cleanup.with_frame(function_id, location),
                }))
            }
        }
    }

    pub fn source_failure(&self) -> Option<&SourceFailure> {
        match self {
            Self::SourceFailure(failure) => Some(failure),
            Self::Backend(_) | Self::SandboxViolation(_) | Self::FailureDuringCleanup(_) => None,
        }
    }

    pub fn kind(&self) -> RuntimeErrorKind {
        match self {
            Self::Backend(_) => RuntimeErrorKind::Backend,
            Self::SourceFailure(failure) => RuntimeErrorKind::SourceFailure(failure.kind()),
            Self::SandboxViolation(violation) => {
                RuntimeErrorKind::SandboxViolation(violation.kind())
            }
            Self::FailureDuringCleanup(_) => RuntimeErrorKind::FailureDuringCleanup,
        }
    }

    pub fn sandbox_violation(&self) -> Option<&SandboxViolation> {
        match self {
            Self::SandboxViolation(violation) => Some(violation),
            Self::Backend(_) | Self::SourceFailure(_) | Self::FailureDuringCleanup(_) => None,
        }
    }

    pub fn failure_during_cleanup(&self) -> Option<&FailureDuringCleanup> {
        match self {
            Self::FailureDuringCleanup(failure) => Some(failure),
            Self::Backend(_) | Self::SourceFailure(_) | Self::SandboxViolation(_) => None,
        }
    }

    pub fn location(&self) -> Option<Location> {
        match self {
            Self::Backend(_) => None,
            Self::SourceFailure(failure) => failure.location(),
            Self::SandboxViolation(violation) => violation.location(),
            Self::FailureDuringCleanup(failure) => failure.initial.location(),
        }
    }

    pub fn backtrace(&self) -> &[BacktraceFrame] {
        match self {
            Self::Backend(_) => &[],
            Self::SourceFailure(failure) => failure.backtrace(),
            Self::SandboxViolation(violation) => violation.backtrace(),
            Self::FailureDuringCleanup(failure) => failure.initial.backtrace(),
        }
    }

    /// Whether this error poisons its execution domain and forbids further guest cleanup.
    pub fn is_poisoning(&self) -> bool {
        matches!(
            self,
            Self::SandboxViolation(_) | Self::FailureDuringCleanup(_)
        )
    }

    pub fn top_most_location_in(&self, source_id: SourceId) -> Option<Location> {
        if let Some(location) = self.location()
            && location.source_id == source_id
        {
            return Some(location);
        }
        for frame in self.backtrace() {
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
        match self {
            Self::Backend(message) => write!(f, "Execution backend error: {message}")?,
            Self::SourceFailure(failure) => failure.fmt_with(f, data)?,
            Self::SandboxViolation(violation) => violation.fmt_with(f, data)?,
            Self::FailureDuringCleanup(failure) => {
                writeln!(f, "Execution poisoned by a failure during cleanup:")?;
                writeln!(f, "initial failure:")?;
                failure.initial.fmt_with(f, data)?;
                writeln!(f, "failure during cleanup:")?;
                failure.during_cleanup.fmt_with(f, data)?;
            }
        }
        Ok(())
    }
}

impl FormatWith<(&SourceTable, &Modules)> for SourceFailure {
    fn fmt_with(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        data: &(&SourceTable, &Modules),
    ) -> std::fmt::Result {
        write!(f, "Execution error: {}", self.kind)?;
        if let Some(location) = self.context.location {
            write!(f, " at {}", location.format_with(data.0))?;
        }
        writeln!(f)?;
        if !self.context.backtrace.is_empty() {
            writeln!(f, "stack backtrace:")?;
            let mut suspended_at = self.context.location;
            for (i, frame) in self.context.backtrace.iter().enumerate() {
                write!(f, "  {i}: ")?;
                frame.fmt_with_suspended_at(f, data, suspended_at)?;
                writeln!(f)?;
                suspended_at = Some(frame.call_site);
            }
        }
        Ok(())
    }
}

impl FormatWith<(&SourceTable, &Modules)> for SandboxViolation {
    fn fmt_with(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        data: &(&SourceTable, &Modules),
    ) -> std::fmt::Result {
        write!(f, "Sandbox violation: {}", self.kind)?;
        if let Some(location) = self.context.location {
            write!(f, " at {}", location.format_with(data.0))?;
        }
        writeln!(f)?;
        if !self.context.backtrace.is_empty() {
            writeln!(f, "stack backtrace:")?;
            let mut suspended_at = self.context.location;
            for (i, frame) in self.context.backtrace.iter().enumerate() {
                write!(f, "  {i}: ")?;
                frame.fmt_with_suspended_at(f, data, suspended_at)?;
                writeln!(f)?;
                suspended_at = Some(frame.call_site);
            }
        }
        if let Some(interrupted) = &self.interrupted_source_failure {
            writeln!(f, "interrupted source failure:")?;
            interrupted.fmt_with(f, data)?;
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

/// The result of a script or native call.
pub type EvalResult = Result<Value, RuntimeError>;
