// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Tree-walking HIR execution with call-local state and owned accessor suspensions.

use std::{collections::VecDeque, mem};

use crate::{
    CompilerSession, Location,
    containers::b,
    eval::{EvalCtx, EvalResult, PlaceResult, RuntimeError, ValOrMut, ValueRef},
    hir::{
        self, CallArgument, ENodeArena, ENodeId, Elaborated, LoopId, NodeKind,
        dictionary::{EvidenceBinding, EvidenceBindingSource, StaticEvidence},
        function::{
            ArgConvention, CallArgsStorageGuard, ScriptFunction, copy_boxed_trivial_copy_native,
        },
        value::{
            ClosedTraitDictionary, FunctionValue, HiddenEvidenceArgValue, SubscriptValue, Value,
        },
    },
    module::{
        ELocalDecl as LocalDecl, EvidenceBindingId, FunctionId, LocalDeclId, LocalFunctionId,
        ModuleFunction, ModuleId, ProjectionIndex, ResolvedLocalClone, ResolvedLocalDrop,
        ResolvedTakeLocalValueMode, ResolvedValueLayout, TraitDictionaryEntry, TraitDictionaryId,
        id::Id,
    },
    place::Place,
    std::{
        array::array_value_from_vec,
        value::{VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX},
    },
    types::{
        r#trait::{TraitDictionaryEntryIndex, TraitMethodIndex},
        r#type::{FnArgType, Type},
    },
};

/// HIR state belonging to one ordinary or suspended script call.
#[derive(Debug)]
struct HirFrame {
    environment_base: usize,
    evidence: Vec<HiddenEvidenceArgValue>,
    returns_place: bool,
}

impl HirFrame {
    fn for_call(
        function: FunctionId,
        environment_base: usize,
        metadata: &ModuleFunction,
        incoming: &[HiddenEvidenceArgValue],
    ) -> Self {
        let expected = metadata
            .evidence_bindings
            .iter()
            .take_while(|binding| matches!(binding.source, EvidenceBindingSource::Parameter(_)))
            .count();
        assert_eq!(
            incoming.len(),
            expected,
            "HIR call {function:?} hidden evidence does not match {:?}",
            metadata.definition,
        );
        Self {
            environment_base,
            evidence: materialize_evidence_bindings(&metadata.evidence_bindings, incoming),
            returns_place: metadata.definition.returns_place(),
        }
    }
}

/// Dispatches a resolved HIR call, delegating native and intrinsic entries to the shared runtime.
pub fn call_function(
    function: FunctionId,
    evidence: Vec<HiddenEvidenceArgValue>,
    arguments: Vec<ValOrMut>,
    location: Location,
    runtime: &mut EvalCtx,
) -> EvalResult {
    let mut arguments = CallArgsStorageGuard::new(arguments);
    let module = runtime
        .compiler_session()
        .expect_fresh_module(function.module);
    let metadata = module.get_function_by_id(function.function).unwrap();
    let Some(script) = metadata.code.as_script() else {
        return runtime.call_native(function, evidence, arguments.take(), location);
    };
    runtime
        .ensure_runnable()
        .map_err(|err| err.with_frame(function, location))?;
    let caller_module = mem::replace(&mut runtime.module_id, function.module);
    let result = eval_script_call(function, script, metadata, evidence, arguments, runtime);
    runtime.module_id = caller_module;
    result.map_err(|err| err.with_frame(function, location))
}

/// Enters one script frame; no HIR state is installed in the shared runtime.
fn eval_script_call(
    function: FunctionId,
    script: &ScriptFunction,
    metadata: &ModuleFunction,
    evidence: Vec<HiddenEvidenceArgValue>,
    mut arguments: CallArgsStorageGuard,
    runtime: &mut EvalCtx,
) -> EvalResult {
    let arg_count = arguments.args.len();
    assert_eq!(arg_count, script.runtime_arg_count);
    let module = runtime
        .compiler_session()
        .expect_fresh_module(runtime.module_id);
    let arena = &module.hir_arena;
    let span = arena[script.entry_node_id].span;
    let base = runtime.environment.len();
    if base.saturating_add(arg_count) > runtime.environment_cell_limit {
        return Err(runtime.environment_cell_limit_error(Some(span)));
    }
    let frame = HirFrame::for_call(function, base, metadata, &evidence);
    runtime.environment.extend(arguments.take());
    runtime.call_depth += 1;
    let mut interpreter = HirInterpreter::new(runtime, frame);
    let result = match eval_node_with_ctx(
        arena,
        script.entry_node_id,
        &mut interpreter,
        &metadata.locals,
    ) {
        Ok(flow) => Ok(flow),
        Err(error) => Err(interpreter.cleanup_after_error(error, |interpreter| {
            drop_frame_owned_locals_on_error(interpreter, &metadata.locals, span)
        })),
    };
    interpreter.runtime.call_depth -= 1;
    if result.is_ok() {
        let expected = base + arg_count;
        if interpreter.runtime.environment.len() > expected
            && interpreter.runtime.environment[expected..]
                .iter()
                .all(|entry| matches!(entry, ValOrMut::Val(Value::Uninit)))
        {
            interpreter.runtime.truncate_environment_storage(expected);
        }
        assert_eq!(interpreter.runtime.environment.len(), expected);
    }
    interpreter.runtime.truncate_environment_storage(base);
    result.map(ControlFlow::into_value)
}

struct HirInterpreter<'run, 'session> {
    runtime: &'run mut EvalCtx<'session>,
    frame: HirFrame,
}

impl<'run, 'session> HirInterpreter<'run, 'session> {
    fn new(runtime: &'run mut EvalCtx<'session>, frame: HirFrame) -> Self {
        Self { runtime, frame }
    }

    #[cfg(test)]
    fn root(runtime: &'run mut EvalCtx<'session>) -> Self {
        Self::new(
            runtime,
            HirFrame {
                environment_base: 0,
                evidence: Vec::new(),
                returns_place: false,
            },
        )
    }

    fn reserve_current_frame_slots(&mut self, locals: &[LocalDecl]) {
        if let Some(max_slot) = locals.iter().map(|local| local.slot.as_index()).max() {
            self.runtime
                .ensure_environment_slot(self.frame.environment_base + max_slot);
        }
    }

    fn assert_no_owned_local_leaks_before_truncate(
        &self,
        locals: &[LocalDecl],
        len: usize,
        span: Location,
    ) {
        #[cfg(debug_assertions)]
        {
            for local in locals.iter().filter(|local| local.owns_storage()) {
                let index = self.frame.environment_base + local.slot.as_index();
                if index < len || index >= self.runtime.environment.len() {
                    continue;
                }
                match &self.runtime.environment[index] {
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

    fn call_function_value(
        &mut self,
        function_value: &FunctionValue,
        arguments: Vec<ValOrMut>,
        location: Location,
    ) -> EvalControlFlowResult {
        let function_id = function_value.function;
        let mut arguments = CallArgsStorageGuard::new(arguments);

        let closure_env_dictionary = function_value
            .closure_env_value_dictionary
            .as_ref()
            .cloned();
        let closure_env_temp = if function_value.closure_env_len == 0 {
            None
        } else {
            let dictionary = closure_env_dictionary
                .clone()
                .expect("closures with captured values must carry a Value dictionary");
            self.runtime
                .check_environment_cell_limit(self.runtime.environment.len(), Some(location))?;
            let closure_env = call_value_clone_for_temp(
                self,
                dictionary,
                ValOrMut::Ref(&function_value.closure_env as *const Value),
                location,
            )?;
            let index = self.runtime.environment.len();
            self.runtime.environment.push(ValOrMut::Val(closure_env));
            Some(index)
        };

        let arguments = if function_value.closure_env_len == 0 {
            arguments.take()
        } else {
            let mut prepared =
                Vec::with_capacity(function_value.closure_env_len + arguments.args.len());
            if let Some(root) = closure_env_temp {
                prepared.extend((0..function_value.closure_env_len).map(|index| {
                    ValOrMut::Mut(Place::Boxed {
                        root,
                        path: vec![index as isize],
                    })
                }));
            }
            prepared.extend(arguments.take());
            prepared
        };

        let result = self.call_function(
            function_id,
            function_value.hidden_args.clone(),
            arguments,
            location,
        );

        if let Some(root) = closure_env_temp {
            let dictionary = closure_env_dictionary
                .clone()
                .expect("closure environment dictionary disappeared");
            let place = Place::Boxed {
                root,
                path: Vec::new(),
            };
            let result = match result {
                Ok(result) => match discard_call_result(call_value_drop_for_temp(
                    self,
                    dictionary,
                    ValOrMut::Mut(place),
                    location,
                )) {
                    Ok(()) => Ok(result),
                    Err(error) => {
                        discard_control_flow_value(result);
                        Err(error)
                    }
                },
                Err(error) => Err(self.cleanup_after_error(error, |ctx| {
                    discard_call_result(call_value_drop_for_temp(
                        ctx,
                        dictionary,
                        ValOrMut::Mut(place),
                        location,
                    ))
                })),
            };
            self.runtime.pop_environment_entry_discard();
            return result;
        }

        result
    }

    fn call_function(
        &mut self,
        function: FunctionId,
        evidence: Vec<HiddenEvidenceArgValue>,
        arguments: Vec<ValOrMut>,
        span: Location,
    ) -> EvalControlFlowResult {
        call_function(function, evidence, arguments, span, self.runtime).map(ControlFlow::Continue)
    }

    /// Runs guest cleanup only for a source failure; after poisoning, callers only reclaim storage.
    fn cleanup_after_error(
        &mut self,
        initial: RuntimeError,
        cleanup: impl FnOnce(&mut Self) -> Result<(), RuntimeError>,
    ) -> RuntimeError {
        if !matches!(initial, RuntimeError::SourceFailure(_)) {
            return self.runtime.record_poisoning_error(initial);
        }
        match cleanup(self) {
            Ok(()) => initial,
            Err(error) => self.runtime.poison(initial, error),
        }
    }

    fn call_resolved_accessor_until_yield_with_extra(
        &mut self,
        function_id: FunctionId,
        extra_arguments: Vec<HiddenEvidenceArgValue>,
        arguments: Vec<ValOrMut>,
        location: Location,
    ) -> Result<(SuspendedAccessor, Place), RuntimeError> {
        self.call_accessor_until_yield(function_id, extra_arguments, arguments)
            .map_err(|err| err.with_frame(function_id, location))
    }

    fn call_accessor_until_yield(
        &mut self,
        function: FunctionId,
        evidence: Vec<HiddenEvidenceArgValue>,
        arguments: Vec<ValOrMut>,
    ) -> Result<(SuspendedAccessor, Place), RuntimeError> {
        let mut arguments = CallArgsStorageGuard::new(arguments);
        self.runtime.ensure_runnable()?;
        if self
            .runtime
            .environment
            .len()
            .saturating_add(arguments.args.len())
            > self.runtime.environment_cell_limit
        {
            return Err(self.runtime.environment_cell_limit_error(None));
        }
        let module = self
            .runtime
            .compiler_session()
            .expect_fresh_module(function.module);
        let metadata = module.get_function_by_id(function.function).unwrap();
        let script = metadata
            .code
            .as_script()
            .expect("yielded accessor must be a script");
        let locals = &metadata.locals;
        let arena = &module.hir_arena;
        let frame = HirFrame::for_call(
            function,
            self.runtime.environment.len(),
            metadata,
            &evidence,
        );
        let base = frame.environment_base;
        let caller_module = mem::replace(&mut self.runtime.module_id, function.module);
        self.runtime.environment.extend(arguments.take());
        self.runtime.call_depth += 1;
        let mut callee = HirInterpreter::new(self.runtime, frame);
        let result = eval_node_with_ctx(arena, script.entry_node_id, &mut callee, locals);
        let result = match result {
            Ok(ControlFlow::Transfer(ControlTransfer::Yield(place))) => Ok((
                SuspendedAccessor {
                    function,
                    frame: callee.frame,
                },
                place,
            )),
            Ok(flow) => {
                discard_control_flow_value(flow);
                callee.runtime.call_depth -= 1;
                callee.runtime.truncate_environment_storage(base);
                callee.runtime.module_id = caller_module;
                panic!("yielded accessor exited without yielding")
            }
            Err(error) => {
                let error = callee.cleanup_after_error(error, |callee| {
                    drop_frame_owned_locals_on_error(
                        callee,
                        locals,
                        arena[script.entry_node_id].span,
                    )
                });
                callee.runtime.call_depth -= 1;
                callee.runtime.truncate_environment_storage(base);
                Err(error)
            }
        };
        self.runtime.module_id = caller_module;
        result
    }

    fn resume_suspended_accessor_epilogue(
        &mut self,
        suspension: SuspendedAccessor,
        location: Location,
    ) -> EvalControlFlowResult {
        let function = suspension.function;
        self.resume_suspended_accessor_epilogue_inner(suspension)
            .map_err(|err| err.with_frame(function, location))
    }

    /// Reclaims a suspended frame's storage after poisoning, without running any more guest cleanup.
    fn abandon_suspended_accessor(&mut self, suspension: SuspendedAccessor) {
        self.runtime.call_depth -= 1;
        self.runtime
            .truncate_environment_storage(suspension.frame.environment_base);
    }

    fn resume_suspended_accessor_epilogue_inner(
        &mut self,
        suspension: SuspendedAccessor,
    ) -> EvalControlFlowResult {
        let module = self
            .runtime
            .compiler_session()
            .expect_fresh_module(suspension.function.module);
        let metadata = module
            .get_function_by_id(suspension.function.function)
            .unwrap();
        let script = metadata
            .code
            .as_script()
            .expect("yielded accessor must be a script");
        let yield_node = script
            .yield_node_id
            .expect("accessor must record its yield node");
        let locals = &metadata.locals;
        let arena = &module.hir_arena;
        let caller_module = mem::replace(&mut self.runtime.module_id, suspension.function.module);
        let base = suspension.frame.environment_base;
        let mut callee = HirInterpreter::new(self.runtime, suspension.frame);
        callee.frame.returns_place = false;
        let result = match eval_epilogue_after_yield(
            arena,
            script.entry_node_id,
            yield_node,
            &mut callee,
            locals,
        ) {
            Ok(flow) => Ok(flow),
            Err(error) => Err(callee.cleanup_after_error(error, |callee| {
                drop_frame_owned_locals_on_error(callee, locals, arena[yield_node].span)
            })),
        };
        self.runtime.call_depth -= 1;
        self.runtime.truncate_environment_storage(base);
        self.runtime.module_id = caller_module;
        result
    }
}

#[derive(Debug)]
struct SuspendedAccessor {
    function: FunctionId,
    frame: HirFrame,
}

#[derive(Debug)]
struct AccessorEpilogue {
    member: AccessorMemberEpilogue,
    cleanup_scopes: Vec<Vec<LocalDeclId>>,
}

#[derive(Debug)]
enum AccessorMemberEpilogue {
    Suspended(SuspendedAccessor),
    None,
}

impl AccessorEpilogue {
    fn suspended(suspension: SuspendedAccessor) -> Self {
        Self {
            member: AccessorMemberEpilogue::Suspended(suspension),
            cleanup_scopes: Vec::new(),
        }
    }

    fn none() -> Self {
        Self {
            member: AccessorMemberEpilogue::None,
            cleanup_scopes: Vec::new(),
        }
    }

    fn push_cleanup_scope(&mut self, cleanup: &[LocalDeclId]) {
        if !cleanup.is_empty() {
            self.cleanup_scopes.push(cleanup.to_vec());
        }
    }
}

#[derive(Debug)]
enum ControlFlow<V> {
    Continue(V),
    Transfer(ControlTransfer),
}

#[derive(Debug)]
enum ControlTransfer {
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
    fn into_value(self) -> Value {
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

type EvalControlFlowResult = Result<ControlFlow<Value>, RuntimeError>;

fn cont(value: Value) -> EvalControlFlowResult {
    Ok(ControlFlow::Continue(value))
}

fn ret(value: Value) -> EvalControlFlowResult {
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
#[cfg(test)]
fn eval_node(
    arena: &ENodeArena,
    node_id: ENodeId,
    module_id: ModuleId,
    locals: &[LocalDecl],
    compiler_session: &CompilerSession,
) -> EvalControlFlowResult {
    let mut runtime = EvalCtx::new(module_id, compiler_session);
    let mut ctx = HirInterpreter::root(&mut runtime);
    eval_node_with_ctx(arena, node_id, &mut ctx, locals)
}

/// Executes a compiled HIR function with ordinary arguments.
pub fn eval_function(
    module: ModuleId,
    function: LocalFunctionId,
    arguments: Vec<ValOrMut>,
    session: &CompilerSession,
) -> EvalResult {
    let mut runtime = EvalCtx::new(module, session);
    eval_function_with_ctx(module, function, arguments, &mut runtime)
}

/// Executes a compiled HIR function in an existing shared runtime.
pub fn eval_function_with_ctx(
    module: ModuleId,
    function: LocalFunctionId,
    arguments: Vec<ValOrMut>,
    runtime: &mut EvalCtx,
) -> EvalResult {
    call_function(
        FunctionId::new(module, function),
        Vec::new(),
        arguments,
        Location::new_synthesized(),
        runtime,
    )
}

/// Evaluate this node given the environment and return the result.
fn eval_node_with_ctx(
    arena: &ENodeArena,
    node_id: ENodeId,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    use NodeKind::*;
    let node = &arena[node_id];
    match &node.kind {
        Immediate(immediate) => cont(immediate.clone().into_value()),
        Uninit => cont(Value::uninit()),
        BuildClosure(build_closure) => eval_build_closure(arena, build_closure, ctx, locals),
        BuildSubscriptValue(build_subscript) => {
            eval_build_subscript_value(arena, build_subscript, ctx, locals)
        }
        FunctionApply(app) => eval_apply(arena, app, node.span, ctx, locals),
        CloneClosureEnv(node) => {
            eval_clone_closure_env(arena, node, arena[node_id].span, ctx, locals)
        }
        DropClosureEnv(node) => {
            eval_drop_closure_env(arena, node, arena[node_id].span, ctx, locals)
        }
        CloneSubscriptValue(node) => {
            eval_clone_subscript_value(arena, node, arena[node_id].span, ctx, locals)
        }
        DropSubscriptValue(node) => eval_drop_subscript_value(arena, node, ctx, locals),
        CloneValue(node) => eval_clone_value(arena, node, arena[node_id].span, ctx, locals),
        DropValue(node) => eval_drop_value(arena, node, arena[node_id].span, ctx, locals),
        StaticApply(app) => eval_static_apply(arena, app, node.span, ctx, locals),
        SubscriptApply(app) => eval_subscript_apply(arena, app, node.span, ctx, locals),
        GetSubscript(get_subscript) => cont(Value::subscript(get_subscript.subscript)),
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
        CheckCallDepth => ctx
            .runtime
            .check_call_depth(node.span)
            .map(|()| ControlFlow::Continue(Value::unit())),
        CheckFuel => ctx
            .runtime
            .check_fuel(node.span)
            .map(|()| ControlFlow::Continue(Value::unit())),
        LoadSubscriptEvidence(node) => cont(Value::subscript_value(
            subscript_from_extra_parameter(ctx, node.extra_parameter),
        )),
        LoadVariantPayloadStorageEvidence(node) => {
            let storage = match extra_parameter_value(ctx, node.extra_parameter) {
                HiddenEvidenceArgValue::VariantPayloadStorage(storage) => storage,
                _ => panic!("variant payload-storage evidence has the wrong runtime shape"),
            };
            cont(Value::native(storage.is_indirect()))
        }
        GetDictionaryFunction(node) => eval_get_dictionary_function(arena, node, ctx),
        CallDictionaryFunction(node) => {
            eval_call_dictionary_function(arena, node, arena[node_id].span, ctx, locals)
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
        PendingAssignment(never) => match *never {},
        Tuple(nodes) | Record(nodes) => eval_tuple(arena, nodes, ctx, locals),
        Project(node) => eval_project(arena, node_id, node.value, node.index, ctx, locals),
        FieldAccess(_) => panic!("field access should not be executed after elaboration"),
        Variant(node) => eval_variant(arena, node, ctx, locals),
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
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let hidden_args = eval_or_return!(eval_hidden_evidence_arg_nodes(
        arena,
        &build_closure.dictionary_captures,
        ctx,
        locals,
    ));
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

#[inline(never)]
fn eval_build_subscript_value(
    arena: &ENodeArena,
    build_subscript: &hir::BuildSubscriptValue<Elaborated>,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let mut captured_hidden_args = eval_or_return!(eval_hidden_evidence_arg_nodes(
        arena,
        &build_subscript.evidence_captures,
        ctx,
        locals,
    ));
    let value = eval_node_with_ctx(arena, build_subscript.subscript, ctx, locals)?.into_value();
    let mut subscript_value = *value.into_subscript().unwrap();
    subscript_value
        .hidden_args
        .append(&mut captured_hidden_args);
    cont(Value::subscript_value(subscript_value))
}

fn eval_hidden_evidence_arg_node(
    arena: &ENodeArena,
    node: ENodeId,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> Result<ControlFlow<HiddenEvidenceArgValue>, RuntimeError> {
    if let NodeKind::LoadSubscriptEvidence(load) = &arena[node].kind {
        return Ok(ControlFlow::Continue(HiddenEvidenceArgValue::Subscript(b(
            subscript_from_extra_parameter(ctx, load.extra_parameter),
        ))));
    }
    if let NodeKind::LoadVariantPayloadStorageEvidence(load) = &arena[node].kind {
        return Ok(ControlFlow::Continue(
            match extra_parameter_value(ctx, load.extra_parameter) {
                HiddenEvidenceArgValue::VariantPayloadStorage(storage) => {
                    HiddenEvidenceArgValue::VariantPayloadStorage(storage)
                }
                _ => panic!("variant payload-storage evidence has the wrong runtime shape"),
            },
        ));
    }
    if let Some(dictionary) = try_dictionary_metadata_node(arena, node, ctx) {
        return Ok(ControlFlow::Continue(
            HiddenEvidenceArgValue::TraitDictionary(dictionary),
        ));
    }
    let value = eval_or_return!(eval_node_with_ctx(arena, node, ctx, locals));
    if let Some(indirect) = value.as_primitive_ty::<bool>() {
        return Ok(ControlFlow::Continue(
            HiddenEvidenceArgValue::VariantPayloadStorage(
                crate::hir::value::VariantPayloadStorage::from_indirect(*indirect),
            ),
        ));
    }
    let Some(subscript) = value.into_subscript() else {
        panic!("expected hidden evidence to be a trait dictionary, subscript, or variant storage");
    };
    Ok(ControlFlow::Continue(HiddenEvidenceArgValue::Subscript(
        subscript,
    )))
}

fn eval_hidden_evidence_arg_nodes(
    arena: &ENodeArena,
    nodes: &[ENodeId],
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> Result<ControlFlow<Vec<HiddenEvidenceArgValue>>, RuntimeError> {
    eval_sequence(
        nodes.iter().copied(),
        nodes.len(),
        |_| {},
        |node| eval_hidden_evidence_arg_node(arena, node, ctx, locals),
    )
}

fn eval_dictionary_metadata_node(
    arena: &ENodeArena,
    node: ENodeId,
    ctx: &mut HirInterpreter<'_, '_>,
) -> Result<ControlFlow<ClosedTraitDictionary>, RuntimeError> {
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
    ctx: &HirInterpreter<'_, '_>,
) -> Option<ClosedTraitDictionary> {
    match &arena[node].kind {
        NodeKind::GetDictionary(get_dict) => {
            let captures = get_dict
                .captures
                .iter()
                .map(|capture| eval_static_evidence_node(arena, *capture, ctx))
                .collect();
            Some(ClosedTraitDictionary {
                definition: TraitDictionaryId::new(
                    get_dict.dictionary.module,
                    get_dict.dictionary.impl_id,
                ),
                captures,
            })
        }
        NodeKind::LoadDictionary(load) => match extra_parameter_value(ctx, load.extra_parameter) {
            HiddenEvidenceArgValue::TraitDictionary(dictionary) => Some(dictionary),
            HiddenEvidenceArgValue::Subscript(_) => {
                panic!("expected dictionary extra parameter")
            }
            HiddenEvidenceArgValue::VariantPayloadStorage(_) => {
                panic!("expected dictionary extra parameter")
            }
        },
        _ => None,
    }
}

fn eval_static_evidence_node(
    arena: &ENodeArena,
    node: ENodeId,
    ctx: &HirInterpreter<'_, '_>,
) -> HiddenEvidenceArgValue {
    match &arena[node].kind {
        NodeKind::GetDictionary(_) | NodeKind::LoadDictionary(_) => {
            HiddenEvidenceArgValue::TraitDictionary(
                try_dictionary_metadata_node(arena, node, ctx)
                    .expect("dictionary evidence node must resolve to a closed dictionary"),
            )
        }
        NodeKind::GetSubscript(get) => {
            HiddenEvidenceArgValue::Subscript(b(SubscriptValue::bare(get.subscript)))
        }
        NodeKind::LoadSubscriptEvidence(load) => HiddenEvidenceArgValue::Subscript(b(
            subscript_from_extra_parameter(ctx, load.extra_parameter),
        )),
        NodeKind::LoadVariantPayloadStorageEvidence(load) => {
            match extra_parameter_value(ctx, load.extra_parameter) {
                HiddenEvidenceArgValue::VariantPayloadStorage(storage) => {
                    HiddenEvidenceArgValue::VariantPayloadStorage(storage)
                }
                _ => panic!("variant payload-storage evidence has the wrong runtime shape"),
            }
        }
        NodeKind::Immediate(value) => HiddenEvidenceArgValue::VariantPayloadStorage(
            crate::hir::value::VariantPayloadStorage::from_indirect(
                *value
                    .as_primitive_ty::<bool>()
                    .expect("static evidence immediate must be a payload-storage boolean"),
            ),
        ),
        other => panic!("unsupported static evidence node: {other:?}"),
    }
}

fn try_dictionary_from_place(
    place: &Place,
    ctx: &HirInterpreter<'_, '_>,
) -> Option<ClosedTraitDictionary> {
    let Place::Boxed { root, path } = place else {
        return None;
    };
    let mut path = path.iter().copied().collect::<VecDeque<_>>();
    let mut index = *root;
    loop {
        match &ctx.runtime.environment[index] {
            ValOrMut::Dictionary(dictionary) => {
                return path.is_empty().then_some(dictionary.clone());
            }
            ValOrMut::Mut(place) => {
                let Place::Boxed {
                    root,
                    path: parent_path,
                } = place
                else {
                    return None;
                };
                index = *root;
                for &index in parent_path.iter().rev() {
                    path.push_front(index);
                }
            }
            ValOrMut::Val(_) | ValOrMut::Ref(_) => return None,
        }
    }
}

fn dictionary_from_extra_parameter(
    ctx: &HirInterpreter<'_, '_>,
    extra_parameter: EvidenceBindingId,
) -> ClosedTraitDictionary {
    match extra_parameter_value(ctx, extra_parameter) {
        HiddenEvidenceArgValue::TraitDictionary(dictionary) => dictionary,
        HiddenEvidenceArgValue::Subscript(_) | HiddenEvidenceArgValue::VariantPayloadStorage(_) => {
            panic!(
                "expected extra parameter {} to contain trait dictionary metadata",
                extra_parameter.as_index()
            )
        }
    }
}

fn subscript_from_extra_parameter(
    ctx: &HirInterpreter<'_, '_>,
    extra_parameter: EvidenceBindingId,
) -> SubscriptValue {
    match extra_parameter_value(ctx, extra_parameter) {
        HiddenEvidenceArgValue::Subscript(subscript) => *subscript,
        HiddenEvidenceArgValue::TraitDictionary(_)
        | HiddenEvidenceArgValue::VariantPayloadStorage(_) => panic!(
            "expected extra parameter {} to contain subscript evidence",
            extra_parameter.as_index()
        ),
    }
}

fn extra_parameter_value(
    ctx: &HirInterpreter<'_, '_>,
    extra_parameter: EvidenceBindingId,
) -> HiddenEvidenceArgValue {
    ctx.frame.evidence[extra_parameter.as_index()].clone()
}

fn materialize_evidence_bindings(
    bindings: &[EvidenceBinding],
    parameters: &[HiddenEvidenceArgValue],
) -> Vec<HiddenEvidenceArgValue> {
    let mut values: Vec<HiddenEvidenceArgValue> = Vec::with_capacity(bindings.len());
    for binding in bindings {
        let value = match &binding.source {
            EvidenceBindingSource::Parameter(parameter) => parameters[parameter.as_index()].clone(),
            EvidenceBindingSource::Static(evidence) => materialize_static_evidence(evidence),
            EvidenceBindingSource::ConstructedDictionary {
                definition,
                captures,
            } => HiddenEvidenceArgValue::TraitDictionary(ClosedTraitDictionary {
                definition: *definition,
                captures: captures
                    .iter()
                    .map(|capture| values[capture.as_index()].clone())
                    .collect(),
            }),
            EvidenceBindingSource::ConstructedSubscript {
                definition,
                captures,
            } => HiddenEvidenceArgValue::Subscript(b(SubscriptValue {
                subscript: *definition,
                hidden_args: captures
                    .iter()
                    .map(|capture| values[capture.as_index()].clone())
                    .collect(),
            })),
        };
        values.push(value);
    }
    values
}

fn materialize_static_evidence(evidence: &StaticEvidence) -> HiddenEvidenceArgValue {
    match evidence {
        StaticEvidence::Dictionary {
            definition,
            captures,
        } => HiddenEvidenceArgValue::TraitDictionary(ClosedTraitDictionary {
            definition: *definition,
            captures: captures.iter().map(materialize_static_evidence).collect(),
        }),
        StaticEvidence::Subscript {
            definition,
            captures,
        } => HiddenEvidenceArgValue::Subscript(b(SubscriptValue {
            subscript: *definition,
            hidden_args: captures.iter().map(materialize_static_evidence).collect(),
        })),
        StaticEvidence::VariantPayloadStorage(indirect) => {
            HiddenEvidenceArgValue::VariantPayloadStorage(
                crate::hir::value::VariantPayloadStorage::from_indirect(*indirect),
            )
        }
    }
}

fn call_dictionary_function(
    ctx: &mut HirInterpreter<'_, '_>,
    dictionary: ClosedTraitDictionary,
    entry_index: TraitDictionaryEntryIndex,
    arguments: Vec<ValOrMut>,
    span: Location,
) -> EvalControlFlowResult {
    let dictionary_definition = ctx.runtime.dictionary_value(&dictionary);
    let TraitDictionaryEntry::Function(function) = dictionary_definition.entry(entry_index);
    let hidden_args = dictionary_definition
        .project_entry_captures(entry_index, &dictionary.captures, || {
            HiddenEvidenceArgValue::TraitDictionary(dictionary.clone())
        })
        .expect("validated dictionary entry capture mapping");
    let function_value = FunctionValue::closure(
        FunctionId::new(dictionary.definition.module_id, function),
        hidden_args,
        Vec::new(),
        None,
    );
    ctx.call_function_value(&function_value, arguments, span)
}

fn eval_get_dictionary_function(
    arena: &ENodeArena,
    node: &hir::GetDictionaryFunction<Elaborated>,
    ctx: &mut HirInterpreter<'_, '_>,
) -> EvalControlFlowResult {
    let dictionary = eval_or_return!(eval_dictionary_metadata_node(arena, node.dictionary, ctx));
    let dictionary_definition = ctx.runtime.dictionary_value(&dictionary);
    let TraitDictionaryEntry::Function(function) = dictionary_definition.entry(node.entry_index);
    let hidden_args = dictionary_definition
        .project_entry_captures(node.entry_index, &dictionary.captures, || {
            HiddenEvidenceArgValue::TraitDictionary(dictionary.clone())
        })
        .expect("validated dictionary entry capture mapping");
    cont(Value::function_value(FunctionValue::closure(
        FunctionId::new(dictionary.definition.module_id, function),
        hidden_args,
        Vec::new(),
        None,
    )))
}

fn eval_call_dictionary_function(
    arena: &ENodeArena,
    node: &hir::CallDictionaryFunction<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    eval_call_dictionary_function_with(arena, node, span, ctx, locals, eval_args)
}

fn eval_addressor_place_call_dictionary_function(
    arena: &ENodeArena,
    node: &hir::CallDictionaryFunction<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    eval_call_dictionary_function_with(arena, node, span, ctx, locals, eval_addressor_place_args)
}

fn eval_call_dictionary_function_with(
    arena: &ENodeArena,
    node: &hir::CallDictionaryFunction<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
    eval_args_fn: EvalArgsFn,
) -> EvalControlFlowResult {
    let dictionary = eval_or_return!(eval_dictionary_metadata_node(arena, node.dictionary, ctx));
    let temp_start = ctx.runtime.environment.len();
    let mut arguments = eval_or_return!(eval_args_fn(
        arena,
        &node.arguments,
        &node.ty.fn_ty.args,
        ctx,
        locals,
    ));
    let result = call_dictionary_function(
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
    ctx: &mut HirInterpreter<'_, '_>,
    dispatch: ResolvedValueMethod,
    method_index: TraitMethodIndex,
    arguments: Vec<ValOrMut>,
    span: Location,
) -> EvalControlFlowResult {
    match dispatch {
        ResolvedValueMethod::Static(function) => {
            ctx.call_function(function, Vec::new(), arguments, span)
        }
        ResolvedValueMethod::Dictionary(dict_index) => {
            let dictionary = dictionary_from_extra_parameter(ctx, dict_index);
            call_dictionary_function(
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
    Dictionary(EvidenceBindingId),
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
    ctx: &mut HirInterpreter<'_, '_>,
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

/// Attempts a local's semantic drop and ends the target lifetime even if execution aborts.
///
/// Once a drop action starts, the value may be partially destroyed—or a sandbox violation may prevent
/// entry into its drop body—and must never be observed or retried. Reclaiming and invalidating its
/// boxed storage is therefore unconditional; the original drop result is then propagated.
fn drop_local_value_at_place(
    ctx: &mut HirInterpreter<'_, '_>,
    drop: ResolvedLocalDrop,
    target: Place,
    span: Location,
) -> Result<(), RuntimeError> {
    let drop_result = call_local_drop_dispatch(ctx, drop, target.clone(), span);
    let discard_result = discard_value_storage_at_place(ctx, &target, span);
    if drop_result.is_err() {
        debug_assert!(
            discard_result.is_ok(),
            "failed to invalidate a drop target after its semantic drop also failed"
        );
        // The drop's non-returning outcome is primary. In release builds, retain it even if the
        // interpreter also failed to address the target for invalidation.
        drop_result
    } else {
        discard_result
    }
}

/// Drops `target` through the resolved `Value::drop` dispatch when its storage is initialized.
fn drop_value_at_place_if_initialized(
    ctx: &mut HirInterpreter<'_, '_>,
    drop: ResolvedLocalDrop,
    target: Place,
    span: Location,
) -> Result<(), RuntimeError> {
    if place_contains_uninit(ctx, &target, span)? {
        return Ok(());
    }
    drop_local_value_at_place(ctx, drop, target, span)
}

fn resolved_local_drop(drop: &ResolvedLocalDrop) -> ResolvedLocalDrop {
    *drop
}

fn resolved_local_clone(clone: &ResolvedLocalClone) -> ResolvedLocalClone {
    *clone
}

fn drop_frame_owned_locals_on_error(
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
    span: Location,
) -> Result<(), RuntimeError> {
    drop_owned_locals_on_error_from(ctx, locals, ctx.frame.environment_base, span)
}

fn drop_owned_locals_on_error_from(
    ctx: &mut HirInterpreter<'_, '_>,
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
        if target_index >= ctx.runtime.environment.len() {
            continue;
        }
        let target = local_place(ctx, locals, id);
        drop_value_at_place_if_initialized(ctx, resolved_local_drop(drop), target, span)?;
    }
    Ok(())
}

fn call_value_clone_with(
    ctx: &mut HirInterpreter<'_, '_>,
    source: ValOrMut,
    _span: Location,
    call: impl FnOnce(&mut HirInterpreter<'_, '_>, Vec<ValOrMut>) -> EvalControlFlowResult,
) -> Result<Value, RuntimeError> {
    Ok(call(ctx, vec![source])?.into_value())
}

fn call_value_clone_for_temp(
    ctx: &mut HirInterpreter<'_, '_>,
    dictionary: ClosedTraitDictionary,
    source: ValOrMut,
    span: Location,
) -> Result<Value, RuntimeError> {
    call_value_clone_with(ctx, source, span, |ctx, arguments| {
        call_dictionary_function(
            ctx,
            dictionary,
            TraitDictionaryEntryIndex::from_index(VALUE_CLONE_METHOD_INDEX.as_index()),
            arguments,
            span,
        )
    })
}

fn call_value_clone_dispatch_for_temp(
    ctx: &mut HirInterpreter<'_, '_>,
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

fn call_value_drop_for_temp(
    ctx: &mut HirInterpreter<'_, '_>,
    dictionary: ClosedTraitDictionary,
    target: ValOrMut,
    span: Location,
) -> EvalControlFlowResult {
    let (target_place, temp_index) = match target {
        ValOrMut::Mut(place) => (place, None),
        ValOrMut::Ref(_) => panic!("cannot drop shared reference storage"),
        ValOrMut::Dictionary(_) => panic!("cannot drop trait dictionary metadata as a Value"),
        ValOrMut::Val(value) => {
            let target_index = ctx.runtime.environment.len();
            if let Err(error) = ctx
                .runtime
                .check_environment_cell_limit(target_index, Some(span))
            {
                value.discard_storage();
                return Err(error);
            }
            ctx.runtime.environment.push(ValOrMut::Val(value));
            let place = Place::Boxed {
                root: target_index,
                path: Vec::new(),
            };
            (place, Some(target_index))
        }
    };
    let result = discard_call_result(call_dictionary_function(
        ctx,
        dictionary,
        TraitDictionaryEntryIndex::from_index(VALUE_DROP_METHOD_INDEX.as_index()),
        vec![ValOrMut::Mut(target_place.clone())],
        span,
    ));
    if result.is_ok() {
        discard_value_storage_at_place(ctx, &target_place, span)?;
    }
    if let Some(target_index) = temp_index {
        let value = ctx.runtime.pop_environment_entry().unwrap();
        debug_assert_eq!(target_index, ctx.runtime.environment.len());
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
    ctx: &mut HirInterpreter<'_, '_>,
    place: &Place,
    span: Location,
) -> Result<(), RuntimeError> {
    let target = place
        .boxed_mut(ctx.runtime)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    let value = mem::replace(target, Value::uninit());
    value.discard_storage();
    Ok(())
}

fn replace_value_storage_at_place(
    ctx: &mut HirInterpreter<'_, '_>,
    place: &Place,
    value: Value,
    span: Location,
) -> Result<(), RuntimeError> {
    let old_value = place
        .replace_value(ctx.runtime, value)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    old_value.discard_storage();
    Ok(())
}

fn place_contains_uninit(
    ctx: &HirInterpreter<'_, '_>,
    place: &Place,
    span: Location,
) -> Result<bool, RuntimeError> {
    let target = place
        .target_ref_if_materialized(ctx.runtime)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    Ok(target.is_none_or(ValueRef::is_uninit))
}

fn local_environment_index(
    ctx: &HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
    id: LocalDeclId,
) -> usize {
    ctx.frame.environment_base + locals[id.as_index()].slot.as_index()
}

fn local_place(ctx: &HirInterpreter<'_, '_>, locals: &[LocalDecl], id: LocalDeclId) -> Place {
    Place::Boxed {
        root: local_environment_index(ctx, locals, id),
        path: Vec::new(),
    }
}

#[inline(never)]
fn eval_clone_closure_env(
    arena: &ENodeArena,
    node: &hir::CloneClosureEnv<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let owned_source;
    let source_place;
    let (function, hidden_args, closure_env_ptr, closure_env_len, closure_env_value_dictionary) = {
        let source = if let Some(place) =
            eval_or_return!(try_eval_node_as_place(arena, node.source, ctx, locals))
        {
            source_place = place;
            source_place
                .target_ref(ctx.runtime)
                .map_err(|err| RuntimeError::new(err, Some(span)))?
                .as_boxed()
                .expect("callable requires boxed storage")
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
            source.closure_env_value_dictionary.clone(),
        )
    };
    let closure_env = if let Some(dictionary) = closure_env_value_dictionary.clone() {
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
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let target = eval_or_return!(eval_node_as_place(arena, node.target, ctx, locals));
    let captured_env = {
        let target = target
            .boxed_mut(ctx.runtime)
            .map_err(|err| RuntimeError::new(err, Some(span)))?;
        let function = target.as_function_mut().unwrap();
        let dictionary = function.closure_env_value_dictionary.clone();
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
fn eval_clone_subscript_value(
    arena: &ENodeArena,
    node: &hir::CloneSubscriptValue<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    cont(Value::subscript_value(eval_or_return!(
        eval_subscript_value(arena, node.source, span, ctx, locals)
    )))
}

#[inline(never)]
fn eval_drop_subscript_value(
    arena: &ENodeArena,
    node: &hir::DropSubscriptValue<Elaborated>,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let target = eval_or_return!(eval_node_as_place(arena, node.target, ctx, locals));
    let target = target
        .boxed_mut(ctx.runtime)
        .map_err(|err| RuntimeError::new(err, Some(arena[node.target].span)))?;
    let value = mem::replace(target, Value::uninit());
    value.discard_storage();
    cont(Value::unit())
}

#[inline(never)]
fn eval_clone_value(
    arena: &ENodeArena,
    node: &hir::CloneValue<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let clone = resolved_local_clone(&node.clone);

    if let ResolvedLocalClone::TrivialCopy = clone {
        if node_may_resolve_to_place(arena, node.source) {
            let layout = ctx.runtime.value_layout(arena[node.source].ty, span);
            let temp_start = ctx.runtime.environment.len();
            let place = eval_or_return!(eval_node_as_place(arena, node.source, ctx, locals));
            let result = copy_trivial_copy_value_from_place_layout(
                &place,
                arena[node.source].ty,
                layout,
                ctx,
                span,
            );
            ctx.runtime.truncate_environment_storage(temp_start);
            return cont(result?);
        }
        return eval_node_with_ctx(arena, node.source, ctx, locals);
    }

    let temp_start = ctx.runtime.environment.len();
    let source = match eval_or_return!(try_eval_node_as_place(arena, node.source, ctx, locals)) {
        Some(place) => {
            place
                .target_ref(ctx.runtime)
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
            ctx.runtime.truncate_environment_storage(temp_start);
            Err(err)
        }
    }
}

#[inline(never)]
fn eval_apply(
    arena: &ENodeArena,
    app: &hir::FunctionApplication<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    // Evaluate left-to-right: function first, then arguments (matches Rust semantics).
    let owned_function_value;
    let function_value = if let Some(place) =
        eval_or_return!(try_eval_node_as_place(arena, app.function, ctx, locals))
    {
        let function_value = place
            .target_ref(ctx.runtime)
            .map_err(|err| RuntimeError::new(err, Some(span)))?
            .as_boxed()
            .expect("callable requires boxed storage")
            .as_function()
            .unwrap();
        function_value.as_ref() as *const FunctionValue
    } else {
        owned_function_value =
            eval_or_return!(eval_node_with_ctx(arena, app.function, ctx, locals));
        owned_function_value.as_function().unwrap().as_ref() as *const FunctionValue
    };
    // SAFETY: the pointer either targets `owned_function_value`, kept alive in this stack frame,
    // or environment storage protected for the call lifetime. In the latter case HIR elaboration's
    // `callee_overlaps_argument_writes` snapshots a callee that argument evaluation or an
    // overlapping mutable-reference argument could invalidate.
    let function_value = unsafe { &*function_value };
    // Use the actual callee signature: a dictionary method's surface arguments can still be generic.
    let args_ty = ctx
        .runtime
        .get_module_function(function_value.function)
        .definition
        .ty_scheme
        .ty
        .args
        .clone();
    eval_resolved_runtime_call_with_args(
        arena,
        RuntimeCallArguments::new(&app.arguments, &args_ty, eval_args),
        ResolvedRuntimeCall::FunctionValue(function_value),
        span,
        ctx,
        locals,
    )
}

fn eval_subscript_value<'a>(
    arena: &ENodeArena,
    subscript: ENodeId,
    span: Location,
    ctx: &mut HirInterpreter<'_, 'a>,
    locals: &[LocalDecl],
) -> Result<ControlFlow<SubscriptValue>, RuntimeError> {
    if let Some(place) = eval_or_return!(try_eval_node_as_place(arena, subscript, ctx, locals)) {
        let value = place
            .target_ref(ctx.runtime)
            .map_err(|err| RuntimeError::new(err, Some(span)))?
            .as_boxed()
            .expect("callable requires boxed storage")
            .as_subscript()
            .unwrap();
        return Ok(ControlFlow::Continue((**value).clone()));
    }
    let value = eval_or_return!(eval_node_with_ctx(arena, subscript, ctx, locals));
    Ok(ControlFlow::Continue(*value.into_subscript().unwrap()))
}

fn eval_subscript_apply_with(
    arena: &ENodeArena,
    app: &hir::SubscriptApplication<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
    eval_args_fn: EvalArgsFn,
) -> EvalControlFlowResult {
    let subscript_value = eval_or_return!(eval_subscript_value(
        arena,
        app.subscript,
        span,
        ctx,
        locals
    ));
    let SubscriptValue {
        subscript,
        hidden_args,
    } = subscript_value;
    let call = ResolvedRuntimeCall::FunctionId {
        function: ctx
            .runtime
            .subscript_member_function(subscript, app.mut_member),
        extra_arguments: hidden_args,
    };
    eval_resolved_runtime_call_with_args(
        arena,
        RuntimeCallArguments::new(&app.arguments, &app.ty.fn_ty.args, eval_args_fn),
        call,
        span,
        ctx,
        locals,
    )
}

#[inline(never)]
fn eval_subscript_apply(
    arena: &ENodeArena,
    app: &hir::SubscriptApplication<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    eval_subscript_apply_with(arena, app, span, ctx, locals, eval_args)
}

fn eval_addressor_place_subscript_apply(
    arena: &ENodeArena,
    app: &hir::SubscriptApplication<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    eval_subscript_apply_with(arena, app, span, ctx, locals, eval_addressor_place_args)
}

#[inline(never)]
fn eval_static_apply(
    arena: &ENodeArena,
    app: &hir::StaticApplication<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    eval_static_apply_with(arena, app, span, ctx, locals, eval_args)
}

fn eval_addressor_place_static_apply(
    arena: &ENodeArena,
    app: &hir::StaticApplication<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    eval_static_apply_with(arena, app, span, ctx, locals, eval_addressor_place_args)
}

/// Strategy for evaluating a static call's visible arguments into a [`PreparedCallArgs`].
type EvalArgsFn = fn(
    &ENodeArena,
    &[CallArgument<Elaborated>],
    &[FnArgType],
    &mut HirInterpreter<'_, '_>,
    &[LocalDecl],
) -> Result<ControlFlow<PreparedCallArgs>, RuntimeError>;

fn eval_static_apply_with(
    arena: &ENodeArena,
    app: &hir::StaticApplication<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
    eval_args_fn: EvalArgsFn,
) -> EvalControlFlowResult {
    let extra_arguments = eval_or_return!(eval_hidden_evidence_arg_nodes(
        arena,
        &app.extra_arguments,
        ctx,
        locals,
    ));
    eval_resolved_runtime_call_with_args(
        arena,
        RuntimeCallArguments::new(&app.arguments, &app.ty.fn_ty.args, eval_args_fn),
        ResolvedRuntimeCall::FunctionId {
            function: app.function,
            extra_arguments,
        },
        span,
        ctx,
        locals,
    )
}

enum ResolvedRuntimeCall<'a> {
    FunctionValue(&'a FunctionValue),
    FunctionId {
        function: FunctionId,
        extra_arguments: Vec<HiddenEvidenceArgValue>,
    },
}

impl ResolvedRuntimeCall<'_> {
    fn call(
        self,
        ctx: &mut HirInterpreter<'_, '_>,
        arguments: Vec<ValOrMut>,
        span: Location,
    ) -> EvalControlFlowResult {
        match self {
            Self::FunctionValue(function_value) => {
                ctx.call_function_value(function_value, arguments, span)
            }
            Self::FunctionId {
                function,
                extra_arguments,
            } => ctx.call_function(function, extra_arguments, arguments, span),
        }
    }

    fn call_accessor_until_yield(
        self,
        ctx: &mut HirInterpreter<'_, '_>,
        arguments: Vec<ValOrMut>,
        span: Location,
    ) -> Result<(SuspendedAccessor, Place), RuntimeError> {
        match self {
            Self::FunctionValue(_) => panic!("first-class function value is not an accessor call"),
            Self::FunctionId {
                function,
                extra_arguments,
            } => ctx.call_resolved_accessor_until_yield_with_extra(
                function,
                extra_arguments,
                arguments,
                span,
            ),
        }
    }
}

struct RuntimeCallArguments<'a> {
    arguments: &'a [CallArgument<Elaborated>],
    arg_tys: &'a [FnArgType],
    eval_args: EvalArgsFn,
}

impl<'a> RuntimeCallArguments<'a> {
    fn new(
        arguments: &'a [CallArgument<Elaborated>],
        arg_tys: &'a [FnArgType],
        eval_args: EvalArgsFn,
    ) -> Self {
        Self {
            arguments,
            arg_tys,
            eval_args,
        }
    }
}

fn eval_resolved_runtime_call_with_args(
    arena: &ENodeArena,
    arguments: RuntimeCallArguments<'_>,
    call: ResolvedRuntimeCall<'_>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    // Argument evaluation may initialize explicit caller-frame temporaries. Reserve the
    // whole frame before recording the interpreter-only scratch boundary so post-call
    // truncation cannot discard a HIR-owned local before its block cleanup runs.
    ctx.reserve_current_frame_slots(locals);
    let temp_start = ctx.runtime.environment.len();
    let mut arguments = eval_or_return!((arguments.eval_args)(
        arena,
        arguments.arguments,
        arguments.arg_tys,
        ctx,
        locals
    ));
    let result = call.call(ctx, arguments.take_arguments(), span);
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
    ctx: &mut HirInterpreter<'_, '_>,
    temp_start: usize,
    result: EvalControlFlowResult,
) -> EvalControlFlowResult {
    ctx.runtime.truncate_environment_storage(temp_start);
    result
}

fn eval_addressor_place_args(
    arena: &ENodeArena,
    args: &[CallArgument<Elaborated>],
    args_ty: &[FnArgType],
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> Result<ControlFlow<PreparedCallArgs>, RuntimeError> {
    assert_eq!(args.len(), args_ty.len());
    let results = eval_or_return!(eval_sequence(
        args.iter(),
        args.len(),
        ValOrMut::discard_storage,
        |arg| eval_call_arg(arena, arg.value, arg.passing, ctx, locals),
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
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let local = &locals[node.id.as_index()];
    ctx.runtime
        .check_environment_cell_limit(ctx.runtime.environment.len(), Some(span))?;
    let target_index = local_environment_index(ctx, locals, node.id);
    ctx.runtime
        .check_environment_cell_limit(target_index, Some(span))?;
    if let Some(clone) = &local.clone {
        ctx.runtime.ensure_environment_slot(target_index);
        let clone = resolved_local_clone(clone);
        if let ResolvedLocalClone::TrivialCopy = clone {
            let value =
                match eval_or_return!(try_eval_node_as_place(arena, node.value, ctx, locals)) {
                    Some(place) => {
                        let layout = ctx.runtime.value_layout(local.ty, span);
                        copy_trivial_copy_value_from_place_layout(
                            &place, local.ty, layout, ctx, span,
                        )?
                    }
                    None => eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals)),
                };
            ctx.runtime.environment[target_index] = ValOrMut::Val(value);
            return cont(Value::unit());
        }
        let source = match eval_or_return!(try_eval_node_as_place(arena, node.value, ctx, locals)) {
            Some(place) => {
                place
                    .target_ref(ctx.runtime)
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
        ctx.runtime.environment[target_index] = ValOrMut::Val(value);
    } else if !local.owns_storage() {
        let entry = match eval_or_return!(try_eval_node_as_place(arena, node.value, ctx, locals)) {
            Some(place) => {
                if let Some(dictionary) = try_dictionary_from_place(&place, ctx) {
                    ValOrMut::Dictionary(dictionary)
                } else if let Some(value) =
                    try_copy_trivial_copy_value_from_place(&place, ctx, span)?
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
        ctx.runtime.set_environment_entry(target_index, entry);
    } else {
        let entry = if is_dictionary_metadata_node(arena, node.value) {
            let dictionary = eval_or_return!(eval_dictionary_metadata_node(arena, node.value, ctx));
            ValOrMut::Dictionary(dictionary)
        } else {
            let value = eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals));
            ValOrMut::Val(value)
        };
        ctx.runtime.set_environment_entry(target_index, entry);
    }
    cont(Value::unit())
}

#[inline(never)]
fn take_owned_local_value(
    id: LocalDeclId,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let index = local_environment_index(ctx, locals, id);
    match mem::replace(
        &mut ctx.runtime.environment[index],
        ValOrMut::Val(Value::uninit()),
    ) {
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
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    match node.mode {
        ResolvedTakeLocalValueMode::MoveOwned => take_owned_local_value(node.id, ctx, locals),
        ResolvedTakeLocalValueMode::CloneBorrowed(ResolvedLocalClone::TrivialCopy) => {
            let local = &locals[node.id.as_index()];
            let layout = ctx.runtime.value_layout(local.ty, span);
            let place = local_place(ctx, locals, node.id);
            cont(copy_trivial_copy_value_from_place_layout(
                &place, local.ty, layout, ctx, span,
            )?)
        }
        ResolvedTakeLocalValueMode::CloneBorrowed(clone) => {
            let place = local_place(ctx, locals, node.id);
            place
                .target_ref(ctx.runtime)
                .map_err(|err| RuntimeError::new(err, Some(span)))?;
            let value =
                call_value_clone_dispatch_for_temp(ctx, &clone, ValOrMut::Mut(place), span)?;
            cont(value)
        }
    }
}

/// Simulate a representation copy in the boxed interpreter.
///
/// Tuple boxes are rebuilt recursively, while native leaves are copied only
/// through the sealed Rust `TrivialCopy` opt-ins above. Named records and tuples
/// use the same boxed tuple representation. This deliberately does not call
/// `Value::clone`; an unsupported value indicates that HIR or the structural
/// classifier incorrectly selected `ResolvedLocalClone::TrivialCopy`.
///
/// A variant is rebuilt from its tag and a recursive representation copy of its inline payload.
/// The fresh host box is only an interpreter implementation detail.
fn copy_boxed_trivial_copy_representation<'a>(value: impl Into<ValueRef<'a>>) -> Option<Value> {
    let value = value.into();
    if let Some(value) = copy_boxed_trivial_copy_native(value) {
        return Some(value);
    }
    let value = value.as_boxed()?;
    if let Some(tag) = value.variant_tag() {
        let storage = value.variant_payload_storage().unwrap();
        return Some(match value.variant_payload() {
            None => Value::variant_shell(tag, storage),
            Some(Value::Uninit) => Value::variant_with_storage(tag, storage, Value::uninit()),
            Some(payload) => Value::variant_with_storage(
                tag,
                storage,
                copy_boxed_trivial_copy_representation(payload)?,
            ),
        });
    }
    let values = value.as_tuple()?;
    Some(Value::tuple(
        values
            .iter()
            .map(copy_boxed_trivial_copy_representation)
            .collect::<Option<Vec<_>>>()?,
    ))
}

fn copy_trivial_copy_value_from_place(
    place: &Place,
    ty: Type,
    ctx: &HirInterpreter<'_, '_>,
    span: Location,
) -> Result<Value, RuntimeError> {
    let value = place
        .target_ref(ctx.runtime)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    copy_boxed_trivial_copy_representation(value).ok_or_else(|| {
        panic!(
            "attempted to materialize non-TrivialCopy local value without Value::clone: type {:?}, place {:?}, span {:?}",
            ty, place, span
        );
    })
}

fn copy_trivial_copy_value_from_place_layout(
    place: &Place,
    ty: Type,
    layout: ResolvedValueLayout,
    ctx: &HirInterpreter<'_, '_>,
    span: Location,
) -> Result<Value, RuntimeError> {
    let value = place
        .target_ref(ctx.runtime)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    copy_boxed_trivial_copy_representation(value).ok_or_else(|| {
        panic!(
            "attempted to materialize TrivialCopy local value of type {:?} with layout {:?}, place {:?}",
            ty, layout, place
        );
    })
}

fn try_copy_trivial_copy_value_from_place(
    place: &Place,
    ctx: &HirInterpreter<'_, '_>,
    span: Location,
) -> Result<Option<Value>, RuntimeError> {
    // Opportunistic native-leaf bridge for place evaluation. Structural copies
    // are represented explicitly by `CloneValue` and use the recursive helper.
    let value = place
        .target_ref(ctx.runtime)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    Ok(copy_boxed_trivial_copy_native(value))
}

#[inline(never)]
fn eval_load_local(
    arena: &ENodeArena,
    node_id: ENodeId,
    node: &hir::LoadLocal,
    ctx: &mut HirInterpreter<'_, '_>,
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
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    if ctx.frame.returns_place {
        let place = match eval_node_as_place(arena, node, ctx, locals)? {
            ControlFlow::Continue(place) => place,
            transfer => return Ok(transfer.map_continue(unreachable_continue)),
        };
        let place = place.resolved(ctx.runtime);
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
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let place = match eval_node_as_place(arena, node, ctx, locals)? {
        ControlFlow::Continue(place) => place.resolved(ctx.runtime),
        transfer => return Ok(transfer.map_continue(unreachable_continue)),
    };
    Ok(ControlFlow::Transfer(ControlTransfer::Yield(place)))
}

#[inline(never)]
fn eval_with_yielded(
    arena: &ENodeArena,
    node: &hir::WithYielded<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    ctx.reserve_current_frame_slots(locals);
    let temp_start = ctx.runtime.environment.len();
    let (epilogue, yielded_place) = eval_or_return!(eval_accessor_until_yield(
        arena,
        node.accessor,
        span,
        ctx,
        locals
    ));

    let binding_index = local_environment_index(ctx, locals, node.binding);
    ctx.runtime
        .set_environment_entry(binding_index, ValOrMut::Mut(yielded_place));
    let body_result = eval_node_with_ctx(arena, node.body, ctx, locals);
    ctx.runtime
        .set_environment_entry(binding_index, ValOrMut::Val(Value::uninit()));

    let body_poisoned_executor = body_result.as_ref().is_err_and(RuntimeError::is_poisoning);
    let mut epilogue_result = if body_poisoned_executor {
        if let AccessorMemberEpilogue::Suspended(suspension) = epilogue.member {
            ctx.abandon_suspended_accessor(suspension);
        }
        cont(Value::unit())
    } else {
        match epilogue.member {
            AccessorMemberEpilogue::Suspended(suspension) => {
                ctx.resume_suspended_accessor_epilogue(suspension, span)
            }
            AccessorMemberEpilogue::None => cont(Value::unit()),
        }
    };
    let cleanup_scopes = epilogue.cleanup_scopes;
    epilogue_result = match epilogue_result {
        // The accessor argument temporaries are pending cleanup after a successful slide.
        Ok(result) if !body_poisoned_executor => {
            drop_accessor_cleanup_scopes(ctx, locals, &cleanup_scopes, span).map(|()| result)
        }
        // A slide failure after a successful body is the primary source failure. Continue its
        // unwind through the accessor argument temporaries; a failure there poisons execution.
        Err(err) if body_result.is_ok() && !err.is_poisoning() => Err(ctx
            .cleanup_after_error(err, |ctx| {
                drop_accessor_cleanup_scopes(ctx, locals, &cleanup_scopes, span)
            })),
        result => result,
    };
    ctx.runtime.truncate_environment_storage(temp_start);
    combine_with_yielded_body_and_epilogue(ctx, body_result, epilogue_result)
}

/// Drops the temporary-owning block scopes wrapped around an accessor, innermost first.
///
/// Their actions are `Value::drop` calls and therefore source-infallible. A sandbox violation stops
/// semantic cleanup; the subsequent environment truncation still reclaims their backing storage.
fn drop_accessor_cleanup_scopes(
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
    cleanup_scopes: &[Vec<LocalDeclId>],
    span: Location,
) -> Result<(), RuntimeError> {
    for cleanup in cleanup_scopes {
        drop_cleanup_locals(ctx, locals, cleanup, span)?;
    }
    Ok(())
}

fn eval_accessor_until_yield(
    arena: &ENodeArena,
    accessor: ENodeId,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> Result<ControlFlow<(AccessorEpilogue, Place)>, RuntimeError> {
    if let NodeKind::Block(block) = &arena[accessor].kind {
        return eval_block_accessor_until_yield(arena, block, span, ctx, locals);
    }

    enum AccessorCall<'a> {
        Static(&'a hir::StaticApplication<Elaborated>),
        Subscript(&'a hir::SubscriptApplication<Elaborated>),
    }

    let call = match &arena[accessor].kind {
        NodeKind::StaticApply(app) => AccessorCall::Static(app),
        NodeKind::SubscriptApply(app) => AccessorCall::Subscript(app),
        _ => panic!("WithYielded accessor must be an accessor call"),
    };
    let temp_start = ctx.runtime.environment.len();
    let (call, result_convention, arguments, arg_tys) = match call {
        AccessorCall::Static(app) => {
            let extra_arguments =
                match eval_hidden_evidence_arg_nodes(arena, &app.extra_arguments, ctx, locals)? {
                    ControlFlow::Continue(arguments) => arguments,
                    ControlFlow::Transfer(transfer) => {
                        ctx.runtime.truncate_environment_storage(temp_start);
                        return Ok(ControlFlow::Transfer(transfer));
                    }
                };
            (
                ResolvedRuntimeCall::FunctionId {
                    function: app.function,
                    extra_arguments,
                },
                app.ty.result_convention,
                &app.arguments,
                &app.ty.fn_ty.args,
            )
        }
        AccessorCall::Subscript(app) => {
            let subscript_value =
                match eval_subscript_value(arena, app.subscript, span, ctx, locals)? {
                    ControlFlow::Continue(value) => value,
                    ControlFlow::Transfer(transfer) => {
                        ctx.runtime.truncate_environment_storage(temp_start);
                        return Ok(ControlFlow::Transfer(transfer));
                    }
                };
            let function = ctx
                .runtime
                .subscript_member_function(subscript_value.subscript, app.mut_member);
            (
                ResolvedRuntimeCall::FunctionId {
                    function,
                    extra_arguments: subscript_value.hidden_args,
                },
                ctx.runtime
                    .get_module_function(function)
                    .definition
                    .return_convention(),
                &app.arguments,
                &app.ty.fn_ty.args,
            )
        }
    };
    let eval_args_fn = if result_convention.returns_place() {
        eval_addressor_place_args
    } else {
        eval_args
    };
    let mut arguments = match eval_args_fn(arena, arguments, arg_tys, ctx, locals)? {
        ControlFlow::Continue(arguments) => arguments,
        ControlFlow::Transfer(transfer) => {
            ctx.runtime.truncate_environment_storage(temp_start);
            return Ok(ControlFlow::Transfer(transfer));
        }
    };
    if result_convention.returns_place() {
        let result = call.call(ctx, arguments.take_arguments(), span);
        ctx.runtime.truncate_environment_storage(temp_start);
        return Ok(control_flow_into_addressor_place(result?)
            .map_continue(|place| (AccessorEpilogue::none(), place)));
    }
    match call.call_accessor_until_yield(ctx, arguments.take_arguments(), span) {
        Ok((suspension, place)) => Ok(ControlFlow::Continue((
            AccessorEpilogue::suspended(suspension),
            place,
        ))),
        Err(err) => {
            ctx.runtime.truncate_environment_storage(temp_start);
            Err(err)
        }
    }
}

fn eval_block_accessor_until_yield(
    arena: &ENodeArena,
    block: &hir::Block<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> Result<ControlFlow<(AccessorEpilogue, Place)>, RuntimeError> {
    let Some((&tail, prefix)) = block.body.split_last() else {
        panic!("WithYielded accessor block must contain an accessor call");
    };
    let env_size = ctx.runtime.environment.len();
    for node in prefix {
        match eval_node_with_ctx(arena, *node, ctx, locals) {
            Ok(ControlFlow::Continue(value)) => value.discard_storage(),
            Ok(transfer) => {
                if let Err(err) =
                    drop_cleanup_locals(ctx, locals, &block.cleanup, arena[*node].span)
                {
                    ctx.runtime.truncate_environment_storage(env_size);
                    return Err(err);
                }
                ctx.runtime.truncate_environment_storage(env_size);
                return Ok(transfer.map_continue(unreachable_continue));
            }
            Err(err) => {
                let err = ctx.cleanup_after_error(err, |ctx| {
                    drop_cleanup_locals(ctx, locals, &block.cleanup, arena[*node].span)
                });
                ctx.runtime.truncate_environment_storage(env_size);
                return Err(err);
            }
        }
    }

    match eval_accessor_until_yield(arena, tail, span, ctx, locals)? {
        ControlFlow::Continue((mut epilogue, place)) => {
            epilogue.push_cleanup_scope(&block.cleanup);
            Ok(ControlFlow::Continue((epilogue, place)))
        }
        ControlFlow::Transfer(transfer) => {
            if let Err(err) = drop_cleanup_locals(ctx, locals, &block.cleanup, arena[tail].span) {
                ctx.runtime.truncate_environment_storage(env_size);
                return Err(err);
            }
            ctx.runtime.truncate_environment_storage(env_size);
            Ok(ControlFlow::Transfer(transfer))
        }
    }
}

fn combine_with_yielded_body_and_epilogue(
    ctx: &mut HirInterpreter<'_, '_>,
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
        (Err(body_err), Err(epilogue_err)) => Err(ctx.runtime.poison(body_err, epilogue_err)),
    }
}

#[inline(never)]
fn eval_with_place(
    arena: &ENodeArena,
    node: &hir::WithPlace<Elaborated>,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    eval_with_bound_place(arena, node, ctx, locals, |ctx| {
        eval_node_with_ctx(arena, node.body, ctx, locals)
    })
}

fn eval_with_bound_place<T>(
    arena: &ENodeArena,
    node: &hir::WithPlace<Elaborated>,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
    body: impl FnOnce(&mut HirInterpreter<'_, '_>) -> Result<ControlFlow<T>, RuntimeError>,
) -> Result<ControlFlow<T>, RuntimeError> {
    ctx.reserve_current_frame_slots(locals);
    let temp_start = ctx.runtime.environment.len();
    let place = match try_eval_node_as_place(arena, node.place, ctx, locals)? {
        ControlFlow::Continue(Some(place)) => place,
        ControlFlow::Continue(None) => {
            panic!("WithPlace input must evaluate to a place");
        }
        ControlFlow::Transfer(transfer) => return Ok(ControlFlow::Transfer(transfer)),
    };

    let binding_index = local_environment_index(ctx, locals, node.binding);
    ctx.runtime
        .set_environment_entry(binding_index, ValOrMut::Mut(place));
    let body_result = body(ctx);
    ctx.runtime
        .set_environment_entry(binding_index, ValOrMut::Val(Value::uninit()));
    ctx.runtime.truncate_environment_storage(temp_start);
    body_result
}

#[inline(never)]
fn try_eval_with_place_as_place(
    arena: &ENodeArena,
    node: &hir::WithPlace<Elaborated>,
    ctx: &mut HirInterpreter<'_, '_>,
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
                    place.map(|place| place.resolved(ctx.runtime)),
                )),
                ControlFlow::Transfer(transfer) => Ok(ControlFlow::Transfer(transfer)),
            },
        );
    if let Ok(ControlFlow::Continue(None)) = body_result {
        panic!(
            "WithPlace body must evaluate to a place: place_kind {:?}, body_kind {:?}, body_ty {:?}, body_span {:?}",
            arena[node.place].kind,
            arena[node.body].kind,
            arena[node.body].ty,
            arena[node.body].span
        );
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
    ctx: &mut HirInterpreter<'_, '_>,
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
    ctx: &mut HirInterpreter<'_, '_>,
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
                let err = ctx.cleanup_after_error(err, |ctx| {
                    drop_cleanup_locals(ctx, locals, &block.cleanup, arena[yield_container].span)
                });
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
                let err = ctx.cleanup_after_error(err, |ctx| {
                    drop_cleanup_locals(ctx, locals, &block.cleanup, arena[*node].span)
                });
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
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    if !block.cleanup.is_empty() {
        return eval_block_with_cleanup(arena, &block.body, ctx, locals, &block.cleanup);
    }
    let nodes = &block.body;
    let env_size = ctx.runtime.environment.len();
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
                ctx.runtime.truncate_environment_storage(env_size);
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
                ctx.runtime.truncate_environment_storage(env_size);
                return Ok(transfer);
            }
        }
    }
    let span = nodes
        .last()
        .map(|node| arena[*node].span)
        .unwrap_or_else(Location::new_synthesized);
    ctx.assert_no_owned_local_leaks_before_truncate(locals, env_size, span);
    ctx.runtime.truncate_environment_storage(env_size);
    cont(last_value.unwrap_or_else(Value::unit))
}

fn drop_cleanup_locals(
    ctx: &mut HirInterpreter<'_, '_>,
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
        if target_index >= ctx.runtime.environment.len() {
            continue;
        }
        let target = local_place(ctx, locals, *id);
        drop_value_at_place_if_initialized(ctx, resolved_local_drop(drop), target, span)?;
    }
    Ok(())
}

fn eval_block_with_cleanup(
    arena: &ENodeArena,
    nodes: &[ENodeId],
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
    cleanup_drops: &[LocalDeclId],
) -> EvalControlFlowResult {
    let env_size = ctx.runtime.environment.len();
    let mut last_value: Option<Value> = None;
    for node in nodes.iter() {
        match eval_node_with_ctx(arena, *node, ctx, locals) {
            Err(err) => {
                if let Some(value) = last_value.take() {
                    value.discard_storage();
                }
                let err = ctx.cleanup_after_error(err, |ctx| {
                    drop_cleanup_locals(ctx, locals, cleanup_drops, arena[*node].span)
                });
                if !err.is_poisoning() {
                    ctx.assert_no_owned_local_leaks_before_truncate(
                        locals,
                        env_size,
                        arena[*node].span,
                    );
                }
                ctx.runtime.truncate_environment_storage(env_size);
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
                    ctx.runtime.truncate_environment_storage(env_size);
                    return Err(err);
                }
                ctx.assert_no_owned_local_leaks_before_truncate(
                    locals,
                    env_size,
                    arena[*node].span,
                );
                ctx.runtime.truncate_environment_storage(env_size);
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
        ctx.runtime.truncate_environment_storage(env_size);
        return Err(err);
    }
    ctx.assert_no_owned_local_leaks_before_truncate(locals, env_size, span);
    ctx.runtime.truncate_environment_storage(env_size);
    cont(last_value.unwrap_or_else(Value::unit))
}

#[inline(never)]
fn eval_assign(
    arena: &ENodeArena,
    node_id: ENodeId,
    assignment: &hir::Assignment<Elaborated>,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    // Source assignments have already captured their RHS outside destination accessors. This
    // final HIR node opens the place and installs that replacement; compound updates bind it once.
    let place = eval_or_return!(eval_node_as_place(arena, assignment.place, ctx, locals));
    let value = eval_or_return!(eval_node_with_ctx(arena, assignment.value, ctx, locals));
    let span = arena[node_id].span;
    if let Some(drop) = &assignment.drop
        && *drop != ResolvedLocalDrop::Skip
    {
        // Reserve the detached old value's slot before touching the destination. The destination
        // then remains initialized throughout semantic destruction, including poisoned exits.
        let old_index = ctx.runtime.environment.len();
        if let Err(error) = ctx
            .runtime
            .check_environment_cell_limit(old_index, Some(span))
        {
            value.discard_storage();
            return Err(error);
        }
        let old_value = place
            .replace_value(ctx.runtime, value)
            .map_err(|error| RuntimeError::new(error, Some(span)))?;
        ctx.runtime.environment.push(ValOrMut::Val(old_value));
        let old_place = Place::Boxed {
            root: old_index,
            path: Vec::new(),
        };
        let result =
            drop_value_at_place_if_initialized(ctx, resolved_local_drop(drop), old_place, span);
        ctx.runtime.truncate_environment_storage(old_index);
        result?;
    } else {
        replace_value_storage_at_place(ctx, &place, value, span)?;
    }
    cont(Value::unit())
}

#[inline(never)]
fn eval_drop_value(
    arena: &ENodeArena,
    drop: &hir::DropValue<Elaborated>,
    span: Location,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let target = eval_or_return!(eval_node_as_place(arena, drop.target, ctx, locals));
    drop_value_at_place_if_initialized(ctx, drop.drop, target, span)?;
    cont(Value::unit())
}

#[inline(never)]
fn eval_tuple(
    arena: &ENodeArena,
    nodes: &[ENodeId],
    ctx: &mut HirInterpreter<'_, '_>,
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
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let index = index.as_index();
    if let Some(mut place) = eval_or_return!(try_eval_node_as_place(arena, data, ctx, locals)) {
        place.push_index(index as isize);
        if place_resolution_depends_on_addressor_place(arena, data) {
            if let Some(value) =
                try_copy_trivial_copy_value_from_place(&place, ctx, arena[node_id].span)?
            {
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

fn place_resolution_depends_on_addressor_place(arena: &ENodeArena, node_id: ENodeId) -> bool {
    match &arena[node_id].kind {
        NodeKind::FunctionApply(app) => app.ty.returns_place(),
        NodeKind::StaticApply(app) => app.ty.returns_place(),
        NodeKind::SubscriptApply(app) => app.ty.returns_place(),
        NodeKind::CallDictionaryFunction(call) => call.ty.returns_place(),
        NodeKind::Project(node) => place_resolution_depends_on_addressor_place(arena, node.value),
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
    variant: &hir::Variant<Elaborated>,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let storage = match variant
        .payload_storage
        .expect("elaborated variant must have payload-storage metadata")
    {
        hir::VariantPayloadStorageSource::Static(storage) => storage,
        hir::VariantPayloadStorageSource::Evidence(extra_parameter) => {
            match extra_parameter_value(ctx, extra_parameter) {
                HiddenEvidenceArgValue::VariantPayloadStorage(storage) => storage,
                _ => panic!("variant payload-storage evidence has the wrong runtime shape"),
            }
        }
    };
    let value = eval_or_return!(eval_node_with_ctx(arena, variant.payload, ctx, locals));
    cont(Value::variant_with_storage(variant.tag, storage, value))
}

#[inline(never)]
fn eval_array(
    arena: &ENodeArena,
    nodes: &[ENodeId],
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let values = eval_or_return!(eval_nodes(arena, nodes, ctx, locals));
    cont(array_value_from_vec(values))
}

fn eval_case(
    arena: &ENodeArena,
    case: &hir::Case<Elaborated>,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let selected = if let Some(place) =
        eval_or_return!(try_eval_node_as_place(arena, case.value, ctx, locals))
    {
        let value = place
            .target_ref(ctx.runtime)
            .map_err(|err| RuntimeError::new(err, Some(arena[case.value].span)))?;
        select_case_alternative(case, value)
    } else {
        let value = eval_or_return!(eval_node_with_ctx(arena, case.value, ctx, locals));
        let selected = select_case_alternative(case, &value);
        value.discard_storage();
        selected
    };
    eval_node_with_ctx(arena, selected, ctx, locals)
}

fn select_case_alternative<'a>(
    case: &hir::Case<Elaborated>,
    value: impl Into<ValueRef<'a>>,
) -> ENodeId {
    let value = value.into();
    let variant_tag = value.as_boxed().and_then(Value::variant_tag);
    for (alternative, node) in &case.alternatives {
        if let Some(&tag) = alternative.as_variant_tag() {
            if variant_tag == Some(tag) {
                return *node;
            }
            continue;
        }
        match alternative.try_matches_runtime_value(value) {
            Ok(true) => return *node,
            Ok(false) => {}
            Err(_) => panic!(
                "Case evaluated a scrutinee incompatible with its literal alternatives. This HIR should have been rejected before evaluation."
            ),
        }
    }
    case.default
}

#[inline(never)]
fn eval_loop(
    arena: &ENodeArena,
    label: LoopId,
    body: ENodeId,
    ctx: &mut HirInterpreter<'_, '_>,
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
fn eval_node_as_place(
    arena: &ENodeArena,
    node_id: ENodeId,
    ctx: &mut HirInterpreter<'_, '_>,
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
    ctx: &mut HirInterpreter<'_, '_>,
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
    passing: ArgConvention,
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> Result<ControlFlow<ValOrMut>, RuntimeError> {
    match passing {
        ArgConvention::MutableRef => eval_node_as_place(arena, arg, ctx, locals)
            .map(|result| result.map_continue(ValOrMut::Mut)),
        ArgConvention::Let => match try_eval_node_as_place(arena, arg, ctx, locals) {
            Ok(ControlFlow::Continue(Some(place))) => {
                Ok(ControlFlow::Continue(ValOrMut::Mut(place)))
            }
            Ok(ControlFlow::Continue(None)) if is_dictionary_metadata_node(arena, arg) => {
                eval_dictionary_metadata_node(arena, arg, ctx)
                    .map(|result| result.map_continue(ValOrMut::Dictionary))
            }
            Ok(ControlFlow::Continue(None)) => eval_node_with_ctx(arena, arg, ctx, locals)
                .map(|result| result.map_continue(ValOrMut::Val)),
            Ok(transfer) => Ok(transfer.map_continue(unreachable_continue)),
            Err(err) => Err(err),
        },
    }
}

fn eval_args(
    arena: &ENodeArena,
    args: &[CallArgument<Elaborated>],
    args_ty: &[FnArgType],
    ctx: &mut HirInterpreter<'_, '_>,
    locals: &[LocalDecl],
) -> Result<ControlFlow<PreparedCallArgs>, RuntimeError> {
    let temp_start = ctx.runtime.environment.len();
    let mut results = Vec::with_capacity(args.len());
    assert_eq!(args.len(), args_ty.len());
    for arg in args {
        let result = eval_call_arg(arena, arg.value, arg.passing, ctx, locals);
        match result {
            Ok(ControlFlow::Continue(arg)) => results.push(arg),
            Ok(transfer) => {
                for result in results {
                    result.discard_storage();
                }
                ctx.runtime.truncate_environment_storage(temp_start);
                return Ok(transfer.map_continue(unreachable_continue));
            }
            Err(err) => {
                for result in results {
                    result.discard_storage();
                }
                ctx.runtime.truncate_environment_storage(temp_start);
                return Err(err);
            }
        }
    }
    Ok(ControlFlow::Continue(PreparedCallArgs::new(results)))
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
        NodeKind::GetFunction(_) | NodeKind::GetDictionaryFunction(_)
    )
}

/// Evaluate a node as a place when the HIR shape permits it.
fn try_eval_node_as_place(
    arena: &ENodeArena,
    node_id: ENodeId,
    ctx: &mut HirInterpreter<'_, '_>,
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
            place.push_index(node.index.as_index() as isize);
            place
        }
        FunctionApply(app) if app.ty.returns_place() => {
            let result = eval_apply(arena, app, node.span, ctx, locals)?;
            return Ok(control_flow_into_addressor_place(result).map_continue(Some));
        }
        StaticApply(app) if app.ty.returns_place() => {
            let result = eval_addressor_place_static_apply(arena, app, node.span, ctx, locals)?;
            return Ok(control_flow_into_addressor_place(result).map_continue(Some));
        }
        SubscriptApply(app) if app.ty.returns_place() => {
            let result = eval_addressor_place_subscript_apply(arena, app, node.span, ctx, locals)?;
            return Ok(control_flow_into_addressor_place(result).map_continue(Some));
        }
        CallDictionaryFunction(call) if call.ty.returns_place() => {
            let result =
                eval_addressor_place_call_dictionary_function(arena, call, node.span, ctx, locals)?;
            return Ok(control_flow_into_addressor_place(result).map_continue(Some));
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
        WithPlace(node) if node_may_resolve_to_place(arena, node.body) => {
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
    ctx: &mut HirInterpreter<'_, '_>,
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
        NodeKind::FunctionApply(app) => app.ty.returns_place(),
        NodeKind::StaticApply(app) => app.ty.returns_place(),
        NodeKind::SubscriptApply(app) => app.ty.returns_place(),
        NodeKind::CallDictionaryFunction(call) => call.ty.returns_place(),
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
    use super::{
        ControlFlow, ControlTransfer, HirInterpreter, combine_with_yielded_body_and_epilogue, cont,
        eval_args, eval_node, eval_nodes, ret,
    };
    use std::{
        fmt,
        sync::atomic::{AtomicUsize, Ordering},
    };

    use crate::{
        CompilerSession, Location,
        compiler::error::{RuntimeErrorKind, SourceFailureKind},
        containers::{SVec2, b},
        eval::{EvalCtx, EvalResult, RuntimeError},
        hir::{
            self, CallArgument, ENode, ENodeArena, Elaborated, LoopId, NodeKind,
            function::{ArgConvention, CallableDefinition, ScriptFunction},
            hir_syn,
            native_functions::NativeOutFn0,
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

    fn make_eval_drop_tracked() -> EvalDropTracked {
        EvalDropTracked
    }

    fn eval_drop_tracked_function() -> ModuleFunction {
        NativeOutFn0::from_rust(make_eval_drop_tracked).description(
            [],
            "Creates a drop-tracked interpreter test value.",
            EffType::empty(),
        )
    }

    fn eval_drop_tracked_node(
        arena: &mut ENodeArena,
        module_id: ModuleId,
        function_id: LocalFunctionId,
        span: Location,
    ) -> crate::hir::ENodeId {
        let ty = eval_drop_tracked_type();
        node(
            arena,
            hir_syn::static_apply(
                crate::module::FunctionId::new(module_id, function_id),
                FnType::new(vec![], ty, EffType::empty()),
                Vec::new(),
                span,
            ),
            ty,
            span,
        )
    }

    fn eval_args_test_session() -> (CompilerSession, ModuleId) {
        let mut session = CompilerSession::new();
        let module_id = session.raw_modules().next_id();
        let path = Path::single_str("$eval_args_test");
        let mut module = Module::new(module_id, path.clone());
        let function =
            module.add_function(ustr("make_eval_drop_tracked"), eval_drop_tracked_function());
        assert_eq!(function, LocalFunctionId::from_index(0));
        let registered = session.register_module(path, module);
        assert_eq!(registered, module_id);
        (session, module_id)
    }

    #[test]
    fn assignment_keeps_destination_initialized_during_drop_and_poisoning() {
        #[derive(Clone)]
        struct ObserveDrop {
            poison: bool,
        }
        impl crate::hir::function::Callable for ObserveDrop {
            fn runtime_argument_passing(&self) -> Option<&[ArgConvention]> {
                Some(&[ArgConvention::MutableRef])
            }
            fn format_ind(
                &self,
                f: &mut fmt::Formatter,
                _: &[crate::module::ELocalDecl],
                _: &crate::module::ModuleEnv<'_>,
                _: usize,
                _: usize,
            ) -> fmt::Result {
                f.write_str("ObserveDrop")
            }
            fn call(&self, args: Vec<super::ValOrMut>, ctx: &mut EvalCtx) -> EvalResult {
                // Test-only inspection of caller storage: destruction receives the detached old
                // value while the original destination already holds its replacement.
                assert_eq!(args[0].as_primitive::<isize>(ctx).unwrap(), Some(&1));
                assert_eq!(
                    ctx.environment[0].as_primitive::<isize>(ctx).unwrap(),
                    Some(&2)
                );
                if self.poison {
                    Err(ctx.environment_cell_limit_error(None))
                } else {
                    Ok(Value::unit())
                }
            }
        }
        for poison in [false, true] {
            let mut session = CompilerSession::new();
            let module_id = session.raw_modules().next_id();
            let path = Path::single_str("$replacement_test");
            let mut module = Module::new(module_id, path.clone());
            let definition = function_definition(
                FnType::new_mut_resolved([(int_type(), true)], Type::unit(), EffType::empty()),
                ["target"],
            );
            let drop = module.add_function(
                ustr("observe_drop"),
                ModuleFunction::new(definition, b(ObserveDrop { poison }), None, Vec::new()),
            );
            session.register_module(path, module);

            let span = Location::new_synthesized();
            let mut arena = ENodeArena::default();
            let place = node(
                &mut arena,
                hir_syn::load_local(LocalDeclId::from_index(0)),
                int_type(),
                span,
            );
            let value = node(&mut arena, hir_syn::native(2isize), int_type(), span);
            let assignment = hir::Assignment {
                place,
                value,
                drop: Some(ResolvedLocalDrop::Static(crate::module::FunctionId::new(
                    module_id, drop,
                ))),
            };
            let assignment_node = node(
                &mut arena,
                NodeKind::Assign(assignment.clone()),
                Type::unit(),
                span,
            );
            let mut locals = [owned_local("target", MutType::mutable(), int_type(), span)];
            LocalDecl::assign_sequential_slots(&mut locals);
            let locals = locals.map(LocalDecl::into_elaborated);
            let mut runtime = EvalCtx::new(module_id, &session);
            let mut ctx = HirInterpreter::root(&mut runtime);
            ctx.runtime
                .environment
                .push(super::ValOrMut::from_primitive(1isize));
            let result =
                super::eval_assign(&arena, assignment_node, &assignment, &mut ctx, &locals);
            assert_eq!(result.is_err(), poison);
            assert_eq!(ctx.runtime.environment.len(), 1);
            assert_eq!(
                ctx.runtime.environment[0]
                    .as_primitive::<isize>(ctx.runtime)
                    .unwrap(),
                Some(&2)
            );
        }
    }

    fn test_module_id() -> ModuleId {
        CompilerSession::new().raw_modules().next_id()
    }

    fn eval_drop_tracked_count() -> usize {
        EVAL_DROP_TRACKED_COUNT.load(Ordering::Relaxed)
    }

    #[test]
    fn with_yielded_body_value_wins_over_epilogue_transfer() {
        let session = CompilerSession::new();
        let mut runtime = EvalCtx::new(ModuleId::from_index(0), &session);
        let mut ctx = HirInterpreter::root(&mut runtime);
        let result = combine_with_yielded_body_and_epilogue(
            &mut ctx,
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
        let session = CompilerSession::new();
        let mut runtime = EvalCtx::new(ModuleId::from_index(0), &session);
        let mut ctx = HirInterpreter::root(&mut runtime);
        let result = combine_with_yielded_body_and_epilogue(
            &mut ctx,
            Err(RuntimeError::new_native(SourceFailureKind::Aborted(Some(
                "body".into(),
            )))),
            ret(Value::native(2 as Int)),
        );

        let err = result.expect_err("expected body error to win over epilogue transfer");
        assert_eq!(
            err.kind(),
            RuntimeErrorKind::SourceFailure(SourceFailureKind::Aborted(Some("body".to_string())))
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
            vec![ArgConvention::MutableRef],
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
        let test_module_id = test_module_id();

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
                    passing: ArgConvention::MutableRef,
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
            vec![ArgConvention::MutableRef],
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
        let test_module_id = test_module_id();

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
        let tracked_function_id = LocalFunctionId::from_index(1);
        let epilogue_tracked =
            eval_drop_tracked_node(&mut arena, test_module_id, tracked_function_id, span);
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
        assert_eq!(
            module.add_function(ustr("make_eval_drop_tracked"), eval_drop_tracked_function()),
            tracked_function_id
        );

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
        let test_module_id = test_module_id();

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
                    passing: ArgConvention::MutableRef,
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
                    passing: ArgConvention::MutableRef,
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
        let tracked = eval_drop_tracked_node(
            &mut arena,
            test_module_id(),
            LocalFunctionId::from_index(0),
            span,
        );
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
        let mut runtime = EvalCtx::new(module_id, &session);
        let mut ctx = HirInterpreter::root(&mut runtime);

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
        let tracked = eval_drop_tracked_node(
            &mut arena,
            test_module_id(),
            LocalFunctionId::from_index(0),
            span,
        );
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
        let (session, module_id) = eval_args_test_session();
        let result = eval_node(&arena, block, module_id, &[], &session).unwrap();
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
        let tracked = eval_drop_tracked_node(
            &mut arena,
            test_module_id(),
            LocalFunctionId::from_index(0),
            span,
        );
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
        let mut runtime = EvalCtx::new(module_id, &session);
        let mut ctx = HirInterpreter::root(&mut runtime);
        let arg_tys = [
            FnArgType::new_by_val(eval_drop_tracked_type()),
            FnArgType::new_by_val(Type::unit()),
        ];
        let arguments = [
            CallArgument {
                value: tracked,
                passing: ArgConvention::Let,
            },
            CallArgument {
                value: return_unit,
                passing: ArgConvention::Let,
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
        let tracked = eval_drop_tracked_node(
            &mut arena,
            test_module_id(),
            LocalFunctionId::from_index(0),
            span,
        );
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
        let mut runtime = EvalCtx::new(module_id, &session);
        let mut ctx = HirInterpreter::root(&mut runtime);
        let arg_tys = [
            FnArgType::new_by_val(eval_drop_tracked_type()),
            FnArgType::new_by_val(Type::unit()),
        ];
        let arguments = [
            CallArgument {
                value: tracked,
                passing: ArgConvention::Let,
            },
            CallArgument {
                value: break_node,
                passing: ArgConvention::Let,
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
