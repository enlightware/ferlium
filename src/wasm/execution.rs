// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{
    cell::RefCell,
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ptr,
    rc::Rc,
};

use js_sys::{
    Function as JsFunction, Reflect, Uint8Array,
    WebAssembly::{self, Table},
};
use strum::FromRepr;
use wasm_bindgen::{JsCast, JsValue};

use crate::{
    CompilerSession,
    compiler::error::SandboxViolationKind,
    eval::RuntimeError,
    execution::ExecutionLimits,
    hir::{native_functions::NativeFailureState, value::Value},
    mir::physical::program::ResolvedPhysicalProgram,
    module::{FunctionId, id::Id},
    std::{math::Float, string::StaticStr},
    types::r#type::Type,
};

use super::{
    Imports,
    abi::HostTableSlotId,
    boxed::{self, NativeOutputs},
    emit::{self, HostExportKind, ScalarType},
    failure::Failures,
};

mod sealed {
    use super::*;

    pub trait Value: Copy {
        type Argument: Copy;
        fn ty() -> Type;
        fn argument(self) -> Self::Argument;
    }

    pub trait Arguments: Copy {
        fn types() -> Vec<Type>;
        /// The table entry must match this argument tuple and R's C ABI.
        unsafe fn invoke<R: WasmValue>(self, slot: HostTableSlotId) -> R;
    }
}

/// Rust values with a supported, matching Ferlium ABI representation. This trait is sealed.
pub trait WasmValue: sealed::Value + 'static {}

macro_rules! value {
    ($($ty:ty),*) => {$ (
        impl sealed::Value for $ty {
            type Argument = Self;
            fn ty() -> Type { Type::primitive::<Self>() }
            fn argument(self) -> Self { self }
        }
        impl WasmValue for $ty {}
    )* };
}
value!(bool, isize, Float);

impl sealed::Value for () {
    type Argument = *const ();
    fn ty() -> Type {
        Type::unit()
    }
    fn argument(self) -> Self::Argument {
        ptr::NonNull::<()>::dangling().as_ptr()
    }
}
impl WasmValue for () {}

/// A tuple of Rust arguments, or `()` for no arguments. This trait is sealed.
pub trait WasmArguments: sealed::Arguments {}

macro_rules! arguments {
    ($($ty:ident:$index:tt),*) => {
        impl<$($ty: WasmValue),*> sealed::Arguments for ($($ty,)*) {
            fn types() -> Vec<Type> { vec![$($ty::ty()),*] }
            #[inline]
            unsafe fn invoke<R: WasmValue>(self, slot: HostTableSlotId) -> R {
                // SAFETY: binding checks the exact signature; the live table slot contains the
                // generated entry itself. wasm32 C function pointers are table indexes.
                let function: unsafe extern "C" fn($($ty::Argument),*) -> R = unsafe { mem::transmute(slot.as_index()) };
                unsafe { function($(self.$index.argument()),*) }
            }
        }
        impl<$($ty: WasmValue),*> WasmArguments for ($($ty,)*) {}
    };
}
arguments!();
arguments!(A:0);
arguments!(A:0, B:1);
arguments!(A:0, B:1, C:2);
arguments!(A:0, B:1, C:2, D:3);
arguments!(A:0, B:1, C:2, D:3, E:4);
arguments!(A:0, B:1, C:2, D:3, E:4, F:5);
arguments!(A:0, B:1, C:2, D:3, E:4, F:5, G:6);
arguments!(A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7);

/// Execution budgets plus a bounded, invocation-owned linear-memory stack.
#[derive(Clone, Copy, Debug)]
pub struct WasmLimits {
    pub execution: ExecutionLimits,
    pub stack_bytes: usize,
}

impl Default for WasmLimits {
    fn default() -> Self {
        Self {
            execution: ExecutionLimits::default(),
            stack_bytes: 1024 * 1024,
        }
    }
}

/// Shared host-owned invocation state; generated code records violations here before trapping.
#[repr(C)]
pub(super) struct InvocationState {
    pub stack: u32,
    pub end: u32,
    pub depth_limit: u32,
    pub fuel: u32,
    pub fuel_enabled: u32,
    pub failure: u32,
    pub diagnostics: *mut Failures,
    pub strings: *const StaticStr,
    pub native_failure: *mut NativeFailureState,
    pub evidence: *const u32,
}

/// Out-of-band diagnostics written by generated code before trapping; zero means no failure.
#[derive(Clone, Copy, FromRepr)]
#[repr(u32)]
pub(super) enum FailureCode {
    Fuel = 1,
    CallDepth,
    StackCapacity,
    Invariant,
    Source,
}

/// Export name of the function a compiled program runs.
pub(super) const ENTRY_EXPORT: &str = "entry";

/// Generated code and instance-local native bindings. Compilation does not execute guest code.
pub struct CompiledProgram {
    emitted: emit::Emitted,
    imports: Imports,
}

impl CompiledProgram {
    pub fn compile(session: &CompilerSession, entry: FunctionId) -> Result<Self, RuntimeError> {
        let program = session.prepare_physical_program(entry.module)?;
        Self::from_physical(session, &program, entry)
    }

    pub(super) fn from_physical(
        session: &CompilerSession,
        program: &ResolvedPhysicalProgram<'_>,
        entry: FunctionId,
    ) -> Result<Self, RuntimeError> {
        let mut imports = Imports::new().map_err(js_error)?;
        let emitted = emit::emit(
            program,
            &[entry],
            &[(entry, ENTRY_EXPORT.into())],
            &mut imports,
            session,
        )
        .map_err(RuntimeError::Backend)?;
        Ok(Self { emitted, imports })
    }

    fn compile_boxed(
        session: &CompilerSession,
        entry: FunctionId,
    ) -> Result<(Self, NativeOutputs), RuntimeError> {
        let program = session.prepare_physical_program(entry.module)?;
        let mut imports = Imports::new().map_err(js_error)?;
        let emitted = emit::emit_boxed(
            &program,
            &[entry],
            &[(entry, ENTRY_EXPORT.into())],
            &mut imports,
            session,
        )
        .map_err(RuntimeError::Backend)?;
        Ok((Self { emitted, imports }, boxed::native_outputs(&program)))
    }

    pub fn bytes(&self) -> &[u8] {
        &self.emitted.bytes
    }

    /// Validate the engine imports and bind a Rust signature once, before any guest call.
    pub fn instantiate<A: WasmArguments, R: WasmValue>(
        &self,
    ) -> Result<Instance<A, R>, RuntimeError> {
        let types = A::types()
            .into_iter()
            .map(ScalarType::of)
            .collect::<Result<Vec<_>, _>>()
            .map_err(RuntimeError::Backend)?;
        let [export] = self.emitted.exports.as_slice() else {
            unreachable!("a compiled program exports only its entry");
        };
        let HostExportKind::Scalar { parameters, result } = &export.kind else {
            return Err(RuntimeError::Backend(
                "boxed Wasm export cannot use a typed binding".into(),
            ));
        };
        if types != *parameters
            || ScalarType::of(R::ty()).map_err(RuntimeError::Backend)? != *result
        {
            return Err(RuntimeError::Backend(
                "Rust signature does not match the Wasm entry".into(),
            ));
        }
        Ok(Instance {
            runtime: self.instantiate_runtime(export)?,
            marker: PhantomData,
        })
    }

    fn instantiate_boxed(
        &self,
        native_outputs: NativeOutputs,
    ) -> Result<BoxedInstance, RuntimeError> {
        let [export] = self.emitted.exports.as_slice() else {
            unreachable!("a compiled program exports only its entry");
        };
        let HostExportKind::Boxed { result } = export.kind else {
            return Err(RuntimeError::Backend(
                "typed Wasm export cannot use a boxed binding".into(),
            ));
        };
        Ok(BoxedInstance {
            runtime: self.instantiate_runtime(export)?,
            owner: export.function,
            result,
            native_outputs,
        })
    }

    fn instantiate_runtime(
        &self,
        export: &emit::HostExport,
    ) -> Result<RuntimeInstance, RuntimeError> {
        let bytes = Uint8Array::from(self.bytes());
        let module = WebAssembly::Module::new(&bytes).map_err(js_error)?;
        let instance =
            WebAssembly::Instance::new(&module, self.imports.object()).map_err(js_error)?;
        let exports = instance.exports();
        let entry = Reflect::get(&exports, &export.name.as_str().into())
            .map_err(js_error)?
            .dyn_into()
            .map_err(js_error)?;
        let setup = Reflect::get(&exports, &emit::SETUP_EXPORT.into())
            .map_err(js_error)?
            .dyn_into()
            .map_err(js_error)?;
        Ok(RuntimeInstance {
            entry: TableSlot::new(&entry)?,
            setup: TableSlot::new(&setup)?,
            stack: Vec::new(),
            strings: self.emitted.strings.clone(),
            evidence: self.emitted.evidence.instantiate(),
        })
    }
}

/// Execute one no-argument expression through generated Wasm and box its result for the shared
/// differential harness.
///
/// This is temporary compatibility scaffolding, not the production host-value ABI.
#[doc(hidden)]
pub fn run_boxed_entry(
    session: &CompilerSession,
    entry: FunctionId,
    limits: WasmLimits,
) -> Result<Value, RuntimeError> {
    let (program, native_outputs) = CompiledProgram::compile_boxed(session, entry)?;
    program
        .instantiate_boxed(native_outputs)?
        .run(session, limits)
}

thread_local! {
    static FREE_TABLE_SLOTS: RefCell<Vec<HostTableSlotId>> = const { RefCell::new(Vec::new()) };
}

/// Owns an instance-local slot in Rust's indirect function table.
struct TableSlot {
    table: Table,
    index: HostTableSlotId,
}

impl TableSlot {
    fn new(function: &JsFunction) -> Result<Self, RuntimeError> {
        let table: Table = wasm_bindgen::function_table()
            .dyn_into()
            .map_err(js_error)?;
        let index = FREE_TABLE_SLOTS
            .with(|slots| slots.borrow_mut().pop())
            .map(Ok)
            .unwrap_or_else(|| table.grow(1).map(HostTableSlotId::new))
            .map_err(js_error)?;
        let slot = Self { table, index };
        slot.table.set(index.as_u32(), function).map_err(js_error)?;
        Ok(slot)
    }
}

impl Drop for TableSlot {
    fn drop(&mut self) {
        if self
            .table
            .set_raw(self.index.as_u32(), &JsValue::NULL)
            .is_ok()
        {
            FREE_TABLE_SLOTS.with(|slots| slots.borrow_mut().push(self.index));
        }
    }
}

/// An ABI-checked binding whose code and function-table slots remain live until it is dropped.
pub struct Instance<A, R> {
    runtime: RuntimeInstance,
    marker: PhantomData<fn(A) -> R>,
}

struct RuntimeInstance {
    entry: TableSlot,
    setup: TableSlot,
    // Frame bytes are lent exclusively to each invocation. MIR lifetimes, not zeroing, govern reads.
    stack: Vec<u64>,
    strings: Box<[StaticStr]>,
    evidence: Box<[u32]>,
}

struct BoxedInstance {
    runtime: RuntimeInstance,
    owner: FunctionId,
    result: Type,
    native_outputs: NativeOutputs,
}

/// A direct Rust-callable entry borrowed for one active invocation. No JavaScript, allocation,
/// argument marshalling or signature checking occurs on this call path.
pub struct BoundFunction<A, R> {
    slot: HostTableSlotId,
    marker: PhantomData<Rc<(A, R)>>,
}

impl<A: WasmArguments, R: WasmValue> BoundFunction<A, R> {
    #[inline]
    pub fn call(&self, arguments: A) -> R {
        // SAFETY: only a bound instance in an active scope lends this handle. Its signature was
        // checked at binding, its table slot is live, and its execution state is installed.
        unsafe { arguments.invoke(self.slot) }
    }
}

impl<A: WasmArguments, R: WasmValue> Instance<A, R> {
    /// Run one call in a fresh invocation. Arguments and results stay in Rust/Wasm throughout.
    pub fn run(&mut self, arguments: A, limits: WasmLimits) -> Result<R, RuntimeError> {
        // SAFETY: the callback holds only sealed Copy arguments and a borrowed function. There
        // are no Rust cleanup obligations in frames between the trap boundary and generated code.
        unsafe { self.with_invocation(limits, |function| function.call(arguments)) }
    }

    /// Run Rust code with a direct callable binding and one shared execution budget.
    ///
    /// # Safety
    /// Wasm traps do not unwind Rust frames. The callback and any native re-entry must tolerate
    /// non-unwinding cancellation: no Rust cleanup guard may be required to restore memory safety.
    /// Owned resources in interrupted frames are not reclaimed by this boundary.
    #[inline(never)]
    pub unsafe fn with_invocation<T>(
        &mut self,
        limits: WasmLimits,
        callback: impl FnOnce(&BoundFunction<A, R>) -> T,
    ) -> Result<T, RuntimeError> {
        // SAFETY: this method's caller upholds the same non-unwinding callback contract.
        unsafe {
            self.runtime.with_invocation(limits, |slot| {
                let function = BoundFunction {
                    slot,
                    marker: PhantomData,
                };
                callback(&function)
            })
        }
    }
}

impl BoxedInstance {
    fn run(
        &mut self,
        session: &CompilerSession,
        limits: WasmLimits,
    ) -> Result<Value, RuntimeError> {
        boxed::validate_result(session, self.owner, &self.native_outputs, self.result)
            .map_err(RuntimeError::Backend)?;
        let layout = boxed::result_layout(session, self.owner, self.result)
            .map_err(RuntimeError::Backend)?;
        if layout.align() > align_of::<u64>() {
            return Err(RuntimeError::Backend(
                "boxed Wasm result alignment exceeds eight bytes".into(),
            ));
        }
        let mut storage = vec![0_u64; layout.size().max(1).div_ceil(size_of::<u64>())];
        let output = storage.as_mut_ptr().cast::<u8>();
        // SAFETY: the generated boxed entry has the fixed pointer-only signature, and the callback
        // has no Rust cleanup obligation below the trap boundary.
        unsafe {
            self.runtime.with_invocation(limits, |slot| {
                let function: unsafe extern "C" fn(*mut u8) = mem::transmute(slot.as_index());
                function(output);
            })?;
        }
        boxed::export(
            session,
            self.owner,
            &self.native_outputs,
            self.result,
            output,
        )
        .map_err(RuntimeError::Backend)
    }
}

impl RuntimeInstance {
    /// Run a callback under the sole JavaScript trap boundary for this instance.
    unsafe fn with_invocation<T>(
        &mut self,
        limits: WasmLimits,
        callback: impl FnOnce(HostTableSlotId) -> T,
    ) -> Result<T, RuntimeError> {
        if limits.stack_bytes > i32::MAX as usize || limits.stack_bytes < 8 {
            return Err(RuntimeError::Backend("invalid Wasm stack capacity".into()));
        }
        let stack_words = limits.stack_bytes / 8;
        if self.stack.len() < stack_words {
            self.stack.resize(stack_words, 0);
        }
        let base = self.stack.as_mut_ptr() as u32;
        let mut diagnostics = Failures::default();
        // Derive both pointers from the same raw borrow. No Rust access to diagnostics resumes
        // until setup is reset; each runtime callback borrows it only for that callback.
        let diagnostics_ptr = &raw mut diagnostics;
        let mut state = InvocationState {
            stack: base,
            end: base
                .checked_add((stack_words * 8) as u32)
                .ok_or_else(|| RuntimeError::Backend("Wasm stack address overflow".into()))?,
            depth_limit: limits.execution.call_depth_limit as u32,
            fuel: limits.execution.fuel_limit.unwrap_or(0) as u32,
            fuel_enabled: u32::from(limits.execution.fuel_limit.is_some()),
            failure: 0,
            strings: self.strings.as_ptr(),
            evidence: self.evidence.as_ptr(),
            // SAFETY: diagnostics_ptr points to the live invocation-owned diagnostics above.
            native_failure: unsafe { &raw mut (*diagnostics_ptr).native },
            diagnostics: diagnostics_ptr,
        };
        // SAFETY: setup is generated with this exact C signature. It borrows state until reset;
        // the stack block is alive, aligned and disjoint from the Rust call stack.
        let setup: unsafe extern "C" fn(*mut InvocationState) =
            unsafe { mem::transmute(self.setup.index.as_index()) };
        unsafe { setup(&mut state) };
        let outcome = catch_trap(|| callback(self.entry.index));
        unsafe { setup(ptr::null_mut()) };
        outcome.map_err(|error| {
            let error = match FailureCode::from_repr(state.failure) {
                Some(FailureCode::Fuel) => {
                    RuntimeError::new_sandbox_violation(SandboxViolationKind::FuelExhausted, None)
                }
                Some(FailureCode::CallDepth) => RuntimeError::new_sandbox_violation(
                    SandboxViolationKind::CallDepthLimitExceeded {
                        limit: limits.execution.call_depth_limit,
                    },
                    None,
                ),
                Some(FailureCode::StackCapacity) => RuntimeError::new_sandbox_violation(
                    SandboxViolationKind::StackByteLimitExceeded {
                        limit: limits.stack_bytes,
                    },
                    None,
                ),
                Some(FailureCode::Invariant) => {
                    RuntimeError::Backend("Wasm MIR invariant failure".into())
                }
                Some(FailureCode::Source) => {
                    return diagnostics.finish(None).expect("source failure diagnostic");
                }
                None => js_error(error),
            };
            diagnostics.finish(Some(error)).expect("execution error")
        })
    }
}

/// The sole JavaScript execution boundary calls a Rust thunk with an opaque pointer. Neither
/// guest arguments nor results cross it. Rust-to-Ferlium calls inside the thunk are ordinary C
/// function-pointer calls, including multiple calls made in one invocation scope.
// Keep an enclosing Rust frame: its normal epilogue restores the shadow-stack pointer even when
// the thunk's frames were abandoned by a trap. This does not run their Rust destructors.
#[inline(never)]
fn catch_trap<F: FnOnce() -> T, T>(callback: F) -> Result<T, JsValue> {
    struct Context<F, T> {
        callback: Option<F>,
        result: MaybeUninit<T>,
    }
    unsafe extern "C" fn invoke<F: FnOnce() -> T, T>(context: *mut Context<F, T>) {
        // SAFETY: catch_trap owns this context until the synchronous invocation returns or traps.
        let context = unsafe { &mut *context };
        context.result.write(context.callback.take().unwrap()());
    }
    let mut context = Context {
        callback: Some(callback),
        result: MaybeUninit::uninit(),
    };
    let table: Table = wasm_bindgen::function_table().dyn_into()?;
    let thunk_slot = HostTableSlotId::from_index(invoke::<F, T> as *const () as usize);
    let thunk = table.get(thunk_slot.as_u32())?;
    thunk.call1(
        &JsValue::UNDEFINED,
        &JsValue::from_f64(ptr::from_mut(&mut context) as usize as f64),
    )?;
    // SAFETY: a normal return from the Rust thunk initialized the result. On a trap we returned
    // above without reading it or attempting guest cleanup.
    Ok(unsafe { context.result.assume_init() })
}

fn js_error(error: JsValue) -> RuntimeError {
    RuntimeError::Backend(format!("Wasm engine: {error:?}"))
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use wasm_bindgen_test::wasm_bindgen_test;

    use crate::{
        Location, MirOptimization,
        compiler::error::SourceFailureKind,
        hir::{native_functions::NativeFallibleOutFnN, value::LiteralValue},
        mir::{
            Operation, ParameterKind, Value,
            builder::FunctionBuilder,
            physical::{prepare_physical_mir, program::resolve_physical_program},
            terminator::Terminator,
        },
        module::{LocalFunctionId, Module, Path, id::Id},
        std::math::int_type,
        types::{
            effects::{PrimitiveEffect, effect},
            r#type::{CallImplType, CallResultConvention, FnType},
        },
        ustr,
    };

    use super::*;

    #[wasm_bindgen_test]
    fn wasm_codegen_failure_during_cleanup() {
        thread_local! { static CALLS: Cell<isize> = const { Cell::new(0) }; }
        fn fail(stage: isize) -> Result<isize, SourceFailureKind> {
            CALLS.set(CALLS.get() * 10 + stage);
            Err(match stage {
                1 => SourceFailureKind::DivisionByZero,
                2 => SourceFailureKind::InvalidArgument("cleanup failed".into()),
                _ => unreachable!(),
            })
        }

        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        session.set_physical_mir_optimization(MirOptimization::Disabled);
        let path = Path::single_str("probe");
        let mut module = Module::new(session.modules().next_id(), path.clone());
        let native = module.add_function(
            ustr("fail"),
            NativeFallibleOutFnN::from_rust(fail).description(
                ["stage"],
                "",
                effect(PrimitiveEffect::Fallible),
            ),
        );
        let native = FunctionId::new(module.module_id(), native);
        session.register_module(path, module);
        let module = session
            .compile(
                "fn compute() -> int { probe::fail(1) }",
                "cleanup",
                Path::single_str("cleanup"),
            )
            .unwrap()
            .module_id;
        let compiled = session.expect_fresh_module(module);
        let entry = FunctionId::new(
            module,
            compiled.get_local_function_id(ustr("compute")).unwrap(),
        );
        let env = session.modules().env_for(compiled);

        // Two genuinely fallible Invokes, not a failing pure Value::drop implementation.
        // The first error edge performs cleanup; its error edge must poison with both causes.
        let mut body = FunctionBuilder::new(ustr("compute"), CallResultConvention::Value);
        let output = Value::Parameter(body.add_parameter(int_type(), ParameterKind::Return));
        let start = body.add_block();
        let returned = body.add_block();
        let cleanup = body.add_block();
        let propagated = body.add_block();
        let poisoned = body.add_block();
        let span = Location::new_synthesized();
        let marker = body
            .append_operation(start, Operation::stack_save(span))
            .unwrap();
        let argument = body
            .append_operation(start, Operation::alloca(span, int_type()))
            .unwrap();
        for (block, stage, normal, error) in [
            (start, 1_isize, returned, cleanup),
            (cleanup, 2, propagated, poisoned),
        ] {
            let constant = body.add_constant(int_type(), LiteralValue::new_native(stage), &env);
            body.append_operation(
                block,
                Operation::store(span, Value::Constant(constant), argument.clone()),
            );
            let call = Operation::call(
                span,
                Value::Function(native),
                [argument.clone(), output.clone()],
                CallImplType::value(FnType::new_by_val(
                    [int_type()],
                    int_type(),
                    effect(PrimitiveEffect::Fallible),
                )),
            );
            body.set_terminator(block, Terminator::invoke(span, call, normal, error));
        }
        body.append_operation(returned, Operation::stack_restore(span, marker.clone()));
        body.set_terminator(returned, Terminator::ret(span));
        body.append_operation(propagated, Operation::clear(span, output));
        body.append_operation(propagated, Operation::stack_restore(span, marker));
        body.set_terminator(propagated, Terminator::propagate_error(span));
        body.set_terminator(poisoned, Terminator::failure_during_cleanup(span));

        let original = session.prepare_physical_program(module).unwrap();
        let artifacts = original.module(module).unwrap();
        let mut entries = (0..artifacts.entry_count())
            .map(|index| artifacts.get(LocalFunctionId::from_index(index)).cloned())
            .collect::<Vec<_>>();
        entries[entry.function.as_index()] = Some(body.finish(env));
        let replacement = prepare_physical_mir(
            entries,
            artifacts.direct_entries().clone(),
            session
                .mir_artifacts_for(module, MirOptimization::Disabled)
                .unwrap(),
            env,
        )
        .unwrap();
        let program = resolve_physical_program(original.modules().iter().map(|artifacts| {
            if artifacts.module() == module {
                &replacement
            } else {
                *artifacts
            }
        }))
        .unwrap();
        let mut imports = Imports::new().unwrap();
        let emitted = emit::emit(
            &program,
            &[entry],
            &[(entry, ENTRY_EXPORT.into())],
            &mut imports,
            &session,
        )
        .unwrap();
        let mut instance = CompiledProgram { emitted, imports }
            .instantiate::<(), isize>()
            .unwrap();
        for _ in 0..2 {
            CALLS.set(0);
            let error = instance.run((), WasmLimits::default()).unwrap_err();
            let failure = error.failure_during_cleanup().unwrap();
            assert_eq!(failure.initial().kind(), SourceFailureKind::DivisionByZero);
            assert_eq!(
                failure.during_cleanup().kind(),
                SourceFailureKind::InvalidArgument("cleanup failed".into())
            );
            assert_eq!(CALLS.get(), 12);
        }
    }
}
