// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{fmt::Debug, hint::black_box, mem::offset_of, ptr};

use js_sys::{Function as JsFunction, Reflect, Uint8Array, WebAssembly};
use wasm_bindgen::{JsCast, JsValue};
use wasm_bindgen_test::wasm_bindgen_test;
use wasmparser::{Operator, Parser, Payload};

use crate::{
    CompilerSession, ExecutionTarget,
    compiler::{
        MirOptimization,
        error::{RuntimeErrorKind, SandboxViolationKind},
    },
    hir::value::{NativeValueType, Value},
    module::{FunctionId, Path},
    std::math::Float,
    ustr,
};

use super::{CompiledProgram, Imports, WasmLimits, WasmValue, emit, execution::InvocationState};

// Observe the address of a real Rust shadow-stack slot without exporting runtime internals.
#[inline(never)]
fn shadow_stack_probe() -> usize {
    let mut slot = 0_u64;
    black_box(ptr::from_mut(&mut slot)) as usize
}

fn compile(session: &mut CompilerSession, source: &str) -> FunctionId {
    let output = session
        .compile(source, "wasm_test", Path::single(ustr("wasm_test")))
        .unwrap();
    let module = session.expect_fresh_module(output.module_id);
    FunctionId::new(
        output.module_id,
        module.get_local_function_id(ustr("compute")).unwrap(),
    )
}

fn differential<A: WasmValue + NativeValueType, R: WasmValue + PartialEq + Debug>(
    session: &mut CompilerSession,
    source: &str,
    input: A,
) {
    let entry = compile(session, source);
    let reference = session
        .run_entry(
            ExecutionTarget::PhysicalMir,
            entry.module,
            entry.function,
            vec![Value::native(input)],
        )
        .unwrap();
    let code =
        CompiledProgram::compile(session, entry).unwrap_or_else(|e| panic!("{source}: {e:?}"));
    let mut instance = code
        .instantiate::<(A,), R>()
        .unwrap_or_else(|e| panic!("{source}: {e:?}"));
    for _ in 0..2 {
        assert_eq!(
            &instance.run((input,), WasmLimits::default()).unwrap(),
            reference.as_primitive_ty::<R>().unwrap(),
            "{source}"
        );
    }
    reference.discard_storage();
}

#[wasm_bindgen_test]
fn wasm_codegen_scalar_differential() {
    let cases = [
        ("fn compute(x: int) -> int { x * 3 + 1 }", 17),
        (
            "fn compute(x: int) -> int { if x > 0 { x + 2 } else { -x } }",
            -8,
        ),
        (
            "fn compute(x: int) -> int { let mut sum = 0; let mut i = 0; loop { if i >= x { break; }; sum += i; i += 1; }; sum }",
            30,
        ),
        (
            "fn twice(x: int) -> int { x + x } fn compute(x: int) -> int { twice(x) + twice(x + 1) }",
            8,
        ),
        (
            "fn bump(x: &mut int) { x += 1; } fn compute(x: int) -> int { let mut y = x; bump(y); y }",
            9,
        ),
        ("fn compute(x: int) -> int { x + 1 }", isize::MAX),
        (
            "fn compute(x: int) -> int { match x { 1 => 4, _ => 9 } }",
            1,
        ),
        (
            "use dependency::*; fn compute(x: int) -> int { adjust(x) }",
            5,
        ),
        (
            "fn compute(x: int) -> int { if x == 0 { 0 } else { compute(x - 1) + 1 } }",
            6,
        ),
        (
            "fn unit_arg(x: ()) -> int { 3 } fn compute(x: int) -> int { unit_arg(()) + x }",
            7,
        ),
        (
            "#[inline(never)] fn exchange(x: &mut int, y: &mut int) { let old = x; x = y; y = old; } fn compute(x: int) -> int { let mut a = x; let mut b = x + 3; exchange(a, b); a * 10 + b }",
            7,
        ),
        (
            "fn compute(x: int) -> int { let mut n = 0; let mut sum = 0; loop { if n >= x { break; }; if n < 10 { sum += n; } else { sum -= n; }; n += 1; }; sum }",
            30,
        ),
    ];
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(optimization);
        session
            .compile(
                "pub fn adjust(x: int) -> int { x * 7 - 2 }",
                "dependency",
                Path::single(ustr("dependency")),
            )
            .unwrap();
        for (source, input) in cases {
            differential::<isize, isize>(&mut session, source, input);
        }
        differential::<Float, Float>(
            &mut session,
            "fn compute(x: float) -> float { x * 1.5 + 2.0 }",
            Float::new(3.5).unwrap(),
        );
        differential::<bool, bool>(&mut session, "fn compute(x: bool) -> bool { not x }", true);
        differential::<Float, Float>(
            &mut session,
            "#[inline(never)] fn adjust(x: &mut float) { x += 0.25; } fn compute(x: float) -> float { let mut y = x; adjust(y); y * 2.0 }",
            Float::new(3.5).unwrap(),
        );
        differential::<isize, ()>(&mut session, "fn compute(x: int) { let y = x + 1; () }", 1);
        differential::<(), isize>(&mut session, "fn compute(x: ()) -> int { 42 }", ());
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_typed_binding_and_direct_calls() {
    let mut session = CompilerSession::new();
    let entry = compile(&mut session, "fn compute(x: int, y: int) -> int { x + y }");
    let code = CompiledProgram::compile(&session, entry).unwrap();
    assert_eq!(
        code.bytes(),
        CompiledProgram::compile(&session, entry).unwrap().bytes()
    );
    assert!(code.instantiate::<(Float, isize), isize>().is_err());
    assert!(code.instantiate::<(isize, isize), bool>().is_err());
    let mut instance = code.instantiate::<(isize, isize), isize>().unwrap();
    // SAFETY: this Rust callback uses only integer locals and direct guest calls, with no cleanup
    // guards or owned resources in frames which a trap could interrupt.
    let result = unsafe {
        instance.with_invocation(WasmLimits::default(), |function| {
            let mut result = 0;
            for i in 0..1000 {
                result = function.call((result, i));
            }
            result
        })
    }
    .unwrap();
    assert_eq!(result, 499500);
    drop(instance);
    // Rebinding exercises slot reclamation without retaining a stale function pointer.
    let mut instance = code.instantiate::<(isize, isize), isize>().unwrap();
    assert_eq!(instance.run((20, 22), WasmLimits::default()).unwrap(), 42);
    let entry = compile(&mut session, "fn compute() -> int { 7 }");
    assert_eq!(
        CompiledProgram::compile(&session, entry)
            .unwrap()
            .instantiate::<(), isize>()
            .unwrap()
            .run((), WasmLimits::default())
            .unwrap(),
        7
    );
    let entry = compile(
        &mut session,
        "struct Empty {} fn compute() -> Empty { Empty {} }",
    );
    assert!(CompiledProgram::compile(&session, entry).is_err());
}

#[wasm_bindgen_test]
fn wasm_codegen_limits_and_rejection() {
    let mut session = CompilerSession::new();
    let entry = compile(
        &mut session,
        // The mutable call forces an addressable slot, so this still tests the memory-stack limit
        // after non-address-observable recursion is promoted entirely to Wasm locals.
        "#[inline(never)] fn decrement(x: &mut int) { x -= 1; } fn compute(x: int) -> int { let mut n = x; if n == 0 { 0 } else { decrement(n); compute(n) + 1 } }",
    );
    let code = CompiledProgram::compile(&session, entry).unwrap();
    let mut instance = code.instantiate::<(isize,), isize>().unwrap();
    let limits = WasmLimits {
        execution: Default::default(),
        stack_bytes: 8,
    };
    assert!(matches!(
        instance.run((8,), limits).unwrap_err().kind(),
        RuntimeErrorKind::SandboxViolation(SandboxViolationKind::StackByteLimitExceeded { .. })
    ));
    let limits = WasmLimits {
        execution: WasmLimits::default().execution.with_call_depth_limit(4),
        ..WasmLimits::default()
    };
    // A trap may abandon Rust frames but must not leak shadow-stack space. Scratch bytes are
    // reusable; the next invocation installs fresh stack bounds and budget state.
    for _ in 0..20 {
        let before = shadow_stack_probe();
        // SAFETY: the callback owns only Copy data, with no cleanup obligations on cancellation.
        let failure = unsafe {
            instance.with_invocation(limits, |function| {
                let mut scratch = [0_u64; 128];
                black_box(&mut scratch);
                let result = function.call((8,));
                black_box(&mut scratch);
                result
            })
        }
        .unwrap_err();
        assert_eq!(shadow_stack_probe(), before);
        assert!(matches!(
            failure.kind(),
            RuntimeErrorKind::SandboxViolation(SandboxViolationKind::CallDepthLimitExceeded { .. })
        ));
        assert_eq!(instance.run((2,), limits).unwrap(), 2);
    }
    // A retained larger scratch buffer must not relax a later invocation's smaller limit.
    assert!(matches!(
        instance
            .run(
                (2,),
                WasmLimits {
                    stack_bytes: 8,
                    ..limits
                }
            )
            .unwrap_err()
            .kind(),
        RuntimeErrorKind::SandboxViolation(SandboxViolationKind::StackByteLimitExceeded {
            limit: 8
        })
    ));
    let entry = compile(
        &mut session,
        "fn compute(x: int) -> int { let mut n = 0; loop { if n >= x { break; }; n += 1; }; n }",
    );
    let mut instance = CompiledProgram::compile(&session, entry)
        .unwrap()
        .instantiate::<(isize,), isize>()
        .unwrap();
    let limits = WasmLimits {
        execution: limits.execution.with_fuel_limit(Some(2)),
        ..limits
    };
    assert!(matches!(
        instance.run((100,), limits).unwrap_err().kind(),
        RuntimeErrorKind::SandboxViolation(SandboxViolationKind::FuelExhausted)
    ));
    assert_eq!(instance.run((3,), WasmLimits::default()).unwrap(), 3);
    let entry = compile(
        &mut session,
        "fn compute(x: int) -> int { if x == 0 { 1 } else { idiv(3, x) } }",
    );
    assert!(CompiledProgram::compile(&session, entry).is_err());
}

#[wasm_bindgen_test]
fn wasm_codegen_dispatch_and_local_storage() {
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(optimization);
        for (source, dispatched) in [
            ("fn compute(x: int) -> int { x * 3 + 1 }", false),
            (
                "fn compute(x: int) -> int { let mut n = 0; loop { if n >= x { break; }; n += 1; }; n }",
                true,
            ),
        ] {
            let entry = compile(&mut session, source);
            let code = CompiledProgram::compile(&session, entry).unwrap();
            // The entry is emitted first; exclude setup's reads of the host invocation state.
            let body = Parser::new(0)
                .parse_all(code.bytes())
                .find_map(|payload| match payload.unwrap() {
                    Payload::CodeSectionEntry(body) => Some(body),
                    _ => None,
                })
                .unwrap();
            let mut dispatches = 0;
            let mut loops = 0;
            for op in body.get_operators_reader().unwrap() {
                match op.unwrap() {
                    Operator::BrTable { .. } => dispatches += 1,
                    Operator::Loop { .. } => loops += 1,
                    Operator::I32Load { .. }
                    | Operator::I32Load8U { .. }
                    | Operator::F64Load { .. } => panic!("scalar storage was not promoted"),
                    Operator::I32Store { memarg } => {
                        assert_eq!(
                            memarg.offset,
                            offset_of!(InvocationState, failure) as u64,
                            "only failure diagnostics may write memory"
                        )
                    }
                    Operator::I32Store8 { .. } | Operator::F64Store { .. } => {
                        panic!("unexpected scalar spill")
                    }
                    _ => (),
                }
            }
            assert_eq!(dispatches, usize::from(dispatched));
            assert_eq!(loops, usize::from(dispatched));
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_inactive_entry_does_not_write_memory() {
    let mut session = CompilerSession::new();
    // Force a memory frame so the raw call reaches fail() with no active invocation. A pure
    // leaf using only locals need not encounter any sandbox check at all.
    let entry = compile(
        &mut session,
        "#[inline(never)] fn bump(x: &mut int) { x += 1; } fn compute(x: int) -> int { let mut y = x; bump(y); y }",
    );
    let program = session.prepare_physical_program(entry.module).unwrap();
    let mut imports = Imports::new().unwrap();
    let emitted = emit::emit(&program, entry, &mut imports).unwrap();
    let module = WebAssembly::Module::new(&Uint8Array::from(emitted.bytes.as_slice())).unwrap();
    let instance = WebAssembly::Instance::new(&module, imports.object()).unwrap();
    let entry: JsFunction = Reflect::get(&instance.exports(), &"entry".into())
        .unwrap()
        .dyn_into()
        .unwrap();
    let memory: WebAssembly::Memory = wasm_bindgen::memory().dyn_into().unwrap();
    let bytes = Uint8Array::new(&memory.buffer());
    let before = bytes.slice(0, 64).to_vec();
    // Deliberately bypass the Rust binding to exercise the generated entry's inactive guard.
    assert!(entry.call1(&JsValue::UNDEFINED, &1.into()).is_err());
    assert_eq!(bytes.slice(0, 64).to_vec(), before);
}
