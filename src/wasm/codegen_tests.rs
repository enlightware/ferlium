// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{cell::Cell, fmt::Debug, hint::black_box, mem::offset_of, ptr};

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
    execution::ReferenceInterpreterLimits,
    hir::{
        function::Function,
        native_functions::{
            NativeAddressorMut, NativeAddressorRef, NativeFnN, NativeFnNN, NativeOptionalFnN,
        },
        value::{NativeValueType, Value},
    },
    mir::physical::{
        lower_physical_mir, lower_unoptimized_physical_mir,
        program::{ResolvedPhysicalProgram, resolve_physical_program},
    },
    module::{FunctionId, Module, Path},
    std::{math::Float, option::option_type, string::String},
    types::{
        effects::{PrimitiveEffect, effect, no_effects},
        r#type::Type,
    },
    ustr,
};

use super::{
    CompiledProgram, Imports, WasmLimits, WasmValue,
    callable_environment::LIVE_ENVIRONMENTS as LIVE_CALLABLE_ENVIRONMENTS,
    emit,
    evidence::{BUILT_ENVIRONMENTS, DictionaryDescriptor, LIVE_ENVIRONMENTS},
    execution::{ENTRY_EXPORT, InvocationState},
};

thread_local! { static DROP_LOG: Cell<isize> = const { Cell::new(0) }; }

fn record_drop(value: isize) {
    DROP_LOG.set(DROP_LOG.get() * 10 + value);
}

// Observe the address of a real Rust shadow-stack slot without exporting runtime internals.
#[inline(never)]
fn shadow_stack_probe() -> usize {
    let mut slot = 0_u64;
    black_box(ptr::from_mut(&mut slot)) as usize
}

fn compile(session: &mut CompilerSession, source: &str) -> FunctionId {
    let output = session
        .compile(source, "wasm_test", Path::single(ustr("wasm_test")))
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    let module = session.expect_fresh_module(output.module_id);
    FunctionId::new(
        output.module_id,
        module.get_local_function_id(ustr("compute")).unwrap(),
    )
}

/// Bypass session specialization so backend tests exercise the retained generic bodies themselves.
fn compile_raw(session: &CompilerSession, entry: FunctionId) -> CompiledProgram {
    with_raw_program(session, entry, |program| {
        CompiledProgram::from_physical(session, program, entry).unwrap()
    })
}

pub(super) fn with_raw_program<T>(
    session: &CompilerSession,
    entry: FunctionId,
    run: impl FnOnce(&ResolvedPhysicalProgram<'_>) -> T,
) -> T {
    let prepared = session.prepare_physical_program(entry.module).unwrap();
    let artifacts = prepared
        .modules()
        .iter()
        .map(|module| {
            let id = module.module();
            let raw = session
                .mir_artifacts_for(id, MirOptimization::Disabled)
                .unwrap();
            let lower = match session.physical_mir_optimization() {
                MirOptimization::Disabled => lower_unoptimized_physical_mir,
                MirOptimization::Enabled => lower_physical_mir,
            };
            lower(
                id,
                raw,
                session.modules().env_for(session.expect_fresh_module(id)),
                session.known_callees(),
            )
            .unwrap()
        })
        .collect::<Vec<_>>();
    let program = resolve_physical_program(artifacts.iter()).unwrap();
    run(&program)
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
    for code in [
        compile_raw(session, entry),
        CompiledProgram::compile(session, entry).unwrap_or_else(|e| panic!("{source}: {e:?}")),
    ] {
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
    }
    reference.discard_storage();
}

#[wasm_bindgen_test]
fn wasm_codegen_stored_functions_and_closures() {
    let cases = [
        "fn increment(x: int) -> int { x + 1 } #[inline(never)] fn apply<T>(f: (T) -> T, x: T) -> T { f(x) } fn compute(x: int) -> int { apply(increment, x) }",
        "fn compute(x: int) -> int { let f = |y| y + x; f(2) + f(3) }",
        "fn maker(x: int) { |y| y + x } fn compute(x: int) -> int { let f = maker(x); let g = f; f(2) + g(3) }",
        "fn id<T>(x: T) -> T { x } fn compute(x: int) -> int { let f = id; f(x) }",
        "fn maker<T>(x: T) { || x } fn compute(x: int) -> int { let f = maker((x, true)); f().0 }",
        "fn compute(x: int) -> int { let text = \"hello\"; let f = || len(text) + x; let g = f; f() + g() }",
        "#[inline(never)] fn apply(f: (&mut int) -> (), x: &mut int) { f(x) } fn bump(x: &mut int) { x += 1; } fn compute(x: int) -> int { let mut y = x; apply(bump, y); y }",
        "fn compute(x: int) -> int { let f = idiv; f(x, 2) }",
        "#[inline(never)] fn show<T>(x: T) -> int { let f = to_string; len(f(x)) } fn compute(x: int) -> int { show(x) }",
        "fn make<T, U>(a: T, b: U) { || (a, b) } fn compute(x: int) -> int { let f = make(true, (x, \"text\")); let p = f(); p.1.0 + len(p.1.1) }",
        "fn compute(x: int) -> int { let f = || x; let g = || f() + 1; let h = g; g() + h() }",
        "fn compute(x: int) -> int { let mut f = || x; for i in 0..4 { f = || i; }; f() }",
        "fn compute(x: int) -> int { let a = (); let f = || a; f(); x }",
        "fn negate(x: bool) -> bool { not x } #[inline(never)] fn apply<T>(f: (T) -> T, x: T) -> T { f(x) } fn compute(x: int) -> int { if apply(negate, x > 0) { 1 } else { 2 } }",
        "fn half(x: float) -> float { x * 0.5 } #[inline(never)] fn apply<T>(f: (T) -> T, x: T) -> T { f(x) } fn compute(x: int) -> int { if apply(half, 6.0) == 3.0 { x } else { 0 } }",
        "fn compute(x: int) -> int { let mut y = x; let f = || { y += 1; y }; f() + f() + y }",
        "fn maker<T, U>(a: T, b: U) { || (a, b) } fn compute(x: int) -> int { let f = maker(true, (x, 1.5)); let p = f(); if p.0 { p.1.0 } else { 0 } }",
        "fn compute(x: int) -> int { let function: Option<(int) -> int> = None; let pair = (function, function); x }",
    ];
    for mode in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_physical_mir_optimization(mode);
        for source in cases {
            let before = LIVE_CALLABLE_ENVIRONMENTS.get();
            differential::<isize, isize>(&mut session, source, 7);
            assert_eq!(LIVE_CALLABLE_ENVIRONMENTS.get(), before, "{source}");
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_closure_cleanup() {
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_allow_unsafe(true);
        session.set_physical_mir_optimization(optimization);
        let path = Path::single_str("probe");
        let mut module = Module::new(session.modules().next_id(), path.clone());
        module.add_function(
            ustr("record"),
            NativeFnN::from_rust(record_drop).description(
                ["id"],
                "",
                effect(PrimitiveEffect::Write),
            ),
        );
        session.register_module(path, module);
        let entry = compile(
            &mut session,
            r#"
            struct Probe(int)
            impl Value for Probe {
                fn eq(a: Probe, b: Probe) -> bool { a.0 == b.0 }
                fn to_string(p: Probe) -> string { to_string(p.0) }
                fn hash(p: Probe, h: &mut hasher) { hash(p.0, h) }
                fn clone(p: Probe) -> Probe { Probe(p.0) }
                fn drop(p: &mut Probe) {
                    effects_unsafe {
                        probe::record(p.0 + 1);
                        if p.0 == 2 { loop {} }
                    }
                }
            }
            fn maker(p: Probe) { || idiv(20, if p.0 == 2 { 0 } else { p.0 }) }
            fn compute(x: int) -> int {
                let p = Probe(x);
                let f = maker(p);
                let g = f;
                g()
            }
        "#,
        );
        let limits = ReferenceInterpreterLimits::default().with_fuel_limit(Some(300));
        for code in [
            compile_raw(&session, entry),
            CompiledProgram::compile(&session, entry).unwrap(),
        ] {
            let mut instance = code.instantiate::<(isize,), isize>().unwrap();
            for input in [4, 0, 2, 4] {
                DROP_LOG.set(0);
                let expected = session
                    .run_entry_with_limits(
                        ExecutionTarget::PhysicalMir,
                        entry.module,
                        entry.function,
                        vec![Value::native(input)],
                        limits,
                    )
                    .map(|value| {
                        let result = *value.as_primitive_ty::<isize>().unwrap();
                        value.discard_storage();
                        result
                    })
                    .map_err(|error| error.kind());
                let log = DROP_LOG.get();
                DROP_LOG.set(0);
                let live = LIVE_CALLABLE_ENVIRONMENTS.get();
                let evidence = LIVE_ENVIRONMENTS.get();
                let actual = instance
                    .run(
                        (input,),
                        WasmLimits {
                            execution: limits.execution,
                            ..WasmLimits::default()
                        },
                    )
                    .map_err(|error| error.kind());
                assert_eq!(actual, expected, "input {input}");
                assert_eq!(DROP_LOG.get(), log, "input {input}");
                if input != 2 {
                    assert_eq!(LIVE_CALLABLE_ENVIRONMENTS.get(), live);
                    assert_eq!(LIVE_ENVIRONMENTS.get(), evidence);
                }
            }
        }
    }
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
fn wasm_codegen_generic_evidence_and_buffers() {
    let sources = [
        "#[inline(never)] fn identity<T>(x: T) -> T { x } fn compute(x: int) -> int { identity(x) }",
        "#[inline(never)] fn identity<T>(x: T) -> T { x } fn compute(x: int) -> int { let p = identity((x, x + 2)); p.0 + p.1 }",
        "trait Tag<Self> { fn tag(value: Self) -> int; } impl Tag for int { fn tag(value: int) -> int { value + 1 } } #[inline(never)] fn tagged<T>(x: T) -> int where T: Tag { tag(x) } fn compute(x: int) -> int { tagged(x) }",
        "fn compute(x: int) -> int { let mut a = [x, x + 1]; array_append(a, x + 2); a[0] + a[2] }",
        "#[inline(never)] fn duplicate<T>(x: T) -> (T, T) { (x, x) } fn compute(x: int) -> int { let p = duplicate((x, true)); if p.1.1 { p.0.0 } else { 0 } }",
        "#[inline(never)] fn repeat<T>(x: T) -> T { let mut n = 0; loop { let pair = (x, x); if n == 3 { return pair.0; }; n += 1; } } fn compute(x: int) -> int { repeat(x) }",
        "#[inline(never)] fn replace<T>(x: &mut T, y: T) { x = y; } fn compute(x: int) -> int { let mut p = (1, false); replace(p, (x, true)); p.0 }",
        "#[inline(never)] fn make_array<T>(x: T) -> [T] { let mut a = [x]; array_append(a, x); a } fn compute(x: int) -> int { let a = make_array(x); a[1] }",
        "fn compute(x: int) -> int { let mut a = []; let mut n = 0; loop { if n >= 100 { break; }; array_append(a, to_string(n)); n += 1; }; let b = a; let expected = to_string(x); if b[7] == expected { len(b) } else { 0 } }",
        "fn compute(x: int) -> int { let mut a = [()]; let mut n = 0; loop { if n >= x { break; }; array_append(a, ()); n += 1; }; len(a) }",
        "trait Mix<Self> { fn mix(x: Self, n: int, flag: bool, factor: float) -> int; } impl Mix for int { fn mix(x: int, n: int, flag: bool, factor: float) -> int { if flag and factor == 2.0 { x + n } else { 0 } } } #[inline(never)] fn forward<T>(x: T) -> int where T: Mix { mix(x, 3, true, 2.0) } fn compute(x: int) -> int { forward(x) }",
        "enum Maybe<T> { Empty, Full(T) } #[inline(never)] fn make<T>(x: T) -> Maybe<T> { Maybe::Full(x) } #[inline(never)] fn duplicate<T>(x: T) -> (T, T) { (x, x) } fn compute(x: int) -> int { match duplicate(make((x, true))).0 { Maybe::Empty => 0, Maybe::Full(p) => p.0 } }",
    ];
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        for source in sources {
            let mut session = CompilerSession::new();
            session.set_mir_optimization(optimization);
            session.set_physical_mir_optimization(optimization);
            let before = LIVE_ENVIRONMENTS.get();
            differential::<isize, isize>(&mut session, source, 7);
            assert_eq!(LIVE_ENVIRONMENTS.get(), before);
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_witnessed_layout_shares_descriptor_lookup() {
    let mut session = CompilerSession::new();
    session.set_mir_optimization(MirOptimization::Disabled);
    session.set_physical_mir_optimization(MirOptimization::Disabled);
    let entry = compile(
        &mut session,
        "#[inline(never)] fn replace<T>(x: &mut T, y: T) { x = y; } fn compute(x: int) -> int { let mut p = (1, false); replace(p, (x, true)); p.0 }",
    );
    let code = compile_raw(&session, entry);
    let mut lookups = 0;
    let mut calls = 0;
    for payload in Parser::new(0).parse_all(code.bytes()) {
        if let Payload::CodeSectionEntry(body) = payload.unwrap() {
            let ops = body
                .get_operators_reader()
                .unwrap()
                .into_iter()
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            calls += ops
                .iter()
                .filter(|op| matches!(op, Operator::CallIndirect { .. }))
                .count();
            // Descriptor-relative loads follow the addition of the evidence-image base. Loads
            // of individual table entries instead use the cached table address directly.
            lookups += ops
                .windows(2)
                .filter(|ops| {
                    matches!(ops,
                        [Operator::I32Add, Operator::I32Load { memarg }]
                            if memarg.offset == offset_of!(DictionaryDescriptor, entries) as u64
                    )
                })
                .count();
        }
    }
    assert!(lookups > 0);
    assert!(
        lookups < calls,
        "size and alignment must share their descriptor lookup: {lookups} lookups, {calls} calls"
    );
    assert_eq!(
        code.instantiate::<(isize,), isize>()
            .unwrap()
            .run((7,), WasmLimits::default())
            .unwrap(),
        7
    );
}

#[wasm_bindgen_test]
fn wasm_codegen_generic_evidence_cleanup() {
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(optimization);
        let entry = compile(
            &mut session,
            r#"
            #[inline(never)] fn fail<T>(value: T, divisor: int) -> int {
                let values = [(value, value)];
                idiv(len(values), divisor)
            }
            fn compute(x: int) -> int { fail(to_string(x), x) }
        "#,
        );
        let code = compile_raw(&session, entry);
        let mut first = code.instantiate::<(isize,), isize>().unwrap();
        let mut second = code.instantiate::<(isize,), isize>().unwrap();
        // Each instance owns its relocated immutable data, independently of the compiled artifact.
        drop(code);
        for input in [0_isize, 1, 0, 2] {
            let expected = session
                .run_entry(
                    ExecutionTarget::PhysicalMir,
                    entry.module,
                    entry.function,
                    vec![Value::native(input)],
                )
                .map(|value| {
                    let result = *value.as_primitive_ty::<isize>().unwrap();
                    value.discard_storage();
                    result
                });
            for instance in [&mut first, &mut second] {
                let before = LIVE_ENVIRONMENTS.get();
                let built = BUILT_ENVIRONMENTS.get();
                let actual = instance.run((input,), WasmLimits::default());
                assert_eq!(
                    actual.as_ref().map_err(|e| e.kind()),
                    expected.as_ref().map_err(|e| e.kind())
                );
                assert_eq!(LIVE_ENVIRONMENTS.get(), before);
                assert!(BUILT_ENVIRONMENTS.get() > built);
            }
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_captured_trait_evidence() {
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(optimization);
        session
            .compile(
                r#"
            pub trait Tag<Self> { fn tag(value: Self) -> int; }
            impl Tag for int { fn tag(value: int) -> int { value } }
            pub struct Wrapper<T>(T)
            impl<T> Tag for Wrapper<T> where T: Tag, T: Value {
                fn tag(value: Wrapper<T>) -> int { tag(value.0) + 1 }
            }
            pub fn forward<T>(value: T) -> int where T: Tag, T: Value { tag(value) }
        "#,
                "captured",
                Path::single_str("captured"),
            )
            .unwrap();
        differential::<isize, isize>(
            &mut session,
            "use captured::*; fn compute(x: int) -> int { forward(Wrapper(Wrapper(x))) }",
            7,
        );
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_native_dictionary_adapters() {
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(optimization);
        let traits = session.compile(
            "pub trait Probe<Self> { fn maybe(x: Self) -> Option<string>; fn add_offset(x: Self, y: int) -> int; }",
            "traits", Path::single_str("traits"),
        ).unwrap().module_id;
        let source = session.expect_fresh_module(traits);
        let trait_id = source.get_trait_id(ustr("Probe")).unwrap();
        let definition = source.get_trait(ustr("Probe")).unwrap();
        let path = Path::single_str("native_probe");
        let mut module = Module::new(session.modules().next_id(), path.clone());
        module.add_concrete_impl_for_trait_def_no_locals(
            trait_id,
            definition,
            [Type::primitive::<isize>()],
            [],
            [],
            [
                Box::new(NativeOptionalFnN::from_rust(
                    |x: isize| (x > 0).then(|| String::from(x.to_string())),
                    option_type(Type::primitive::<String>()),
                )) as Function,
                Box::new(NativeFnNN::from_rust(|x: isize, y: isize| x + y)) as Function,
            ],
        );
        session.register_module(path, module);
        for input in [0, 4] {
            differential::<isize, isize>(
                &mut session,
                r#"
                use traits::*; use native_probe::*;
                #[inline(never)] fn forward<T>(x: T) -> int where T: Probe {
                            let n = add_offset(x, 3);
                    match maybe(x) { None => n, Some(text) => n + len(text) }
                }
                fn compute(x: int) -> int { forward(x) }
            "#,
                input,
            );
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_native_addressors() {
    unsafe extern "C" fn shared(value: *const String) -> *const String {
        value
    }
    unsafe extern "C" fn mutable(value: *mut String) -> *mut String {
        value
    }
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(optimization);
        let path = Path::single_str("native_members");
        let mut module = Module::new(session.modules().next_id(), path.clone());
        // SAFETY: identity projections remain rooted and allow ordinary string replacement.
        unsafe {
            module.add_native_member(
                ustr("native_self"),
                Some(NativeAddressorRef::new(shared).description(["self"], "", no_effects())),
                Some(NativeAddressorMut::new(mutable).description(["self"], "", no_effects())),
            );
        }
        session.register_module(path, module);
        differential::<isize, isize>(
            &mut session,
            r#"
                use native_members::*;
                fn compute(x: int) -> int {
                    let mut text = "before";
                    let before = len(text.native_self);
                    text.native_self = to_string(x);
                    before + len(text.native_self)
                }
            "#,
            123,
        );
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
    // Entries need no source name: the top-level expression is compiler-generated.
    let module = session
        .compile(
            "fn compute() -> int { 7 }\ncompute() + 1",
            "wasm_test",
            Path::single(ustr("wasm_test")),
        )
        .unwrap()
        .module_id;
    let expression = session
        .expect_fresh_module(module)
        .get_local_function_id(ustr("<expr>"))
        .unwrap();
    assert_eq!(
        CompiledProgram::compile(&session, FunctionId::new(module, expression))
            .unwrap()
            .instantiate::<(), isize>()
            .unwrap()
            .run((), WasmLimits::default())
            .unwrap(),
        8
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
}

#[wasm_bindgen_test]
fn wasm_codegen_managed_differential() {
    // Bridge coverage until generated Wasm joins the shared language-suite harness.
    let cases = [
        "#[inline(never)] fn pair(x: int) -> (int, bool) { (x + 2, true) } fn compute(x: int) -> int { let p = pair(x); if p.1 { p.0 } else { 0 } }",
        "struct Pair { a: int, b: float } #[inline(never)] fn update(p: &mut Pair) { p.a += 2; p.b += 1.0; } fn compute(x: int) -> int { let mut p = Pair { a: x, b: 2.0 }; update(p); p.a }",
        "fn compute(x: int) -> int { let s = to_string(x); let copy = s; if s == copy { 1 } else { 0 } }",
        "#[inline(never)] fn pair(x: int) -> (string, int) { (to_string(x), x) } fn compute(x: int) -> int { let p = pair(x); let copy = p; if p.0 == copy.0 { copy.1 } else { 0 } }",
        "fn compute(x: int) -> int { let mut s = to_string(x); let mut i = 0; loop { if i >= x { break; }; s = string_concat(s, \"!\"); i += 1; }; if s == \"4!!!!\" { 1 } else { 0 } }",
        "fn compute(x: int) -> int { let mut s = \"hello\"; string_push_str(s, \" world\"); if s == \"hello world\" { x } else { 0 } }",
        "#[inline(never)] fn divide(x: int) -> int { idiv(20, x) } fn compute(x: int) -> int { let s = to_string(x); let result = divide(x); if s == to_string(x) { result } else { 0 } }",
    ];
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(optimization);
        for source in cases {
            differential::<isize, isize>(&mut session, source, 4);
        }
        let entry = compile(&mut session, cases.last().unwrap());
        let expected = session
            .run_entry(
                ExecutionTarget::PhysicalMir,
                entry.module,
                entry.function,
                vec![Value::native(0_isize)],
            )
            .unwrap_err();
        let mut instance = CompiledProgram::compile(&session, entry)
            .unwrap()
            .instantiate::<(isize,), isize>()
            .unwrap();
        for _ in 0..3 {
            assert_eq!(
                instance
                    .run((0,), WasmLimits::default())
                    .unwrap_err()
                    .kind(),
                expected.kind()
            );
            assert_eq!(instance.run((4,), WasmLimits::default()).unwrap(), 5);
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_variant_differential() {
    // Bridge coverage until generated Wasm joins the shared language-suite harness.
    let cases = [
        "enum Choice { Empty, Number(int), Real(float) } #[inline(never)] fn choose(x: int) -> Choice { if x == 0 { Choice::Empty } else if x == 1 { Choice::Real(2.5) } else { Choice::Number(x) } } fn compute(x: int) -> int { match choose(x) { Choice::Empty => 7, Choice::Number(n) => n + 1, Choice::Real(f) => if f == 2.5 { 8 } else { 9 } } }",
        "fn compute(x: int) -> int { let v = if x == 0 { Empty } else { Text(to_string(x)) }; let copy = v; match copy { Empty => 7, Text(s) => if s == to_string(x) { x } else { 0 } } }",
        "enum Text { Empty, Full(string) } #[inline(never)] fn change(v: &mut Text, x: int) { v = Text::Full(to_string(x)); } fn compute(x: int) -> int { let mut v = Text::Empty; change(v, x); match v { Text::Empty => 0, Text::Full(s) => if s == to_string(x) { x } else { 0 } } }",
        "enum List { Nil, Cons(string, List) } #[inline(never)] fn build(x: int) -> List { if x == 0 { List::Nil } else { List::Cons(to_string(x), build(x - 1)) } } #[inline(never)] fn count(l: List) -> int { match l { List::Nil => 0, List::Cons(s, tail) => count(tail) + 1 } } fn compute(x: int) -> int { let l = build(x); let copy = l; count(copy) + count(l) }",
    ];
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(optimization);
        for source in cases {
            for input in [0, 1, 4] {
                differential::<isize, isize>(&mut session, source, input);
            }
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_optional_native_results() {
    // Bridge coverage for the native presence/payload ABI, including an absent reused result.
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(optimization);
        let path = Path::single_str("probe");
        let mut module = Module::new(session.modules().next_id(), path.clone());
        module.add_function(
            ustr("integer"),
            NativeOptionalFnN::from_rust(
                |x: isize| (x > 0).then_some(x + 1),
                option_type(Type::primitive::<isize>()),
            )
            .description(["x"], "", Default::default()),
        );
        module.add_function(
            ustr("real"),
            NativeOptionalFnN::from_rust(
                |x: isize| (x > 0).then(|| Float::new(2.5).unwrap()),
                option_type(Type::primitive::<Float>()),
            )
            .description(["x"], "", Default::default()),
        );
        module.add_function(
            ustr("text"),
            NativeOptionalFnN::from_rust(
                |x: isize| (x > 0).then(|| String::from(x.to_string())),
                option_type(Type::primitive::<String>()),
            )
            .description(["x"], "", Default::default()),
        );
        module.add_function(
            ustr("unit"),
            NativeOptionalFnN::from_rust(
                |x: isize| (x > 0).then_some(()),
                option_type(Type::unit()),
            )
            .description(["x"], "", Default::default()),
        );
        session.register_module(path, module);
        for source in [
            "fn compute(x: int) -> int { match probe::integer(x) { None => 7, Some(n) => n } }",
            "fn compute(x: int) -> int { match probe::real(x) { None => 7, Some(f) => if f == 2.5 { x } else { 0 } } }",
            "fn compute(x: int) -> int { let v = probe::text(x); let copy = v; match copy { None => 7, Some(s) => if s == to_string(x) { x } else { 0 } } }",
            "fn compute(x: int) -> int { match probe::unit(x) { None => 7, Some(u) => x } }",
            "fn compute(x: int) -> int { let mut v = probe::text(x); let mut n = x; loop { if n <= 0 { break; }; n -= 1; v = probe::text(n); }; match v { None => 7, Some(s) => 0 } }",
        ] {
            for input in [0, 4] {
                differential::<isize, isize>(&mut session, source, input);
            }
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_cleanup_failures() {
    // Backend invariant: source cleanup runs, but poisoning never executes the outer destructor.
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_allow_unsafe(true);
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(optimization);
        let path = Path::single_str("probe");
        let mut module = Module::new(session.modules().next_id(), path.clone());
        module.add_function(
            ustr("record"),
            NativeFnN::from_rust(record_drop).description(
                ["id"],
                "",
                effect(PrimitiveEffect::Write),
            ),
        );
        session.register_module(path, module);
        let entry = compile(
            &mut session,
            r#"
            struct Probe(int)
            impl Value for Probe {
                fn eq(a: Probe, b: Probe) -> bool { a.0 == b.0 }
                fn to_string(p: Probe) -> string { to_string(p.0) }
                fn hash(p: Probe, h: &mut hasher) { hash(p.0, h) }
                fn clone(p: Probe) -> Probe { Probe(p.0) }
                fn drop(p: &mut Probe) {
                    effects_unsafe {
                        probe::record(p.0);
                        if p.0 == 2 { loop {} }
                    }
                }
            }
            fn compute(x: int) -> int {
                let outer = Probe(9);
                let inner = Probe(x);
                idiv(20, if x <= 3 { 0 } else { x })
            }
        "#,
        );
        let mut instance = CompiledProgram::compile(&session, entry)
            .unwrap()
            .instantiate::<(isize,), isize>()
            .unwrap();
        let limits = ReferenceInterpreterLimits::default().with_fuel_limit(Some(100));
        for (input, log) in [(4, 49), (3, 39), (2, 2), (4, 49)] {
            DROP_LOG.set(0);
            let expected = session
                .run_entry_with_limits(
                    ExecutionTarget::PhysicalMir,
                    entry.module,
                    entry.function,
                    vec![Value::native(input)],
                    limits,
                )
                .map(|value| {
                    let result = *value.as_primitive_ty::<isize>().unwrap();
                    value.discard_storage();
                    result
                });
            assert_eq!(DROP_LOG.get(), log);
            DROP_LOG.set(0);
            let actual = instance.run(
                (input,),
                WasmLimits {
                    execution: limits.execution,
                    ..WasmLimits::default()
                },
            );
            assert_eq!(
                actual.as_ref().map_err(|e| e.kind()),
                expected.as_ref().map_err(|e| e.kind())
            );
            assert_eq!(DROP_LOG.get(), log);
            if input == 2 {
                assert!(
                    actual
                        .unwrap_err()
                        .sandbox_violation()
                        .unwrap()
                        .interrupted_source_failure()
                        .is_some()
                );
            }
        }
        // Fixed Value adapters must not charge extra source call-depth frames for destruction.
        for depth in 2..8 {
            DROP_LOG.set(0);
            let limits = limits.with_call_depth_limit(depth);
            let expected = session
                .run_entry_with_limits(
                    ExecutionTarget::PhysicalMir,
                    entry.module,
                    entry.function,
                    vec![Value::native(4_isize)],
                    limits,
                )
                .map(|value| value.discard_storage())
                .map_err(|error| error.kind());
            DROP_LOG.set(0);
            let actual = instance
                .run(
                    (4,),
                    WasmLimits {
                        execution: limits.execution,
                        ..WasmLimits::default()
                    },
                )
                .map(|_| ())
                .map_err(|error| error.kind());
            assert_eq!(actual, expected, "call-depth limit {depth}");
        }
    }
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
    let emitted = emit::emit(
        &program,
        &[entry],
        &[(entry, ENTRY_EXPORT.into())],
        &mut imports,
        &session,
    )
    .unwrap();
    let module = WebAssembly::Module::new(&Uint8Array::from(emitted.bytes.as_slice())).unwrap();
    let instance = WebAssembly::Instance::new(&module, imports.object()).unwrap();
    let entry: JsFunction = Reflect::get(&instance.exports(), &ENTRY_EXPORT.into())
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
