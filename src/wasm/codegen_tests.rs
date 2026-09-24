// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{cell::Cell, fmt::Debug, hint::black_box, mem::offset_of, ptr};

use js_sys::{Function as JsFunction, Reflect, Uint8Array, WebAssembly};
use wasm_bindgen::{JsCast, JsValue};
use wasm_bindgen_test::wasm_bindgen_test;
use wasmparser::{Operator, Parser, Payload};

use crate::{
    CompilerSession, FxHashSet, Location,
    compiler::{
        MirOptimization,
        error::{RuntimeErrorKind, SandboxViolationKind, SourceFailureKind},
    },
    execution::ReferenceInterpreterLimits,
    hir::{
        function::Function,
        native_functions::{
            NativeAddressorMut, NativeAddressorRef, NativeFnN, NativeFnNN, NativeOptionalFnN,
        },
    },
    mir::{
        BlockId, Operation, OperationKind, ParameterId, Value as MirValue,
        pass::stack_region::no_op_stack_markers,
        physical::{
            lower_physical_mir, lower_unoptimized_physical_mir,
            program::{ResolvedPhysicalProgram, resolve_physical_program},
        },
        terminator::TerminatorKind,
    },
    module::{FunctionId, LocalFunctionId, Module, Path, id::Id},
    std::{math::Float, option::option_type, string::String},
    types::{
        effects::{PrimitiveEffect, effect, no_effects},
        r#type::{CallImplType, FnType, Type},
    },
    ustr,
};

use super::{
    CompiledProgram, Imports, WasmLimits, WasmValue,
    callable_environment::LIVE_ENVIRONMENTS as LIVE_CALLABLE_ENVIRONMENTS,
    emit,
    evidence::{BUILT_ENVIRONMENTS, DictionaryDescriptor, LIVE_ENVIRONMENTS},
    execution::{ENTRY_EXPORT, InvocationState, run_boxed_entry},
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

fn physical_operations(
    program: &ResolvedPhysicalProgram<'_>,
    mut visit: impl FnMut(&Operation) -> bool,
) -> bool {
    for module in program.modules() {
        for index in 0..module.entry_count() {
            let Some(body) = module.get(LocalFunctionId::from_index(index)) else {
                continue;
            };
            for block in body.blocks() {
                let block = body.block(block);
                if block.operations().iter().any(&mut visit) {
                    return true;
                }
                if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind
                    && visit(operation)
                {
                    return true;
                }
            }
        }
    }
    false
}

fn wasm_operator_count(bytes: &[u8], mut matches: impl FnMut(&Operator<'_>) -> bool) -> usize {
    Parser::new(0)
        .parse_all(bytes)
        .filter_map(|payload| match payload.unwrap() {
            Payload::CodeSectionEntry(body) => Some(
                body.get_operators_reader()
                    .unwrap()
                    .into_iter()
                    .filter(|operation| matches(operation.as_ref().unwrap()))
                    .count(),
            ),
            _ => None,
        })
        .sum()
}

/// Instructions of a named exported function, independent of code-section ordering.
///
/// This follows the export exactly, so a fallible scalar entry resolves to its generated wrapper
/// rather than the wrapped Ferlium function.
fn exported_function_operators<'a>(bytes: &'a [u8], name: &str) -> Vec<Operator<'a>> {
    let mut imported_functions = 0usize;
    let mut function_index = None;
    for payload in Parser::new(0).parse_all(bytes) {
        match payload.unwrap() {
            Payload::ImportSection(section) => {
                imported_functions += section
                    .into_imports()
                    .filter(|import| {
                        matches!(
                            import.as_ref().unwrap().ty,
                            wasmparser::TypeRef::Func(_) | wasmparser::TypeRef::FuncExact(_)
                        )
                    })
                    .count();
            }
            Payload::ExportSection(section) => {
                for export in section {
                    let export = export.unwrap();
                    if export.name == name && export.kind == wasmparser::ExternalKind::Func {
                        function_index = Some(export.index as usize);
                    }
                }
            }
            _ => {}
        }
    }
    let body_index = function_index
        .expect("fixture must export its entry")
        .checked_sub(imported_functions)
        .expect("exported entry must be defined in the generated module");
    let body = Parser::new(0)
        .parse_all(bytes)
        .filter_map(|payload| match payload.unwrap() {
            Payload::CodeSectionEntry(body) => Some(body),
            _ => None,
        })
        .nth(body_index)
        .expect("exported entry must have a code body");
    body.get_operators_reader()
        .unwrap()
        .into_iter()
        .collect::<Result<_, _>>()
        .unwrap()
}

fn calls_borrowed_subscript_member(program: &ResolvedPhysicalProgram<'_>) -> bool {
    for module in program.modules() {
        for index in 0..module.entry_count() {
            let Some(body) = module.get(LocalFunctionId::from_index(index)) else {
                continue;
            };
            let borrowed = body
                .blocks()
                .flat_map(|block| {
                    let block = body.block(block);
                    block.operations().iter().chain(
                        if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
                            Some(operation)
                        } else {
                            None
                        },
                    )
                })
                .filter(|operation| {
                    matches!(operation.kind, OperationKind::BorrowSubscriptMember { .. })
                })
                .map(|operation| operation.result_id().unwrap())
                .collect::<Vec<_>>();
            if body.blocks().any(|block| {
                let block = body.block(block);
                block
                    .operations()
                    .iter()
                    .chain(
                        if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
                            Some(operation)
                        } else {
                            None
                        },
                    )
                    .any(|operation| {
                        matches!(operation.kind, OperationKind::Call { .. })
                            && matches!(operation.operands.first(), Some(MirValue::Register(id)) if borrowed.contains(id))
                    })
            }) {
                return true;
            }
        }
    }
    false
}

fn assert_wasm_runs<A: WasmValue + Copy, R: WasmValue + PartialEq + Debug>(
    session: &mut CompilerSession,
    source: &str,
    input: A,
    expected: R,
) {
    let entry = compile(session, source);
    for code in [
        compile_raw(session, entry),
        CompiledProgram::compile(session, entry).unwrap_or_else(|e| panic!("{source}: {e:?}")),
    ] {
        let mut instance = code
            .instantiate::<(A,), R>()
            .unwrap_or_else(|e| panic!("{source}: {e:?}"));
        for _ in 0..2 {
            assert_eq!(
                instance.run((input,), WasmLimits::default()).unwrap(),
                expected,
                "{source}"
            );
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_subscript_call_clone_and_stack_reclamation() {
    let first = r#"
        subscript first<T>(values: &mut [T]) -> T where T: Value {
            ref mut { values[0] }
        }
        fn compute(x: int) -> int {
            let accessor = first;
            let copied = accessor;
            let mut values = [x];
            let before = values->[accessor];
            values->[copied] = x + 3;
            before * 10 + values[0]
        }
    "#;
    let mut session = CompilerSession::new();
    session.set_allow_experimental(true);
    session.set_physical_mir_optimization(MirOptimization::Disabled);
    let entry = compile(&mut session, first);
    with_raw_program(&session, entry, |program| {
        assert!(physical_operations(program, |operation| matches!(
            operation.kind,
            OperationKind::CloneSubscriptEnv { .. }
        )));
        assert!(calls_borrowed_subscript_member(program));
    });
    let mut instance = compile_raw(&session, entry)
        .instantiate::<(isize,), isize>()
        .unwrap();
    assert_eq!(instance.run((5,), WasmLimits::default()).unwrap(), 58);

    let projections = "slot->[accessor] += 1;".repeat(64);
    let reclaim = r#"
        #[inline(never)]
        fn identity<T>(value: T) -> T { value }
        subscript cell<T>(slot: &mut T) -> T where T: Value {
            mut {
                let mut local = slot;
                yield local;
                let restored = identity(local);
                slot = restored
            }
        }
        fn compute(x: int) -> int {
            let accessor = cell;
            let mut slot = x;
            $PROJECTIONS
            slot
        }
    "#
    .replace("$PROJECTIONS", &projections);
    let mut session = CompilerSession::new();
    session.set_allow_experimental(true);
    session.set_mir_optimization(MirOptimization::Disabled);
    session.set_physical_mir_optimization(MirOptimization::Disabled);
    let entry = compile(&mut session, &reclaim);
    with_raw_program(&session, entry, |program| {
        let mut dynamic_after_yield = false;
        for module in program.modules() {
            for index in 0..module.entry_count() {
                let Some(body) = module.get(LocalFunctionId::from_index(index)) else {
                    continue;
                };
                for block in body.blocks() {
                    let TerminatorKind::Yield { resume, .. } = body.block(block).terminator().kind
                    else {
                        continue;
                    };
                    dynamic_after_yield |=
                        body.block(resume).operations().iter().any(|operation| {
                            matches!(operation.kind, OperationKind::Alloca { .. })
                                && !operation.operands.is_empty()
                        });
                }
            }
        }
        assert!(
            dynamic_after_yield,
            "regression requires a run-time-sized allocation after the yield"
        );
        assert!(
            !program
                .function(entry)
                .unwrap()
                .blocks()
                .flat_map(|block| program.function(entry).unwrap().block(block).operations())
                .any(|operation| matches!(operation.kind, OperationKind::StackRestore)),
            "the caller must not mask retained-frame leaks with its own stack restore"
        );
    });
    let mut instance = compile_raw(&session, entry)
        .instantiate::<(isize,), isize>()
        .unwrap();
    assert_eq!(
        instance
            .run(
                (5,),
                WasmLimits {
                    stack_bytes: 512,
                    ..WasmLimits::default()
                },
            )
            .unwrap(),
        69
    );
}

#[wasm_bindgen_test]
fn wasm_codegen_subscript_resume_failure() {
    let source = r#"
        subscript cell(slot: &mut int) -> int {
            mut {
                let mut local = slot;
                yield local;
                slot = local;
                let failure = [0][1];
            }
        }
        fn compute(x: int) -> int {
            let accessor = cell;
            let mut slot = x;
            slot->[accessor] = x + 1;
            slot
        }
    "#;
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_allow_experimental(true);
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(optimization);
        let entry = compile(&mut session, source);
        for code in [
            compile_raw(&session, entry),
            CompiledProgram::compile(&session, entry).unwrap(),
        ] {
            let environments = LIVE_CALLABLE_ENVIRONMENTS.get();
            let evidence = LIVE_ENVIRONMENTS.get();
            let error = code
                .instantiate::<(isize,), isize>()
                .unwrap()
                .run((5,), WasmLimits::default())
                .unwrap_err();
            assert_eq!(
                error.kind(),
                RuntimeErrorKind::SourceFailure(SourceFailureKind::Aborted(Some(
                    "Array access out of bounds: index 1 for length 1".into()
                )))
            );
            assert_eq!(LIVE_CALLABLE_ENVIRONMENTS.get(), environments);
            assert_eq!(LIVE_ENVIRONMENTS.get(), evidence);
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
                match input {
                    4 => assert_eq!(actual, Ok(5)),
                    0 => assert_eq!(
                        actual,
                        Err(RuntimeErrorKind::SourceFailure(
                            SourceFailureKind::DivisionByZero
                        ))
                    ),
                    2 => assert!(matches!(
                        actual,
                        Err(RuntimeErrorKind::SandboxViolation(
                            SandboxViolationKind::FuelExhausted
                        ))
                    )),
                    _ => unreachable!(),
                }
                assert_ne!(DROP_LOG.get(), 0, "input {input}");
                if input != 2 {
                    assert_eq!(LIVE_CALLABLE_ENVIRONMENTS.get(), live);
                    assert_eq!(LIVE_ENVIRONMENTS.get(), evidence);
                }
            }
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
            for instance in [&mut first, &mut second] {
                let before = LIVE_ENVIRONMENTS.get();
                let built = BUILT_ENVIRONMENTS.get();
                let actual = instance
                    .run((input,), WasmLimits::default())
                    .map_err(|error| error.kind());
                if input == 0 {
                    assert_eq!(
                        actual,
                        Err(RuntimeErrorKind::SourceFailure(
                            SourceFailureKind::DivisionByZero
                        ))
                    );
                } else {
                    assert_eq!(actual, Ok(1 / input));
                }
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
        assert_wasm_runs::<isize, isize>(
            &mut session,
            "use captured::*; fn compute(x: int) -> int { forward(Wrapper(Wrapper(x))) }",
            7,
            9,
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
        for (input, expected) in [(0, 3), (4, 8)] {
            assert_wasm_runs::<isize, isize>(
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
                expected,
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
        assert_wasm_runs::<isize, isize>(
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
            9,
        );
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_function_types_are_interned() {
    let mut session = CompilerSession::new();
    let entry = compile(&mut session, "fn compute(x: int, y: int) -> int { x + y }");
    let code = CompiledProgram::compile(&session, entry).unwrap();
    let mut types = Vec::new();
    let mut function_types = Vec::new();
    for payload in Parser::new(0).parse_all(code.bytes()) {
        match payload.unwrap() {
            Payload::TypeSection(section) => types.extend(
                section
                    .into_iter_err_on_gc_types()
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap(),
            ),
            Payload::ImportSection(section) => {
                function_types.extend(section.into_imports().filter_map(|import| {
                    match import.unwrap().ty {
                        wasmparser::TypeRef::Func(index)
                        | wasmparser::TypeRef::FuncExact(index) => Some(index),
                        _ => None,
                    }
                }));
            }
            Payload::FunctionSection(section) => {
                function_types.extend(section.into_iter().map(Result::unwrap));
            }
            _ => (),
        }
    }
    assert!(types.len() > 1, "fixture must emit several signatures");
    assert_eq!(
        types.len(),
        types.iter().collect::<FxHashSet<_>>().len(),
        "duplicate Wasm function types: {types:?}"
    );
    let integer_binary = types
        .iter()
        .position(|ty| {
            ty.params() == [wasmparser::ValType::I32, wasmparser::ValType::I32]
                && ty.results() == [wasmparser::ValType::I32]
        })
        .expect("fixture must emit its native add and compute signature");
    assert!(
        function_types
            .iter()
            .filter(|&&index| index as usize == integer_binary)
            .count()
            >= 2,
        "native add and compute must reuse the same Wasm type"
    );
}

#[wasm_bindgen_test]
fn wasm_codegen_trivial_scalar_body_emits_only_its_result() {
    let mut session = CompilerSession::new();
    session.set_mir_optimization(MirOptimization::Enabled);
    session.set_physical_mir_optimization(MirOptimization::Enabled);
    let entry = compile(&mut session, "fn compute() -> int { 1 + 1 }");
    let code = CompiledProgram::compile(&session, entry).unwrap();
    assert_eq!(
        code.instantiate::<(), isize>()
            .unwrap()
            .run((), WasmLimits::default())
            .unwrap(),
        2
    );
    let mut globals = None;
    let mut first_body = None;
    for payload in Parser::new(0).parse_all(code.bytes()) {
        match payload.unwrap() {
            Payload::GlobalSection(section) => globals = Some(section.count()),
            Payload::CodeSectionEntry(body) if first_body.is_none() => first_body = Some(body),
            _ => (),
        }
    }
    assert_eq!(globals, None);
    let body = first_body.unwrap();
    assert_eq!(body.get_locals_reader().unwrap().get_count(), 0);
    let operations = body
        .get_operators_reader()
        .unwrap()
        .into_iter()
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    assert!(matches!(
        operations.as_slice(),
        [Operator::I32Const { value: 2 }, Operator::End]
    ));
}

#[wasm_bindgen_test]
fn wasm_codegen_trivial_boxed_entry_keeps_runtime_context() {
    let mut session = CompilerSession::new();
    session.set_mir_optimization(MirOptimization::Enabled);
    session.set_physical_mir_optimization(MirOptimization::Enabled);
    let entry = compile(&mut session, "fn compute() -> int { 1 + 1 }");
    let value = run_boxed_entry(&session, entry, WasmLimits::default()).unwrap();
    assert_eq!(value.as_primitive_ty::<isize>(), Some(&2));
}

#[wasm_bindgen_test]
fn wasm_codegen_witnessed_alloca_reserves_helper_locals() {
    let operation = Operation::alloca_dynamic(
        Location::new_synthesized(),
        Type::unit(),
        MirValue::Parameter(ParameterId::from_index(0)),
    );
    assert!(emit::operation_needs_helper_locals(&operation));
}

#[wasm_bindgen_test]
fn wasm_codegen_identifies_stack_frontier_changes() {
    let span = Location::new_synthesized();
    let dynamic = Operation::alloca_dynamic(
        span,
        Type::unit(),
        MirValue::Parameter(ParameterId::from_index(0)),
    );
    assert!(emit::operation_changes_stack_frontier(&dynamic));
    assert!(!emit::operation_changes_stack_frontier(&Operation::alloca(
        span,
        Type::unit()
    )));
    assert!(emit::operation_changes_stack_frontier(
        &Operation::end_project(span, MirValue::Parameter(ParameterId::from_index(0)))
    ));
    assert!(emit::operation_changes_stack_frontier(&Operation::project(
        span,
        MirValue::Parameter(ParameterId::from_index(0)),
        [],
        Type::unit(),
        CallImplType::value(FnType::new_by_val([], Type::unit(), no_effects())),
    )));
    assert!(emit::terminator_changes_stack_frontier(
        &TerminatorKind::Yield {
            place: MirValue::Parameter(ParameterId::from_index(0)),
            resume: BlockId::from_index(0),
        }
    ));
}

#[wasm_bindgen_test]
fn wasm_codegen_dynamic_callee_reclaims_its_stack_frontier() {
    let mut session = CompilerSession::new();
    session.set_mir_optimization(MirOptimization::Disabled);
    session.set_physical_mir_optimization(MirOptimization::Disabled);
    let entry = compile(
        &mut session,
        r#"
            #[inline(never)]
            fn replace<T>(slot: &mut T, value: T) where T: Value { slot = value; }
            fn compute(limit: int) -> int {
                let mut value = (0, false);
                let mut i = 0;
                loop {
                    if i >= limit { break; };
                    replace(value, (i, true));
                    i += 1;
                };
                value.0
            }
        "#,
    );
    let program = session.prepare_physical_program(entry.module).unwrap();
    assert!(physical_operations(&program, |operation| {
        matches!(operation.kind, OperationKind::Alloca { .. }) && !operation.operands.is_empty()
    }));
    let caller = program.function(entry).unwrap();
    let elided = no_op_stack_markers(
        caller,
        emit::operation_changes_stack_frontier,
        emit::terminator_changes_stack_frontier,
    );
    let saves = caller
        .blocks()
        .flat_map(|block| caller.block(block).operations())
        .filter_map(|operation| {
            matches!(operation.kind, OperationKind::StackSave)
                .then(|| operation.result_id())
                .flatten()
        })
        .collect::<Vec<_>>();
    assert!(!saves.is_empty());
    assert!(saves.iter().all(|marker| elided.contains(marker)));

    let mut instance = compile_raw(&session, entry)
        .instantiate::<(isize,), isize>()
        .unwrap();
    assert_eq!(
        instance
            .run(
                (256,),
                WasmLimits {
                    stack_bytes: 512,
                    ..WasmLimits::default()
                },
            )
            .unwrap(),
        255
    );
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
    let entry = compile(&mut session, "fn compute(x: bool) -> bool { not x }");
    assert!(
        !CompiledProgram::compile(&session, entry)
            .unwrap()
            .instantiate::<(bool,), bool>()
            .unwrap()
            .run((true,), WasmLimits::default())
            .unwrap()
    );
    let entry = compile(&mut session, "fn compute(x: float) -> float { x * 2.0 }");
    assert_eq!(
        CompiledProgram::compile(&session, entry)
            .unwrap()
            .instantiate::<(Float,), Float>()
            .unwrap()
            .run((Float::new(3.5).unwrap(),), WasmLimits::default())
            .unwrap(),
        Float::new(7.0).unwrap()
    );
    let entry = compile(&mut session, "fn compute(x: ()) -> int { 42 }");
    assert_eq!(
        CompiledProgram::compile(&session, entry)
            .unwrap()
            .instantiate::<((),), isize>()
            .unwrap()
            .run(((),), WasmLimits::default())
            .unwrap(),
        42
    );
    let entry = compile(&mut session, "fn compute(x: int) { () }");
    CompiledProgram::compile(&session, entry)
        .unwrap()
        .instantiate::<(isize,), ()>()
        .unwrap()
        .run((1,), WasmLimits::default())
        .unwrap();
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
fn wasm_codegen_known_integer_calls_select_instructions() {
    let mut session = CompilerSession::new();
    session.set_mir_optimization(MirOptimization::Disabled);
    session.set_physical_mir_optimization(MirOptimization::Disabled);
    let entry = compile(
        &mut session,
        "fn compute(x: int, y: int) -> int { x + y - x * -y }",
    );
    let code = CompiledProgram::compile(&session, entry).unwrap();
    let mut add = 0;
    let mut sub = 0;
    let mut mul = 0;
    let mut calls = 0;
    for payload in Parser::new(0).parse_all(code.bytes()) {
        if let Payload::CodeSectionEntry(body) = payload.unwrap() {
            for operation in body.get_operators_reader().unwrap() {
                match operation.unwrap() {
                    Operator::I32Add => add += 1,
                    Operator::I32Sub => sub += 1,
                    Operator::I32Mul => mul += 1,
                    Operator::Call { .. } | Operator::CallIndirect { .. } => calls += 1,
                    _ => (),
                }
            }
        }
    }
    // Runtime bookkeeping may add more integer operations; require the source operations without
    // coupling this test to the current prologue.
    assert!(add >= 1 && sub >= 2 && mul >= 1);
    assert_eq!(calls, 0);
    let mut instance = code.instantiate::<(isize, isize), isize>().unwrap();
    assert_eq!(instance.run((7, 3), WasmLimits::default()).unwrap(), 31);
    assert_eq!(
        instance
            .run((isize::MAX, 1), WasmLimits::default())
            .unwrap(),
        -1,
        "integer instructions retain Ferlium's wrapping semantics"
    );

    let entry = compile(&mut session, "fn compute(x: bool) -> bool { not x }");
    let code = CompiledProgram::compile(&session, entry).unwrap();
    let calls = wasm_operator_count(code.bytes(), |op| {
        matches!(op, Operator::Call { .. } | Operator::CallIndirect { .. })
    });
    assert_eq!(calls, 0);
    assert!(
        !code
            .instantiate::<(bool,), bool>()
            .unwrap()
            .run((true,), WasmLimits::default())
            .unwrap()
    );
    let entry = compile(&mut session, "fn compute(x: int) -> int { from_int(x) }");
    let code = CompiledProgram::compile(&session, entry).unwrap();
    let calls = wasm_operator_count(code.bytes(), |op| {
        matches!(op, Operator::Call { .. } | Operator::CallIndirect { .. })
    });
    assert_eq!(calls, 0);
    assert_eq!(
        code.instantiate::<(isize,), isize>()
            .unwrap()
            .run((37,), WasmLimits::default())
            .unwrap(),
        37
    );
}

#[wasm_bindgen_test]
fn wasm_codegen_known_float_calls_select_saturating_instructions() {
    for (expression, instruction) in [("x + x", "add"), ("x - -x", "sub"), ("x * x", "mul")] {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        session.set_physical_mir_optimization(MirOptimization::Disabled);
        let entry = compile(
            &mut session,
            &format!("fn compute(x: float) -> float {{ {expression} }}"),
        );
        let code = CompiledProgram::compile(&session, entry).unwrap();
        let mut arithmetic = 0;
        let mut minimums = 0;
        let mut maximums = 0;
        let mut calls = 0;
        for payload in Parser::new(0).parse_all(code.bytes()) {
            if let Payload::CodeSectionEntry(body) = payload.unwrap() {
                for operation in body.get_operators_reader().unwrap() {
                    let operation = operation.unwrap();
                    arithmetic += usize::from(match instruction {
                        "add" => matches!(operation, Operator::F64Add),
                        "sub" => matches!(operation, Operator::F64Sub),
                        "mul" => matches!(operation, Operator::F64Mul),
                        _ => unreachable!(),
                    });
                    minimums += usize::from(matches!(operation, Operator::F64Min));
                    maximums += usize::from(matches!(operation, Operator::F64Max));
                    calls += usize::from(matches!(
                        operation,
                        Operator::Call { .. } | Operator::CallIndirect { .. }
                    ));
                }
            }
        }
        assert_eq!((arithmetic, minimums, maximums, calls), (1, 1, 1, 0));
        let mut instance = code.instantiate::<(Float,), Float>().unwrap();
        assert_eq!(
            instance
                .run((Float::new(1e308).unwrap(),), WasmLimits::default())
                .unwrap(),
            Float::new(f64::MAX).unwrap()
        );
        if instruction != "mul" {
            assert_eq!(
                instance
                    .run((Float::new(-1e308).unwrap(),), WasmLimits::default())
                    .unwrap(),
                Float::new(-f64::MAX).unwrap()
            );
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_comparison_codes_select_predicates() {
    for (expression, left, right, expected, equality) in [
        ("x < y", 2, 3, true, false),
        ("x < y", 3, 3, false, false),
        ("x <= y", 3, 3, true, false),
        ("x <= y", 4, 3, false, false),
        ("x > y", 3, 2, true, false),
        ("x > y", 3, 3, false, false),
        ("x >= y", 2, 3, false, false),
        ("x >= y", 3, 3, true, false),
        (
            "match cmp(x, y) { Equal => true, _ => false }",
            3,
            3,
            true,
            true,
        ),
    ] {
        let mut session = CompilerSession::new();
        let entry = compile(
            &mut session,
            &format!("fn compute(x: int, y: int) -> bool {{ {expression} }}"),
        );
        let code = CompiledProgram::compile(&session, entry).unwrap();
        let ordered = wasm_operator_count(code.bytes(), |op| {
            matches!(op, Operator::I32LtS | Operator::I32GtS)
        });
        assert_eq!(ordered, usize::from(!equality), "{expression}");
        assert_eq!(
            wasm_operator_count(code.bytes(), |op| matches!(
                op,
                Operator::Call { .. } | Operator::CallIndirect { .. }
            )),
            0,
            "{expression} should not call comparison glue"
        );
        assert_eq!(
            code.instantiate::<(isize, isize), bool>()
                .unwrap()
                .run((left, right), WasmLimits::default())
                .unwrap(),
            expected
        );
    }

    for (expression, left, right, expected, equality) in [
        ("x < y", 2.0, 3.0, true, false),
        ("x < y", 3.0, 3.0, false, false),
        ("x <= y", 3.0, 3.0, true, false),
        ("x <= y", 4.0, 3.0, false, false),
        ("x > y", 3.0, 2.0, true, false),
        ("x > y", 3.0, 3.0, false, false),
        ("x >= y", 2.0, 3.0, false, false),
        ("x >= y", 3.0, 3.0, true, false),
        (
            "match cmp(x, y) { Equal => true, _ => false }",
            -0.0,
            0.0,
            true,
            true,
        ),
    ] {
        let mut session = CompilerSession::new();
        let entry = compile(
            &mut session,
            &format!("fn compute(x: float, y: float) -> bool {{ {expression} }}"),
        );
        let code = CompiledProgram::compile(&session, entry).unwrap();
        let ordered = wasm_operator_count(code.bytes(), |op| {
            matches!(op, Operator::F64Lt | Operator::F64Gt)
        });
        assert_eq!(ordered, usize::from(!equality), "{expression}");
        assert_eq!(
            wasm_operator_count(code.bytes(), |op| matches!(
                op,
                Operator::Call { .. } | Operator::CallIndirect { .. }
            )),
            0,
            "{expression} should not call comparison glue"
        );
        assert_eq!(
            code.instantiate::<(Float, Float), bool>()
                .unwrap()
                .run(
                    (Float::new(left).unwrap(), Float::new(right).unwrap()),
                    WasmLimits::default(),
                )
                .unwrap(),
            expected
        );
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_materializes_escaping_comparison_codes() {
    for ty in ["int", "float"] {
        let mut session = CompilerSession::new();
        let entry = compile(
            &mut session,
            &format!(
                "fn compute(x: {ty}, y: {ty}) -> int {{ \
                    match cmp(x, y) {{ Less => -1, Equal => 0, Greater => 1 }} \
                }}"
            ),
        );
        let code = CompiledProgram::compile(&session, entry).unwrap();
        assert_eq!(
            wasm_operator_count(code.bytes(), |op| matches!(
                op,
                Operator::Call { .. } | Operator::CallIndirect { .. }
            )),
            0,
            "escaping {ty} comparison code should not call native glue"
        );
        if ty == "int" {
            let mut instance = code.instantiate::<(isize, isize), isize>().unwrap();
            for (inputs, expected) in [((2, 3), -1), ((3, 3), 0), ((3, 2), 1)] {
                assert_eq!(
                    instance.run(inputs, WasmLimits::default()).unwrap(),
                    expected
                );
            }
        } else {
            let mut instance = code.instantiate::<(Float, Float), isize>().unwrap();
            for (inputs, expected) in [
                ((Float::new(2.0).unwrap(), Float::new(3.0).unwrap()), -1),
                ((Float::new(-0.0).unwrap(), Float::new(0.0).unwrap()), 0),
                ((Float::new(3.0).unwrap(), Float::new(2.0).unwrap()), 1),
            ] {
                assert_eq!(
                    instance.run(inputs, WasmLimits::default()).unwrap(),
                    expected
                );
            }
        }
    }
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
        for (source, positive) in [
            (
                "fn compute(x: int) -> int { match probe::integer(x) { None => 7, Some(n) => n } }",
                5,
            ),
            (
                "fn compute(x: int) -> int { match probe::real(x) { None => 7, Some(f) => if f == 2.5 { x } else { 0 } } }",
                4,
            ),
            (
                "fn compute(x: int) -> int { let v = probe::text(x); let copy = v; match copy { None => 7, Some(s) => if s == to_string(x) { x } else { 0 } } }",
                4,
            ),
            (
                "fn compute(x: int) -> int { match probe::unit(x) { None => 7, Some(u) => x } }",
                4,
            ),
            (
                "fn compute(x: int) -> int { let mut v = probe::text(x); let mut n = x; loop { if n <= 0 { break; }; n -= 1; v = probe::text(n); }; match v { None => 7, Some(s) => 0 } }",
                7,
            ),
        ] {
            assert_wasm_runs::<isize, isize>(&mut session, source, 0, 7);
            assert_wasm_runs::<isize, isize>(&mut session, source, 4, positive);
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
            let actual = instance.run(
                (input,),
                WasmLimits {
                    execution: limits.execution,
                    ..WasmLimits::default()
                },
            );
            match input {
                4 => assert_eq!(actual.unwrap(), 5),
                3 => assert_eq!(
                    actual.unwrap_err().kind(),
                    RuntimeErrorKind::SourceFailure(SourceFailureKind::DivisionByZero)
                ),
                2 => {
                    assert!(matches!(
                        actual.as_ref().unwrap_err().kind(),
                        RuntimeErrorKind::SandboxViolation(SandboxViolationKind::FuelExhausted)
                    ));
                    assert!(
                        actual
                            .unwrap_err()
                            .sandbox_violation()
                            .unwrap()
                            .interrupted_source_failure()
                            .is_some()
                    );
                }
                _ => unreachable!(),
            }
            assert_eq!(DROP_LOG.get(), log);
        }
        // Fixed Value adapters must not charge extra source call-depth frames for destruction.
        assert_eq!(
            instance
                .run(
                    (4,),
                    WasmLimits {
                        execution: limits.with_call_depth_limit(3).execution,
                        ..WasmLimits::default()
                    },
                )
                .unwrap(),
            5
        );
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_structured_control_flow_and_local_storage() {
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(optimization);
        for (source, has_loop, has_branch) in [
            ("fn compute(x: int) -> int { x * 3 + 1 }", false, false),
            (
                "fn compute(x: int) -> int { let mut n = 0; loop { if n >= x { break; }; n += 1; }; n }",
                true,
                false,
            ),
            (
                "fn compute(x: bool, y: bool) -> int { if x { if y { 1 } else { 2 } } else { 3 } }",
                false,
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
            let mut direct_edges = 0;
            let mut branches = 0;
            let mut loops = 0;
            for op in body.get_operators_reader().unwrap() {
                match op.unwrap() {
                    Operator::BrTable { .. } => dispatches += 1,
                    Operator::Br { .. } | Operator::BrIf { .. } => direct_edges += 1,
                    Operator::If { .. } => branches += 1,
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
            assert_eq!(
                dispatches, 0,
                "structured source must not use the dispatcher: {optimization:?}: {source}"
            );
            assert_eq!(loops, usize::from(has_loop));
            if has_loop {
                assert!(direct_edges > 0, "loop edges must branch directly");
            }
            if has_branch {
                assert!(branches >= 2, "nested source branches must use Wasm ifs");
            }
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_omits_noop_stack_markers_in_loops() {
    let mut session = CompilerSession::new();
    let entry = compile(
        &mut session,
        "fn compute(limit: int) -> int { \
             let mut i = 0; let mut sum = 0; \
             loop { if i >= limit { break; }; sum += i; i += 1; }; \
             sum \
         }",
    );
    let program = session.prepare_physical_program(entry.module).unwrap();
    let body = program.function(entry).unwrap();
    assert!(
        body.blocks()
            .flat_map(|block| body.block(block).operations())
            .any(|operation| matches!(operation.kind, OperationKind::StackSave))
    );
    assert!(
        body.blocks()
            .flat_map(|block| body.block(block).operations())
            .any(|operation| matches!(operation.kind, OperationKind::StackRestore))
    );
    assert!(
        !no_op_stack_markers(
            body,
            emit::operation_changes_stack_frontier,
            emit::terminator_changes_stack_frontier,
        )
        .is_empty(),
        "the loop bracket must be redundant under the Wasm frontier model"
    );

    let code = CompiledProgram::compile(&session, entry).unwrap();
    for operation in exported_function_operators(code.bytes(), ENTRY_EXPORT) {
        match operation {
            Operator::GlobalGet { global_index } | Operator::GlobalSet { global_index } => {
                assert_ne!(
                    global_index,
                    emit::STACK_GLOBAL_INDEX,
                    "the no-op loop bracket must not access the Wasm stack frontier"
                );
            }
            _ => {}
        }
    }

    let mut instance = code.instantiate::<(isize,), isize>().unwrap();
    assert_eq!(instance.run((10,), WasmLimits::default()).unwrap(), 45);
}

#[wasm_bindgen_test]
fn wasm_codegen_stackifies_single_use_scalar_expressions() {
    let mut session = CompilerSession::new();
    let entry = compile(
        &mut session,
        "fn compute(x: int, y: int) -> bool {
             let sum = x + 1; let scaled = sum * 2; scaled == y
         }",
    );
    let code = CompiledProgram::compile(&session, entry).unwrap();
    assert_stackified_add_mul(&exported_function_operators(code.bytes(), ENTRY_EXPORT));

    let mut instance = code.instantiate::<(isize, isize), bool>().unwrap();
    assert!(instance.run((3, 8), WasmLimits::default()).unwrap());
    assert!(!instance.run((3, 9), WasmLimits::default()).unwrap());
}

#[wasm_bindgen_test]
fn wasm_codegen_stackifies_across_elided_stack_markers() {
    let mut session = CompilerSession::new();
    let entry = compile(
        &mut session,
        "fn add_one(x: int) -> int { x + 1 }
         fn compute(x: int, y: int) -> bool {
             let sum = add_one(x); let scaled = sum * 2; scaled == y
         }",
    );
    let program = session.prepare_physical_program(entry.module).unwrap();
    let physical = program.function(entry).unwrap();
    assert!(
        physical
            .blocks()
            .flat_map(|block| physical.block(block).operations())
            .any(|operation| matches!(operation.kind, OperationKind::StackSave))
    );
    assert!(
        !no_op_stack_markers(
            physical,
            emit::operation_changes_stack_frontier,
            emit::terminator_changes_stack_frontier,
        )
        .is_empty()
    );
    let code = CompiledProgram::compile(&session, entry).unwrap();
    assert_stackified_add_mul(&exported_function_operators(code.bytes(), ENTRY_EXPORT));

    let mut instance = code.instantiate::<(isize, isize), bool>().unwrap();
    assert!(instance.run((3, 8), WasmLimits::default()).unwrap());
    assert!(!instance.run((3, 9), WasmLimits::default()).unwrap());
}

fn assert_stackified_add_mul(operations: &[Operator<'_>]) {
    let add = operations
        .iter()
        .position(|operation| matches!(operation, Operator::I32Add))
        .expect("fixture must retain its addition");
    let mul = operations
        .iter()
        .position(|operation| matches!(operation, Operator::I32Mul))
        .expect("fixture must retain its multiplication");
    assert!(
        add < mul
            && !operations[add + 1..mul].iter().any(|operation| matches!(
                operation,
                Operator::LocalGet { .. } | Operator::LocalSet { .. }
            )),
        "the single-use sum must flow directly into the multiplication: {operations:?}"
    );
}

#[wasm_bindgen_test]
fn wasm_codegen_bounds_deep_scalar_expression_emission() {
    let expression = |depth| {
        (0..depth).fold("x".to_owned(), |expression, _| {
            format!("({expression} + 1)")
        })
    };
    let mut session = CompilerSession::new();
    let entry = compile(
        &mut session,
        &format!(
            "#[inline(never)] fn at_limit(x: int) -> int {{ {} }}
             #[inline(never)] fn over_limit(x: int) -> int {{ {} }}
             fn compute(x: int) -> int {{ at_limit(x) + over_limit(x) }}",
            // Each source addition becomes an alternating place writer and scalar load in
            // physical MIR, so 64 additions exercise approximately 128 producer hops.
            expression(64),
            expression(66),
        ),
    );
    let code = CompiledProgram::compile(&session, entry).unwrap();
    let maximum_stackified_adds = Parser::new(0)
        .parse_all(code.bytes())
        .filter_map(|payload| match payload.unwrap() {
            Payload::CodeSectionEntry(body) => Some(
                body.get_operators_reader()
                    .unwrap()
                    .into_iter()
                    .map(Result::unwrap)
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .flat_map(|operations| {
            operations
                .split(|operation| {
                    matches!(
                        operation,
                        Operator::LocalGet { .. } | Operator::LocalSet { .. }
                    )
                })
                .map(|segment| {
                    segment
                        .iter()
                        .filter(|operation| matches!(operation, Operator::I32Add))
                        .count()
                })
                .collect::<Vec<_>>()
        })
        .max()
        .unwrap();
    assert!(
        maximum_stackified_adds >= 64,
        "the expression at the depth limit must actually be emitted as one operand-stack chain"
    );

    let mut instance = code.instantiate::<(isize,), isize>().unwrap();
    assert_eq!(instance.run((12,), WasmLimits::default()).unwrap(), 154);
}

#[wasm_bindgen_test]
fn wasm_codegen_structured_branches_execute_both_arms() {
    let source =
        "fn compute(x: int) -> int { if x < 0 { -x } else { if x == 0 { 7 } else { x + 1 } } }";
    let mut session = CompilerSession::new();
    let entry = compile(&mut session, source);
    let code = CompiledProgram::compile(&session, entry).unwrap();
    let dispatches = Parser::new(0)
        .parse_all(code.bytes())
        .find_map(|payload| match payload.unwrap() {
            Payload::CodeSectionEntry(body) => Some(
                body.get_operators_reader()
                    .unwrap()
                    .into_iter()
                    .map(Result::unwrap)
                    .filter(|operation| matches!(operation, Operator::BrTable { .. }))
                    .count(),
            ),
            _ => None,
        })
        .unwrap();
    assert_eq!(dispatches, 0, "the executed entry must use structured Wasm");
    let mut instance = code.instantiate::<(isize,), isize>().unwrap();
    for (input, expected) in [(-5, 5), (0, 7), (9, 10)] {
        assert_eq!(
            instance.run((input,), WasmLimits::default()).unwrap(),
            expected
        );
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_structures_reducible_control_flow() {
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(optimization);
        for (source, cases) in [
            (
                "fn compute(n: int) -> int { let mut s = 0; for i in 0..n { s = s + i * 2 }; s }",
                [(0, 0), (1, 0), (10, 90)],
            ),
            (
                "fn compute(x: int) -> int { let o = if x > 0 { Some(x) } else { None }; \
                 match o { Some(v) => v * 2, None => 7 } }",
                [(-3, 7), (0, 7), (4, 8)],
            ),
            // Nested loops with `continue`, and an `if` inside the inner loop.
            (
                "fn compute(n: int) -> int { let mut s = 0; for i in 0..n { \
                 for j in 0..i { if j == 2 { continue; }; s = s + j } }; s }",
                [(0, 0), (3, 1), (6, 14)],
            ),
            // An early return from a loop, and fallible indexing whose failure leaves the loop.
            (
                "fn compute(n: int) -> int { let a = [1, 2, 3, 4, 5]; let mut s = 0; \
                 for i in 0..n { if s > 5 { return s * 10 }; s = s + a[i] }; s }",
                [(0, 0), (2, 3), (5, 60)],
            ),
            // A switch with three targets.
            (
                "fn compute(x: int) -> int { let v = if x < 0 { A } else if x == 0 { B } else { C }; \
                 match v { A => 1, B => 2, C => 3 } }",
                [(-1, 1), (0, 2), (1, 3)],
            ),
        ] {
            let entry = compile(&mut session, source);
            let code = CompiledProgram::compile(&session, entry).unwrap();
            let dispatches = Parser::new(0)
                .parse_all(code.bytes())
                .find_map(|payload| match payload.unwrap() {
                    Payload::CodeSectionEntry(body) => Some(
                        body.get_operators_reader()
                            .unwrap()
                            .into_iter()
                            .map(Result::unwrap)
                            .filter(|operation| matches!(operation, Operator::BrTable { .. }))
                            .count(),
                    ),
                    _ => None,
                })
                .unwrap();
            assert_eq!(
                dispatches, 0,
                "reducible control flow must be structured: {optimization:?}: {source}"
            );
            let mut instance = code.instantiate::<(isize,), isize>().unwrap();
            for (input, expected) in cases {
                assert_eq!(
                    instance.run((input,), WasmLimits::default()).unwrap(),
                    expected,
                    "{optimization:?}: {source}"
                );
            }
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
