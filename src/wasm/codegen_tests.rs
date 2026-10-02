// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{cell::Cell, fmt::Debug, hint::black_box, mem::offset_of, ptr};

use js_sys::{Function as JsFunction, Reflect, Uint8Array, WebAssembly};
use wasm_bindgen::{JsCast, JsValue};
use wasm_bindgen_test::wasm_bindgen_test;
use wasmparser::{FunctionBody, Operator, Parser, Payload};

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
    module::{FunctionId, LocalFunctionId, Module, Path, Visibility, id::Id},
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

#[wasm_bindgen_test]
fn wasm_codegen_tag_scalars_cross_direct_calls_without_memory() {
    let mut session = CompilerSession::new();
    let entry = compile(
        &mut session,
        "enum Signal { Stop, Wait, Go }
         #[inline(never)] fn choose(x: int) -> Signal {
             if x < 0 { Signal::Stop } else if x == 0 { Signal::Wait } else { Signal::Go }
         }
         #[inline(never)] fn consume(x: Signal) -> int {
             match x { Stop => -1, Wait => 0, Go => 1 }
         }
         pub fn compute(x: int) -> int { consume(choose(x)) }",
    );
    let code = CompiledProgram::compile(&session, entry).unwrap();
    let operators = exported_function_operators(code.bytes(), ENTRY_EXPORT);
    assert!(
        !operators.iter().any(|op| matches!(
            op,
            Operator::I32Load { .. } | Operator::I32Store { .. } | Operator::MemoryCopy { .. }
        )),
        "tag transport needs no memory: {operators:?}"
    );
    let mut instance = code.instantiate::<(isize,), isize>().unwrap();
    for (x, expected) in [(-9, -1), (0, 0), (8, 1)] {
        assert_eq!(instance.run((x,), WasmLimits::default()).unwrap(), expected);
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_tag_scalars_keep_mutable_generic_and_callable_contracts() {
    for source in [
        "#[inline(never)] fn replace(x: &mut Ordering, y: Ordering) { x = y; }
         fn compute(x: int) -> int { let mut v = Less; replace(v, if x == 0 { Equal } else { Greater }); match v { Equal => 0, _ => 1 } }",
        "#[inline(never)] fn identity<T>(x: T) -> T { x }
         fn compute(x: int) -> int { let v: Ordering = identity(if x == 0 { Equal } else { Greater }); match v { Equal => 0, _ => 1 } }",
        "#[inline(never)] fn apply(f: (Ordering) -> Ordering, x: Ordering) -> Ordering { f(x) }
         fn compute(x: int) -> int { let v = apply(|v| v, if x == 0 { Equal } else { Greater }); match v { Equal => 0, _ => 1 } }",
        "#[inline(never)] fn choose(x: int) -> Ordering { let v = idiv(1, x); if v == 1 { Equal } else { Greater } }
         fn compute(x: int) -> int { match choose(x) { Equal => 0, _ => 1 } }",
    ] {
        let mut session = CompilerSession::new();
        let entry = compile(&mut session, source);
        let code = compile_raw(&session, entry);
        let mut instance = code.instantiate::<(isize,), isize>().unwrap();
        if source.contains("idiv") {
            assert!(instance.run((0,), WasmLimits::default()).is_err());
            assert_eq!(instance.run((1,), WasmLimits::default()).unwrap(), 0);
            assert_eq!(instance.run((2,), WasmLimits::default()).unwrap(), 1);
        } else {
            assert_eq!(instance.run((0,), WasmLimits::default()).unwrap(), 0);
            assert_eq!(instance.run((2,), WasmLimits::default()).unwrap(), 1);
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_native_variant_results_resolve_session_tags() {
    use crate::hir::native_functions::NativeVariantFnNN;

    let mut session = CompilerSession::new();
    // Deliberately give semantic tags different identities from Rust discriminants.
    for tag in ["Unrelated", "Greater", "Less", "Equal"] {
        session.variant_tag_id(ustr(tag));
    }
    let path = Path::single_str("host_variant");
    let mut host = Module::new(session.modules().next_id(), path.clone());
    NativeVariantFnNN::from_rust(|left: isize, right: isize| right.cmp(&left))
        .description(["left", "right"], "Reversed comparison", no_effects())
        .add_to(&mut host, ustr("compare"), Visibility::Public);
    session.register_module(path, host);
    for expression in [
        "host_variant::compare(x, y)",
        "{ let f = host_variant::compare; f(x, y) }",
    ] {
        let entry = compile(
            &mut session,
            &format!(
                "pub fn compute(x: int, y: int) -> int {{ match {expression} {{ Less => -1, Equal => 0, Greater => 1 }} }}",
            ),
        );
        let code = compile_raw(&session, entry);
        let mut instance = code.instantiate::<(isize, isize), isize>().unwrap();
        for (left, right, expected) in [(2, 9, 1), (9, 2, -1), (7, 7, 0)] {
            assert_eq!(
                instance.run((left, right), WasmLimits::default()).unwrap(),
                expected
            );
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_native_variant_results_fold_into_discriminant_tests() {
    use crate::hir::native_functions::NativeVariantFnNN;

    let mut session = CompilerSession::new();
    let path = Path::single_str("host_variant");
    let mut host = Module::new(session.modules().next_id(), path.clone());
    NativeVariantFnNN::from_rust(|left: isize, right: isize| left.cmp(&right))
        .description(["left", "right"], "Comparison", no_effects())
        .add_to(&mut host, ustr("compare"), Visibility::Public);
    session.register_module(path, host);
    let entry = compile(
        &mut session,
        "pub fn compute(x: int, y: int) -> int { match host_variant::compare(x, y) { Less => 10, _ => 20 } }",
    );
    let code = CompiledProgram::compile(&session, entry).unwrap();
    let operators = exported_function_operators(code.bytes(), ENTRY_EXPORT);
    // The call returns Rust's discriminant, which the caller tests directly: no tag is built.
    assert!(
        operators
            .windows(2)
            .any(|pair| matches!(pair, [Operator::I32Const { value: -1 }, Operator::I32Eq])),
        "{operators:?}"
    );
    assert!(
        !operators.iter().any(|op| matches!(op, Operator::Select)),
        "{operators:?}"
    );
    let mut instance = code.instantiate::<(isize, isize), isize>().unwrap();
    for (left, right, expected) in [(2, 9, 10), (9, 2, 20), (7, 7, 20)] {
        assert_eq!(
            instance.run((left, right), WasmLimits::default()).unwrap(),
            expected
        );
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_single_case_native_variants_return_their_tag() {
    use crate::hir::native_functions::NativeVariantFnN;

    enum Ready {
        Ready,
    }
    crate::native_variant_result!(Ready { Ready });
    let mut session = CompilerSession::new();
    let path = Path::single_str("host_ready");
    let mut host = Module::new(session.modules().next_id(), path.clone());
    // The decoder has no alternatives, so its whole body is a stored unit variant.
    NativeVariantFnN::from_rust(|_: isize| Ready::Ready)
        .description(["input"], "Single case", no_effects())
        .add_to(&mut host, ustr("ready"), Visibility::Public);
    session.register_module(path, host);
    for expression in [
        "host_ready::ready(x)",
        "{ let f = host_ready::ready; f(x) }",
    ] {
        let entry = compile(
            &mut session,
            &format!("pub fn compute(x: int) -> int {{ match {expression} {{ Ready => x + 1 }} }}"),
        );
        for code in [
            CompiledProgram::compile(&session, entry).unwrap(),
            compile_raw(&session, entry),
        ] {
            let mut instance = code.instantiate::<(isize,), isize>().unwrap();
            assert_eq!(instance.run((4,), WasmLimits::default()).unwrap(), 5);
        }
    }
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

/// Body and parameter count of a named exported function, independent of code-section ordering.
///
/// This follows the export exactly, so a fallible scalar entry resolves to its generated wrapper
/// rather than the wrapped Ferlium function.
fn exported_function_body<'a>(bytes: &'a [u8], name: &str) -> (FunctionBody<'a>, u32) {
    let mut types = Vec::new();
    let mut function_types = Vec::new();
    let mut imported_functions = 0usize;
    let mut function_index = None;
    for payload in Parser::new(0).parse_all(bytes) {
        match payload.unwrap() {
            Payload::TypeSection(section) => {
                types.extend(section.into_iter_err_on_gc_types().map(Result::unwrap))
            }
            Payload::ImportSection(section) => {
                function_types.extend(section.into_imports().filter_map(|import| {
                    match import.unwrap().ty {
                        wasmparser::TypeRef::Func(index)
                        | wasmparser::TypeRef::FuncExact(index) => Some(index),
                        _ => None,
                    }
                }));
                imported_functions = function_types.len();
            }
            Payload::FunctionSection(section) => {
                function_types.extend(section.into_iter().map(Result::unwrap));
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
    let function_index = function_index.expect("fixture must export its entry");
    let parameter_count = types[function_types[function_index] as usize]
        .params()
        .len() as u32;
    let body_index = function_index
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
    (body, parameter_count)
}

fn exported_function_operators<'a>(bytes: &'a [u8], name: &str) -> Vec<Operator<'a>> {
    exported_function_body(bytes, name)
        .0
        .get_operators_reader()
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
fn wasm_codegen_subscript_caller_failure_resumes_owned_evidence() {
    // The generic accessor builds a captured environment for `(T, T)` before its yield and only
    // releases it after resumption. An out-of-bounds index on the projected array fails in the
    // caller while the projection is open. Its cleanup must still resume the accessor, and so
    // release that environment. The generic driver keeps the accessor generic in raw programs.
    let source = r#"
        subscript cell<T>(slot: &mut [int], value: T) -> [int] where T: Value {
            mut {
                let values = [(value, value)];
                let mut local = slot;
                yield local;
                local[0] = local[0] + len(values);
                slot = local
            }
        }
        #[inline(never)]
        fn drive<T>(slot: &mut [int], value: T, index: int) where T: Value {
            slot->[cell](value)[index] += 1
        }
        fn compute(x: int) -> int {
            let mut slot = [x];
            drive(slot, to_string(x), x);
            slot[0]
        }
    "#;
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        let mut session = CompilerSession::new();
        session.set_allow_experimental(true);
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(optimization);
        let entry = compile(&mut session, source);
        let mut instance = compile_raw(&session, entry)
            .instantiate::<(isize,), isize>()
            .unwrap();
        for input in [1_isize, 0, 1] {
            let before = LIVE_ENVIRONMENTS.get();
            let built = BUILT_ENVIRONMENTS.get();
            let actual = instance
                .run((input,), WasmLimits::default())
                .map_err(|error| error.kind());
            if input == 0 {
                assert_eq!(actual, Ok(2));
            } else {
                assert_eq!(
                    actual,
                    Err(RuntimeErrorKind::SourceFailure(SourceFailureKind::Aborted(
                        Some("Array access out of bounds: index 1 for length 1".into())
                    )))
                );
            }
            assert!(
                BUILT_ENVIRONMENTS.get() > built,
                "the accessor must build its environment before the caller fails ({optimization:?})"
            );
            assert_eq!(
                LIVE_ENVIRONMENTS.get(),
                before,
                "input {input} ({optimization:?})"
            );
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
    let mut dynamic_allocations = 0;
    for payload in Parser::new(0).parse_all(code.bytes()) {
        if let Payload::CodeSectionEntry(body) = payload.unwrap() {
            let ops = body
                .get_operators_reader()
                .unwrap()
                .into_iter()
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            // Witnessed storage uses the checked dynamic allocator: its end is held in an
            // i64 helper, while size, alignment and base require three i32 helpers.
            if ops.iter().any(|op| matches!(op, Operator::I64GtU)) {
                assert!(
                    body.get_locals_reader()
                        .unwrap()
                        .into_iter()
                        .any(|local| local.unwrap().1 == wasmparser::ValType::I64),
                    "dynamic allocation must reserve its i64 end helper"
                );
                dynamic_allocations += 1;
            }
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
    assert!(
        dynamic_allocations > 0,
        "fixture must exercise witnessed allocation"
    );
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
fn wasm_codegen_shared_helper_source_maps_preserve_origins_and_split_boundaries() {
    let source = Location::new_synthesized().source_id();
    let first = Location::new(1, 2, source);
    let second = Location::new(3, 4, source);
    let caller = Location::new(5, 6, source);
    let entry = |bytes, span, inlined_at| emit::CodeSourceMapEntry {
        body: 7,
        bytes,
        span,
        inlined_at,
    };
    let merged = emit::merge_function_source_maps(vec![
        entry(2..6, first, vec![]),
        entry(2..4, second, vec![caller]),
        entry(4..6, second, vec![caller]),
        entry(2..6, first, vec![]),
    ]);
    assert_eq!(merged.len(), 4);
    for (entries, range) in merged.as_chunks::<2>().0.iter().zip([2..4, 4..6]) {
        assert!(
            entries
                .iter()
                .all(|entry| entry.body == 7 && entry.bytes == range)
        );
        assert_eq!(entries[0].span, first);
        assert_eq!(entries[1].span, second);
        assert_eq!(entries[1].inlined_at, [caller]);
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_generated_helpers_and_adapters_are_shared() {
    let mut session = CompilerSession::new();
    session.set_mir_optimization(MirOptimization::Enabled);
    let module = session
        .compile(
            &format!(
                "{}\npub fn quicksort_float_a(a: [float]) {{ quicksort_array(a) }}",
                include_str!("../../tests/modules/quicksort.fer")
            ),
            "sharing",
            Path::single_str("sharing"),
        )
        .unwrap()
        .module_id;
    let program = session.prepare_physical_program(module).unwrap();
    let roots = (0..program.module(module).unwrap().entry_count())
        .map(LocalFunctionId::from_index)
        .filter(|&id| program.module(module).unwrap().get(id).is_some())
        .map(|id| FunctionId::new(module, id))
        .collect::<Vec<_>>();
    let mut imports = Imports::new().unwrap();
    let mapped = emit::emit_with_source_map(&program, &roots, &[], &mut imports, &session).unwrap();
    let mut imports = Imports::new().unwrap();
    let plain = emit::emit(&program, &roots, &[], &mut imports, &session).unwrap();
    assert_eq!(
        mapped.bytes, plain.bytes,
        "debug locations must not affect sharing"
    );
    // Compiling the result checks call signatures and all remapped table/function indices.
    WebAssembly::Module::new(&Uint8Array::from(mapped.bytes.as_slice())).unwrap();
    let mut imported = 0;
    let mut signatures = Vec::new();
    let mut bodies = Vec::new();
    let mut names = Vec::new();
    let mut table_functions = Vec::new();
    for payload in Parser::new(0).parse_all(&mapped.bytes) {
        match payload.unwrap() {
            Payload::ImportSection(section) => {
                imported = section
                    .into_imports()
                    .filter(|entry| {
                        matches!(
                            entry.as_ref().unwrap().ty,
                            wasmparser::TypeRef::Func(_) | wasmparser::TypeRef::FuncExact(_)
                        )
                    })
                    .count();
            }
            Payload::FunctionSection(section) => {
                signatures.extend(section.into_iter().map(Result::unwrap))
            }
            Payload::CodeSectionEntry(body) => bodies.push(body.as_bytes()),
            Payload::CustomSection(section) if section.name() == "name" => {
                for name in wasmparser::NameSectionReader::new(section.data_reader()) {
                    if let wasmparser::Name::Function(map) = name.unwrap() {
                        names.extend(map.into_iter().map(Result::unwrap));
                    }
                }
            }
            Payload::ElementSection(section) => {
                for element in section {
                    if let wasmparser::ElementItems::Functions(functions) = element.unwrap().items {
                        table_functions.extend(functions.into_iter().map(Result::unwrap));
                    }
                }
            }
            _ => {}
        }
    }
    assert!(
        names
            .iter()
            .any(|name| name.name.starts_with("<dictionary adapter Value::")),
        "unshared adapters must retain descriptive method names"
    );
    assert!(
        names
            .iter()
            .any(|name| name.name.starts_with("<shared function ")
                && name.name.contains("SizedSeq")
                && name.name.contains("::len#impl:")
                && name.name.contains("-thunk")),
        "array length thunks should share: {names:?}"
    );
    let mut keys = FxHashSet::default();
    let mut non_adapters = 0;
    let mut adapters = 0;
    let mut buffer_drops = 0;
    for name in names {
        if name.name.contains("#physical:buffer_drop:") {
            buffer_drops += 1;
            let body = wasmparser::FunctionBody::new(wasmparser::BinaryReader::new(
                bodies[name.index as usize - imported],
                0,
            ));
            assert_eq!(
                body.get_locals_reader().unwrap().get_count(),
                0,
                "buffer-drop address and loaded pointer must need no locals: {}, {:?}",
                name.name,
                body.get_operators_reader()
                    .unwrap()
                    .into_iter()
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap()
            );
            assert!(
                !body
                    .get_operators_reader()
                    .unwrap()
                    .into_iter()
                    .any(|operation| matches!(
                        operation.unwrap(),
                        Operator::LocalSet { .. } | Operator::LocalTee { .. }
                    )),
                "buffer-drop temporaries must stay on the expression stack: {}",
                name.name
            );
        }
        if name.name.starts_with("<shared function ") {
            assert!(
                name.name.contains(" x"),
                "shared group size missing: {}",
                name.name
            );
            let index = name.index as usize - imported;
            assert!(
                keys.insert((signatures[index], bodies[index])),
                "duplicate {}",
                name.name
            );
            // Classify by the displayed representative; mixed groups count only once.
            if !name.name.contains("dictionary adapter ") {
                non_adapters += 1;
            } else {
                adapters += 1;
            }
        }
    }
    assert!(
        buffer_drops > 0,
        "fixture must include a generated buffer drop"
    );
    assert!(
        non_adapters >= 2 && adapters >= 2,
        "fixture must exercise both representative kinds: {non_adapters} non-adapter groups, {adapters} adapter groups"
    );
    assert!(
        table_functions.len() > table_functions.iter().collect::<FxHashSet<_>>().len(),
        "distinct dictionary slots should share an adapter function"
    );
    for pair in mapped.source_map.windows(2) {
        assert!(
            pair[0].body < pair[1].body
                || (pair[0].body == pair[1].body
                    && (pair[0].bytes.end <= pair[1].bytes.start
                        || pair[0].bytes == pair[1].bytes)),
            "unordered source-map entries: {pair:?}"
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
fn wasm_codegen_reserves_only_needed_helper_locals() {
    for (source, expected) in [
        (
            "#[inline(never)] fn bump(x: int) -> int { x + 1 } fn compute(x: int) -> int { bump(x) }",
            8,
        ),
        (
            "fn compute(x: int) -> int { let values = [x, x + 1]; len(values) }",
            2,
        ),
    ] {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.set_physical_mir_optimization(MirOptimization::Enabled);
        let entry = compile(&mut session, source);
        let code = CompiledProgram::compile(&session, entry).unwrap();
        assert_eq!(
            code.instantiate::<(isize,), isize>()
                .unwrap()
                .run((7,), WasmLimits::default())
                .unwrap(),
            expected
        );
        let (body, parameter_count) = exported_function_body(code.bytes(), ENTRY_EXPORT);
        let locals = body
            .get_locals_reader()
            .unwrap()
            .into_iter()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        // Neither static calls nor array construction needs the i64 allocation-end helper.
        assert!(
            locals.iter().all(|(_, ty)| *ty == wasmparser::ValType::I32),
            "{source}: {locals:?}"
        );
        let operations = exported_function_operators(code.bytes(), ENTRY_EXPORT);
        let count: u32 = locals.iter().map(|(count, _)| count).sum();
        for local_index in parameter_count..parameter_count + count {
            assert!(
                operations.iter().any(|op| matches!(op,
                Operator::LocalGet { local_index: index }
                | Operator::LocalSet { local_index: index }
                | Operator::LocalTee { local_index: index } if *index == local_index)),
                "{source}: local {local_index} was reserved but never used"
            );
        }
    }
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

/// Counts selected operators across every function body of a compiled program.
fn count_operators(code: &CompiledProgram, mut counted: impl FnMut(&Operator) -> bool) -> usize {
    let mut count = 0;
    for payload in Parser::new(0).parse_all(code.bytes()) {
        if let Payload::CodeSectionEntry(body) = payload.unwrap() {
            for operation in body.get_operators_reader().unwrap() {
                count += usize::from(counted(&operation.unwrap()));
            }
        }
    }
    count
}

#[wasm_bindgen_test]
fn wasm_codegen_speculated_float_tree_saturates_only_on_its_slow_path() {
    let mut session = CompilerSession::new();
    let entry = compile(
        &mut session,
        "fn compute(x: float, y: float) -> float { (x * y + 1.0) * x - y }",
    );
    let code = CompiledProgram::compile(&session, entry).unwrap();
    // Four saturating operations remain, all on the slow path; the fast path checks its root once
    // and converts it back without a fallback, since the conversion is only reached when finite.
    assert_eq!(
        count_operators(&code, |operation| matches!(operation, Operator::F64Min)),
        4
    );
    assert_eq!(
        count_operators(&code, |operation| matches!(operation, Operator::F64Max)),
        4
    );
    assert_eq!(
        count_operators(&code, |operation| matches!(operation, Operator::Select)),
        0
    );
    assert_eq!(
        count_operators(&code, |operation| matches!(
            operation,
            Operator::Call { .. }
        )),
        0
    );
    // The language semantics: every operation saturates.
    let saturate = |value: f64| value.clamp(-f64::MAX, f64::MAX);
    let expected = |x: f64, y: f64| saturate(saturate(saturate(saturate(x * y) + 1.0) * x) - y);
    let mut instance = code.instantiate::<(Float, Float), Float>().unwrap();
    for (x, y) in [
        (3.0, 2.0),
        // `x * y` overflows, so the slow path computes the result.
        (f64::MAX, 2.0),
        (0.0, f64::MAX),
        (f64::MAX, -f64::MAX),
        (-0.0, 1.0),
    ] {
        let result = instance
            .run(
                (Float::new(x).unwrap(), Float::new(y).unwrap()),
                WasmLimits::default(),
            )
            .unwrap()
            .into_inner();
        assert_eq!(result.to_bits(), expected(x, y).to_bits(), "({x}, {y})");
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_speculated_float_trees_match_per_operation_saturation() {
    let max = f64::MAX;
    for (source, x, y) in [
        // Overflow then cancellation: per-operation saturation gives 0, the raw tree NaN.
        ("(x + x) - y", max, max),
        // Overflow then scaling: per-operation saturation gives MAX / 2, the raw tree MAX.
        ("(x + x) * y", max, 0.5),
        // Overflow then multiplication by zero: 0 with saturation, NaN without.
        ("(x * x) * y", max, 0.0),
        ("-(x * y) - (x * y)", max, -2.0),
        ("(x * y + 1.0) * x - y", -3.5, 1.25),
    ] {
        let expressions =
            [MirOptimization::Disabled, MirOptimization::Enabled].map(|optimization| {
                let mut session = CompilerSession::new();
                session.set_mir_optimization(optimization);
                let entry = compile(
                    &mut session,
                    &format!("fn compute(x: float, y: float) -> float {{ {source} }}"),
                );
                let code = CompiledProgram::compile(&session, entry).unwrap();
                let mut instance = code.instantiate::<(Float, Float), Float>().unwrap();
                instance
                    .run(
                        (Float::new(x).unwrap(), Float::new(y).unwrap()),
                        WasmLimits::default(),
                    )
                    .unwrap()
                    .into_inner()
                    .to_bits()
            });
        assert_eq!(expressions[0], expressions[1], "{source} at ({x}, {y})");
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_ordered_comparisons_select_predicates() {
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
            matches!(
                op,
                Operator::I32LtS | Operator::I32LeS | Operator::I32GtS | Operator::I32GeS
            )
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
        ("x < y", -0.0, 0.0, false, false),
        ("x <= y", -0.0, 0.0, true, false),
        ("x > y", 0.0, -0.0, false, false),
        ("x >= y", 0.0, -0.0, true, false),
        ("x < y", -f64::MAX, f64::MAX, true, false),
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
            matches!(
                op,
                Operator::F64Lt | Operator::F64Le | Operator::F64Gt | Operator::F64Ge
            )
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
fn wasm_codegen_comparison_switches_use_one_predicate() {
    for ty in ["int", "float"] {
        for (case, positive) in [
            ("Less", true),
            ("Less", false),
            ("Equal", true),
            ("Equal", false),
            ("Greater", true),
            ("Greater", false),
        ] {
            let mut session = CompilerSession::new();
            let entry = compile(
                &mut session,
                &format!(
                    "fn compute(x: {ty}, y: {ty}) -> int {{ if (match cmp(x, y) {{ {case} => {positive}, _ => {} }}) {{ 7 }} else {{ 9 }} }}",
                    !positive,
                ),
            );
            let code = CompiledProgram::compile(&session, entry).unwrap();
            let operators = exported_function_operators(code.bytes(), ENTRY_EXPORT);
            let predicates = operators
                .iter()
                .filter(|op| {
                    matches!(
                        op,
                        Operator::I32LtS
                            | Operator::I32LeS
                            | Operator::I32GtS
                            | Operator::I32GeS
                            | Operator::I32Eq
                            | Operator::I32Ne
                            | Operator::F64Lt
                            | Operator::F64Le
                            | Operator::F64Gt
                            | Operator::F64Ge
                            | Operator::F64Eq
                            | Operator::F64Ne
                    )
                })
                .count();
            assert_eq!(predicates, 1, "{ty} {case} {positive}: {operators:?}");
            assert!(
                !operators.iter().any(|op| matches!(op, Operator::Select)),
                "{operators:?}"
            );
            for (left, right, actual) in [(-3, 2, "Less"), (2, 2, "Equal"), (3, -2, "Greater")] {
                let expected = if (actual == case) == positive { 7 } else { 9 };
                let result = if ty == "int" {
                    code.instantiate::<(isize, isize), isize>()
                        .unwrap()
                        .run((left, right), WasmLimits::default())
                        .unwrap()
                } else {
                    code.instantiate::<(Float, Float), isize>()
                        .unwrap()
                        .run(
                            (
                                Float::new(left as f64).unwrap(),
                                Float::new(right as f64).unwrap(),
                            ),
                            WasmLimits::default(),
                        )
                        .unwrap()
                };
                assert_eq!(result, expected, "{ty} {case} {positive} {left} {right}");
            }
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_comparison_switch_nested_arms_join() {
    let mut session = CompilerSession::new();
    let entry = compile(
        &mut session,
        "fn compute(x: int, y: int) -> int { \
            let z = if (match cmp(x + 1, y * 2) { Less => true, _ => false }) { \
                if x > 0 { x * 5 } else { x * 7 } \
            } else { if y > 0 { y * 11 } else { y * 13 } }; z + 1 }",
    );
    let code = CompiledProgram::compile(&session, entry).unwrap();
    let operators = exported_function_operators(code.bytes(), ENTRY_EXPORT);
    assert_eq!(
        operators
            .iter()
            .filter(|op| matches!(op, Operator::I32LtS))
            .count(),
        1,
        "{operators:?}"
    );
    assert!(
        !operators.iter().any(|op| matches!(op, Operator::Select)),
        "{operators:?}"
    );
    let mut instance = code.instantiate::<(isize, isize), isize>().unwrap();
    for (x, y) in [(1, 2), (-3, 2), (7, 2), (2, -3), (-2, -3)] {
        let expected = if x + 1 < y * 2 {
            if x > 0 { x * 5 } else { x * 7 }
        } else if y > 0 {
            y * 11
        } else {
            y * 13
        } + 1;
        assert_eq!(
            instance.run((x, y), WasmLimits::default()).unwrap(),
            expected
        );
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_materializes_escaping_ordering_tags() {
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
            "escaping {ty} ordering tag should not call native glue"
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
fn wasm_codegen_value_ne_defaults_and_overrides() {
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        for override_ne in ["", "fn ne(a: Probe, b: Probe) -> bool { false }"] {
            let mut session = CompilerSession::new();
            session.set_allow_unsafe(true);
            session.set_mir_optimization(optimization);
            session.set_physical_mir_optimization(optimization);
            let entry = compile(
                &mut session,
                &format!(
                    r#"
                struct Derived(int)
                struct Probe(int)
                impl Value for Probe {{
                    fn eq(a: Probe, b: Probe) -> bool {{ a.0 == b.0 }}
                    fn to_string(p: Probe) -> string {{ "Probe" }}
                    fn hash(p: Probe, h: &mut hasher) {{ hash(p.0, h) }}
                    fn clone(p: Probe) -> Probe {{ Probe(p.0) }}
                    fn drop(p: &mut Probe) {{}}
                    {override_ne}
                }}
                fn different<T>(a: T, b: T) -> bool where T: Value {{ a != b }}
                fn compute(x: int) -> bool {{
                    different(x, 7) and different(Derived(x), Derived(7))
                        and different([x], [7]) and different(Probe(x), Probe(7))
                }}
            "#
                ),
            );
            let code = CompiledProgram::compile(&session, entry).unwrap();
            let mut instance = code.instantiate::<(isize,), bool>().unwrap();
            assert!(!instance.run((7,), WasmLimits::default()).unwrap());
            assert_eq!(
                instance.run((8,), WasmLimits::default()).unwrap(),
                override_ne.is_empty()
            );
        }
    }
}

#[wasm_bindgen_test]
fn wasm_codegen_trait_callbacks_obey_call_depth_limits() {
    for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
        for default in ["", "fn other(x: Self) -> int { 0 }"] {
            let mut session = CompilerSession::new();
            session.set_mir_optimization(optimization);
            session.set_physical_mir_optimization(optimization);
            let entry = compile(
                &mut session,
                &format!(
                    r#"
                trait Loop<Self> {{ fn cycle(x: Self) -> int; {default} }}
                fn callback(x: int) -> int {{ cycle(x) }}
                fn bridge(f: (int) -> int, x: int) -> int {{ f(x) }}
                impl Loop for int {{ fn cycle(x: int) -> int {{ bridge(callback, x) }} }}
                fn compute(x: int) -> int {{ cycle(x) }}
            "#
                ),
            );
            let code = CompiledProgram::compile(&session, entry).unwrap();
            let mut instance = code.instantiate::<(isize,), isize>().unwrap();
            let limits = WasmLimits {
                execution: WasmLimits::default().execution.with_call_depth_limit(8),
                ..WasmLimits::default()
            };
            assert!(matches!(
                instance.run((1,), limits).unwrap_err().kind(),
                RuntimeErrorKind::SandboxViolation(
                    SandboxViolationKind::CallDepthLimitExceeded { .. }
                )
            ));
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
            // The entry is emitted first, after the shared failure function of a module with
            // runtime globals; exclude setup's reads of the host invocation state.
            let has_globals = Parser::new(0)
                .parse_all(code.bytes())
                .any(|payload| matches!(payload.unwrap(), Payload::GlobalSection(_)));
            let body = Parser::new(0)
                .parse_all(code.bytes())
                .filter_map(|payload| match payload.unwrap() {
                    Payload::CodeSectionEntry(body) => Some(body),
                    _ => None,
                })
                .nth(usize::from(has_globals))
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
fn wasm_codegen_borrows_static_string_handles_across_native_calls() {
    let mut session = CompilerSession::new();
    let entry = compile(
        &mut session,
        "fn compute(x: int) -> int { string_len(f\"left{x}éright\") }",
    );
    let code = CompiledProgram::compile(&session, entry).unwrap();
    let mut table_reads = 0;
    let operations = exported_function_operators(code.bytes(), ENTRY_EXPORT);
    for (index, operation) in operations.iter().enumerate() {
        if matches!(operation, Operator::I32Load { memarg }
            if memarg.offset == offset_of!(InvocationState, strings) as u64)
        {
            table_reads += 1;
            assert!(
                !operations[index + 1..]
                    .iter()
                    .take(3)
                    .any(|operation| matches!(operation, Operator::I32Load { .. })),
                "read-only literal handles must be borrowed, rather than loaded for a frame copy: {:?}",
                &operations[index.saturating_sub(1)..(index + 7).min(operations.len())]
            );
        }
    }
    assert!(
        table_reads >= 2,
        "fixture must use multiple static literal segments"
    );
    let mut instance = code.instantiate::<(isize,), isize>().unwrap();
    // Repeat calls with different allocations; table references remain valid throughout each.
    for (input, expected) in [(7, 11), (-123, 14), (0, 11)] {
        assert_eq!(
            instance.run((input,), WasmLimits::default()).unwrap(),
            expected
        );
    }
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
            format!("({expression} - 1)")
        })
    };
    let mut session = CompilerSession::new();
    let entry = compile(
        &mut session,
        &format!(
            "#[inline(never)] fn at_limit(x: int) -> int {{ {} }}
             #[inline(never)] fn over_limit(x: int) -> int {{ {} }}
             fn compute(x: int) -> int {{ at_limit(x) + over_limit(x) }}",
            // Each source subtraction becomes an alternating place writer and scalar load in
            // physical MIR, so 64 subtractions exercise approximately 128 producer hops. Emission
            // would fold a chain of constant additions.
            expression(64),
            expression(66),
        ),
    );
    let code = CompiledProgram::compile(&session, entry).unwrap();
    let maximum_stackified_subs = Parser::new(0)
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
                        .filter(|operation| matches!(operation, Operator::I32Sub))
                        .count()
                })
                .collect::<Vec<_>>()
        })
        .max()
        .unwrap();
    assert!(
        maximum_stackified_subs >= 64,
        "the expression at the depth limit must actually be emitted as one operand-stack chain"
    );

    let mut instance = code.instantiate::<(isize,), isize>().unwrap();
    assert_eq!(instance.run((12,), WasmLimits::default()).unwrap(), -106);
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

#[wasm_bindgen_test]
fn wasm_codegen_sharing_relocates_calls_and_debug_ranges() {
    use wasm_encoder::{
        CodeSection, ConstExpr, ElementSection, Elements, ExportKind, ExportSection, Function,
        FunctionSection, GlobalSection, GlobalType, Instruction as I, Module, RefType,
        TableSection, TableType, TypeSection, ValType,
    };

    let mut types = TypeSection::new();
    types.ty().function([], [ValType::I32]);
    types.ty().function([], [ValType::F64]);
    let mut functions = FunctionSection::new();
    let mut code = CodeSection::new();
    for _ in 0..130 {
        functions.function(0);
        let mut body = Function::new([]);
        body.instruction(&I::I32Const(7)).instruction(&I::End);
        code.function(&body);
    }
    for target in [129, 0] {
        functions.function(0);
        let mut body = Function::new([]);
        body.instruction(&I::Call(target)).instruction(&I::End);
        code.function(&body);
    }
    for zero in [0.0_f64, -0.0] {
        functions.function(1);
        let mut body = Function::new([]);
        body.instruction(&I::F64Const(zero.into()))
            .instruction(&I::End);
        code.function(&body);
    }
    let mut exports = ExportSection::new();
    exports.export("a", ExportKind::Func, 130);
    exports.export("b", ExportKind::Func, 131);
    let mut tables = TableSection::new();
    tables.table(TableType {
        element_type: RefType::FUNCREF,
        table64: false,
        minimum: 2,
        maximum: None,
        shared: false,
    });
    let mut elements = ElementSection::new();
    elements.active(
        None,
        &ConstExpr::i32_const(0),
        Elements::Functions(vec![130, 131].into()),
    );
    let mut globals = GlobalSection::new();
    globals.global(
        GlobalType {
            val_type: ValType::Ref(RefType::FUNCREF),
            mutable: false,
            shared: false,
        },
        &ConstExpr::ref_func(130),
    );
    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&tables)
        .section(&globals)
        .section(&exports)
        .section(&elements)
        .section(&code);
    let bytes = module.finish();
    let source = Location::new_synthesized().source_id();
    let sources = [(130, 1..4), (131, 1..3)]
        .into_iter()
        .enumerate()
        .map(|(origin, (body, bytes))| emit::CodeSourceMapEntry {
            body,
            bytes,
            span: Location::new(origin as u32, origin as u32 + 1, source),
            inlined_at: vec![],
        })
        .collect();
    let (shared, sources) = emit::share_functions(bytes.clone(), sources).unwrap();
    assert_eq!(shared, emit::share_functions(bytes, vec![]).unwrap().0);
    WebAssembly::Module::new(&Uint8Array::from(shared.as_slice())).unwrap();
    let mut targets = Vec::new();
    let mut table_targets = Vec::new();
    let mut global_target = None;
    let mut bodies = 0;
    let mut zeros = Vec::new();
    for payload in Parser::new(0).parse_all(&shared) {
        match payload.unwrap() {
            Payload::ExportSection(section) => {
                targets.extend(section.into_iter().map(|e| e.unwrap().index))
            }
            Payload::GlobalSection(section) => {
                for global in section {
                    let mut reader = global.unwrap().init_expr.get_operators_reader();
                    if let Operator::RefFunc { function_index } = reader.read().unwrap() {
                        global_target = Some(function_index);
                    }
                }
            }
            Payload::ElementSection(section) => {
                for element in section {
                    if let wasmparser::ElementItems::Functions(functions) = element.unwrap().items {
                        table_targets.extend(functions.into_iter().map(Result::unwrap));
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                bodies += 1;
                for operator in body.get_operators_reader().unwrap() {
                    if let Operator::F64Const { value } = operator.unwrap() {
                        zeros.push(value.bits());
                    }
                }
            }
            _ => {}
        }
    }
    assert_eq!(bodies, 4, "leaf and caller duplicates should each share");
    assert_eq!(targets[0], targets[1]);
    assert_eq!(global_target, Some(targets[0]));
    assert_eq!(
        table_targets, targets,
        "table slots must keep their order and follow function aliases"
    );
    assert_eq!(zeros, [0.0_f64.to_bits(), (-0.0_f64).to_bits()]);
    assert_eq!(sources.len(), 2);
    assert!(
        sources
            .iter()
            .all(|entry| entry.body == targets[0] as usize && entry.bytes == (1..3))
    );
}

#[wasm_bindgen_test]
fn wasm_codegen_sharing_stabilizes_recursive_components() {
    use wasm_encoder::{
        CodeSection, ExportKind, ExportSection, Function, FunctionSection, Instruction as I,
        Module, TypeSection, ValType,
    };

    let mut types = TypeSection::new();
    types.ty().function([], [ValType::I32]);
    let mut functions = FunctionSection::new();
    let mut code = CodeSection::new();
    for targets in [
        vec![2],
        vec![2],
        vec![0, 1],
        vec![2],
        vec![0, 1],
        vec![5],
        vec![6],
    ] {
        functions.function(0);
        let mut body = Function::new([]);
        for &target in &targets {
            body.instruction(&I::Call(target));
        }
        if targets.len() == 2 {
            body.instruction(&I::I32Add);
        }
        body.instruction(&I::End);
        code.function(&body);
    }
    let mut exports = ExportSection::new();
    for index in 0..7 {
        exports.export(&format!("f{index}"), ExportKind::Func, index);
    }
    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&exports)
        .section(&code);
    let (shared, _) = emit::share_functions(module.finish(), vec![]).unwrap();
    WebAssembly::Module::new(&Uint8Array::from(shared.as_slice())).unwrap();
    let mut targets = Vec::new();
    for payload in Parser::new(0).parse_all(&shared) {
        if let Payload::ExportSection(section) = payload.unwrap() {
            targets.extend(section.into_iter().map(|e| e.unwrap().index));
        }
    }
    assert_eq!(targets[0], targets[1]);
    assert_eq!(targets[0], targets[3]);
    assert_eq!(targets[2], targets[4]);
    assert_ne!(
        targets[5], targets[6],
        "different self references require a stronger equivalence proof"
    );
}
