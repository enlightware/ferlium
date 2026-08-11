// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;

use ferlium::{
    ExecutionTarget,
    compiler::error::{RuntimeErrorKind, SandboxViolationKind, SourceFailureKind},
    eval::RuntimeError,
    execution::ReferenceInterpreterLimits,
    format::FormatWith,
    hir::value::Value,
    mir::interpreter::Interpreter,
    module::ShowModuleWithOptions,
};

use crate::harness::{TestSession, bool, expected_tuple, int, int_value};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

fn prepare_mir(session: &mut TestSession, module_id: ferlium::module::ModuleId) {
    session
        .session_mut()
        .prepare_execution_target(ExecutionTarget::Mir, module_id);
}

fn run_mir_with_limits(
    session: &mut TestSession,
    source: &str,
    call_depth_limit: usize,
    fuel_limit: Option<usize>,
) -> Result<Value, RuntimeError> {
    let module_id = session.compile(source).module_id;
    let main_id = session
        .session()
        .expect_fresh_module(module_id)
        .get_local_function_id(ustr::ustr("main"))
        .expect("test source must define `fn main`");
    let limits = ReferenceInterpreterLimits::default()
        .with_call_depth_limit(call_depth_limit)
        .with_fuel_limit(fuel_limit);
    prepare_mir(session, module_id);
    let mut interpreter = Interpreter::with_limits(module_id, session.session(), limits);
    interpreter.run_main(module_id, main_id)
}

#[test]
fn execution_targets_accept_by_value_arguments() {
    let mut session = TestSession::new();
    let module_id = session
        .compile("fn add_one(value: int) -> int { value + 1 }")
        .module_id;
    let add_one_id = session
        .session()
        .expect_fresh_module(module_id)
        .get_local_function_id(ustr::ustr("add_one"))
        .unwrap();
    for target in ExecutionTarget::ALL {
        assert_val_eq!(
            session
                .session_mut()
                .run_entry(target, module_id, add_one_id, vec![int_value(41)])
                .unwrap(),
            int(42)
        );
    }
}

#[test]
fn execution_targets_use_configured_limits() {
    let mut session = TestSession::new();
    let output = session.compile("fn recover() -> int { 40 + 2 } loop {}");
    let entry = output.expr.expect("test source should have an expression");
    let recovery_entry = session
        .session()
        .expect_fresh_module(output.module_id)
        .get_local_function_id(ustr::ustr("recover"))
        .expect("test source should define a recovery function");
    let limits = ReferenceInterpreterLimits::default().with_fuel_limit(Some(0));

    for target in ExecutionTarget::ALL {
        let error = session
            .session_mut()
            .run_entry_with_limits(target, output.module_id, entry, vec![], limits)
            .expect_err("execution must consume the configured fuel");
        assert_eq!(
            error.kind(),
            RuntimeErrorKind::SandboxViolation(SandboxViolationKind::FuelExhausted)
        );

        // CompilerSession owns compiled artifacts, not one mutable executor generation. Interactive
        // front ends can therefore report a poisoned run and create a fresh executor for the next
        // evaluation without rebuilding the compiler session.
        assert_val_eq!(
            session
                .session_mut()
                .run_entry(target, output.module_id, recovery_entry, vec![])
                .expect("a fresh execution after a sandbox violation should succeed"),
            int(42)
        );
    }
}

#[test]
fn sandbox_violation_during_source_failure_cleanup_retains_both_causes() {
    let mut session = TestSession::new();
    let module_id = session
        .compile(
            r#"
                struct Bomb(int)

                impl Value for Bomb {
                    fn eq(left: Bomb, right: Bomb) -> bool { left.0 == right.0 }
                    fn to_string(value: Bomb) -> string { to_string(value.0) }
                    fn hash(value: Bomb, state: &mut hasher) { hash(value.0, state) }
                    fn clone(source: Bomb) -> Bomb { Bomb(source.0) }
                    fn drop(target: &mut Bomb) { loop {} }
                }

                fn main() -> int {
                    let bomb = Bomb(0);
                    idiv(1, 0)
                }
            "#,
        )
        .module_id;
    let main_id = session
        .session()
        .expect_fresh_module(module_id)
        .get_local_function_id(ustr::ustr("main"))
        .expect("test source should define `main`");
    let limits = ReferenceInterpreterLimits::default().with_fuel_limit(Some(0));

    for target in ExecutionTarget::ALL {
        let error = session
            .session_mut()
            .run_entry_with_limits(target, module_id, main_id, vec![], limits)
            .expect_err("the source failure's cleanup must exhaust fuel");
        let violation = error
            .sandbox_violation()
            .expect("cleanup fuel exhaustion must be a sandbox violation");
        assert_eq!(violation.kind(), SandboxViolationKind::FuelExhausted);
        assert_eq!(
            violation
                .interrupted_source_failure()
                .expect("the interrupted source failure must be retained")
                .kind(),
            SourceFailureKind::DivisionByZero
        );
    }
}

fn assert_fuel_violation_during_cleanup(
    session: &mut TestSession,
    source: &str,
    expected_drop_log: isize,
) {
    let limits = ReferenceInterpreterLimits::default().with_fuel_limit(Some(0));

    for target in ExecutionTarget::ALL {
        session
            .run("testing::reset_tracked_drops()")
            .discard_storage();
        let module_id = session.compile(source).module_id;
        let main_id = session
            .session()
            .expect_fresh_module(module_id)
            .get_local_function_id(ustr::ustr("main"))
            .expect("test source should define `main`");
        let error = session
            .session_mut()
            .run_entry_with_limits(target, module_id, main_id, vec![], limits)
            .expect_err("cleanup must exhaust fuel");
        assert_eq!(
            error.kind(),
            RuntimeErrorKind::SandboxViolation(SandboxViolationKind::FuelExhausted)
        );
        assert_val_eq!(
            session.run("testing::tracked_drop_log()"),
            int(expected_drop_log)
        );
    }
}

#[test]
fn sandbox_violation_during_inline_return_cleanup_reclaims_storage() {
    let mut session = TestSession::new();
    assert_fuel_violation_during_cleanup(
        &mut session,
        r#"
            struct Probe(int)
            struct Bomb(int)

            impl Value for Probe {
                fn eq(left: Probe, right: Probe) -> bool { left.0 == right.0 }
                fn to_string(value: Probe) -> string { to_string(value.0) }
                fn hash(value: Probe, state: &mut hasher) { hash(value.0, state) }
                fn clone(source: Probe) -> Probe { Probe(source.0) }
                fn drop(target: &mut Probe) { testing::record_tracked_drop(target.0) }
            }

            impl Value for Bomb {
                fn eq(left: Bomb, right: Bomb) -> bool { left.0 == right.0 }
                fn to_string(value: Bomb) -> string { to_string(value.0) }
                fn hash(value: Bomb, state: &mut hasher) { hash(value.0, state) }
                fn clone(source: Bomb) -> Bomb { Bomb(source.0) }
                fn drop(target: &mut Bomb) {
                    testing::record_tracked_drop(target.0);
                    loop {}
                }
            }

            fn main() {
                let outer = Probe(9);
                {
                    let bomb = Bomb(1);
                    return ();
                }
            }
        "#,
        1,
    );
}

#[test]
fn sandbox_violation_during_assignment_drop_reclaims_storage() {
    let mut session = TestSession::new();
    assert_fuel_violation_during_cleanup(
        &mut session,
        r#"
            struct Bomb(int)

            impl Value for Bomb {
                fn eq(left: Bomb, right: Bomb) -> bool { left.0 == right.0 }
                fn to_string(value: Bomb) -> string { to_string(value.0) }
                fn hash(value: Bomb, state: &mut hasher) { hash(value.0, state) }
                fn clone(source: Bomb) -> Bomb { Bomb(source.0) }
                fn drop(target: &mut Bomb) {
                    testing::record_tracked_drop(target.0);
                    loop {}
                }
            }

            fn main() {
                let mut value = Bomb(1);
                value = Bomb(2);
            }
        "#,
        1,
    );
}

/// Print the elaborated HIR of `src` for parameter-passing experiments.
/// Run with: `cargo nextest run hir_param --no-capture`
fn _print_param_hir(label: &str, src: &str) {
    let mut session = TestSession::new();
    let module_id = session.compile(src).module_id;
    let module = session.session().expect_fresh_module(module_id);
    let hir = module
        .format_with(&ShowModuleWithOptions::new(
            session.session().modules(),
            true,
            false,
        ))
        .to_string();
    println!("\n=== {label} ===\n--- source ---\n{src}\n--- hir ---\n{hir}");
    println!("--- locals ---");
    for name in module.own_symbols() {
        if let Some(f) = module.get_function(name) {
            println!("fn {name} ({} locals):", f.locals.len());
            for (i, l) in f.locals.iter().enumerate() {
                println!(
                    "  local {i}: name={:?} slot={:?} mut={:?} storage={:?} clone={:?} assign_mode={:?}",
                    l.name.0, l.slot, l.mut_ty, l.storage, l.clone, l.assignment_mode
                );
            }
        }
    }
}

#[test]
fn simple_functions() {
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn t(x: int) {x}"),
        r#"fn t(%p0: @arg let int, %p1: @ret int):
  b0:
    memcpy %p0 to %p1
    ret
"#,
    );
}

#[test]
fn call_functions() {
    let mut session = TestSession::new();

    assert_eq_sans_flake!(
        session.emit_mir("fn a0(x: int) { x + 1 }"),
        r#"fn a0(%p0: @arg let int, %p1: @ret int):
  @c0: int = 1
  b0:
    %r0 = alloca int
    store @c0 to %r0
    %r1 = alloca int
    call std::Num<std::int>::from_int#impl:25eabc6b(%r0, %r1)
    call std::Num<std::int>::add#impl:7665d3ee(%p0, %r1, %p1)
    ret
"#
    );

    assert_eq_sans_flake!(
        session.emit_mir("fn a0(x: int) { let y: int = 2 * x; y }"),
        r#"fn a0(%p0: @arg let int, %p1: @ret int):
  @c0: int = 2
  @c1: () = ()
  b0:
    %r0 = alloca int
    %r1 = alloca int
    store @c0 to %r1
    %r2 = alloca int
    call std::Num<std::int>::from_int#impl:25eabc6b(%r1, %r2)
    call std::Num<std::int>::mul#impl:a3604103(%r2, %p0, %r0)
    move %r0 to %p1
    ret
"#
    );
}

#[test]
fn match_case_functions() {
    let mut session = TestSession::new();

    assert_eq_sans_flake!(
        session.emit_mir("fn a0(x:int) {if true {x} else {2}}"),
        r#"fn a0(%p0: @arg let int, %p1: @ret int):
  @c0: bool = true
  @c1: int = 2
  b0:
    br b1
  b1:
    %r0 = comp_eq @c0 true
    condbr %r0, b2, b3
  b2:
    memcpy %p0 to %p1
    br b4
  b3:
    %r1 = alloca int
    store @c1 to %r1
    call std::Num<std::int>::from_int#impl:25eabc6b(%r1, %p1)
    br b4
  b4:
    ret
"#
    );

    assert_eq_sans_flake!(
        session.emit_mir("fn a0(x:int) {match x { 0 => x, 1 => x - 1, _ => -1 }}"),
        r#"fn a0(%p0: @arg let int, %p1: @ret int):
  @c0: int = 1
  b0:
    br b1
  b1:
    %r0 = comp_eq %p0 0
    condbr %r0, b2, b3
  b2:
    memcpy %p0 to %p1
    br b6
  b3:
    %r1 = comp_eq %p0 1
    condbr %r1, b4, b5
  b4:
    %r2 = alloca int
    store @c0 to %r2
    %r3 = alloca int
    call std::Num<std::int>::from_int#impl:25eabc6b(%r2, %r3)
    call std::Num<std::int>::sub#impl:6eee9827(%p0, %r3, %p1)
    br b6
  b5:
    %r4 = alloca int
    store @c0 to %r4
    %r5 = alloca int
    call std::Num<std::int>::from_int#impl:25eabc6b(%r4, %r5)
    call std::Num<std::int>::neg#impl:6b873453(%r5, %p1)
    br b6
  b6:
    ret
"#
    );
}

#[test]
fn user_function_call() {
    let mut sessions = TestSession::new();

    assert_eq_sans_flake!(
        sessions.emit_mir("fn a0(x: int) { a0(x) }"),
        r#"fn a0(%p0: @arg let int, %p1: @ret never):
  b0:
    check_call_depth
    call <test>::a0(%p0, %p1)
    ret
"#
    )
}

#[test]
fn mir_call_depth_limit_stops_recursive_execution() {
    let mut session = TestSession::new();
    let error = run_mir_with_limits(
        &mut session,
        "fn recurse() { recurse() } fn main() { recurse() }",
        4,
        None,
    )
    .expect_err("recursive MIR execution must reach the configured call-depth limit");
    assert_eq!(
        error.kind(),
        RuntimeErrorKind::SandboxViolation(SandboxViolationKind::CallDepthLimitExceeded {
            limit: 4
        })
    );
}

#[test]
fn mir_environment_cell_limit_stops_allocation_and_leaves_session_usable() {
    let mut session = TestSession::new();
    let module_id = session
        .compile("fn main() -> int { let x: int = 1; x }")
        .module_id;
    let main_id = session
        .session()
        .expect_fresh_module(module_id)
        .get_local_function_id(ustr::ustr("main"))
        .expect("test source must define `fn main`");
    let limits = ReferenceInterpreterLimits::default().with_environment_cell_limit(1);
    prepare_mir(&mut session, module_id);
    let mut interpreter = Interpreter::with_limits(module_id, session.session(), limits);
    let error = interpreter
        .run_main(module_id, main_id)
        .expect_err("MIR allocation must respect the configured environment cell limit");
    assert_eq!(
        error.kind(),
        RuntimeErrorKind::SandboxViolation(SandboxViolationKind::EnvironmentCellLimitExceeded {
            limit: 1
        })
    );
    assert!(interpreter.is_poisoned());
    assert_eq!(
        interpreter
            .run_main(module_id, main_id)
            .expect_err("a poisoned interpreter must reject re-entry")
            .kind(),
        RuntimeErrorKind::SandboxViolation(SandboxViolationKind::EnvironmentCellLimitExceeded {
            limit: 1
        })
    );

    let mut interpreter = Interpreter::new(module_id, session.session());
    assert_val_eq!(interpreter.run_main(module_id, main_id).unwrap(), int(1));
}

#[test]
fn sandbox_violation_during_closure_environment_drop_reclaims_the_temporary() {
    let mut session = TestSession::new();
    let module_id = session
        .compile(
            r#"
                struct Bomb(string)

                impl Value for Bomb {
                    fn eq(left: Bomb, right: Bomb) -> bool { left.0 == right.0 }
                    fn to_string(value: Bomb) -> string { to_string(value.0) }
                    fn hash(value: Bomb, state: &mut hasher) { hash(value.0, state) }
                    fn clone(source: Bomb) -> Bomb { Bomb(source.0) }
                    fn drop(target: &mut Bomb) {
                        let a00 = 0; let a01 = 0; let a02 = 0; let a03 = 0;
                        let a04 = 0; let a05 = 0; let a06 = 0; let a07 = 0;
                        let a08 = 0; let a09 = 0; let a10 = 0; let a11 = 0;
                        let a12 = 0; let a13 = 0; let a14 = 0; let a15 = 0;
                    }
                }

                fn main() {
                    let bomb = Bomb("owns a heap string");
                    let f = || bomb.0;
                    f()
                }
            "#,
        )
        .module_id;
    let main_id = session
        .session()
        .expect_fresh_module(module_id)
        .get_local_function_id(ustr::ustr("main"))
        .expect("test source should define `main`");
    prepare_mir(&mut session, module_id);

    // Sweep this implementation-detail limit to reach the cloned closure environment's drop.
    // A regression used to leave its resource-owning temporary live when the drop was cancelled,
    // causing native stack reclamation to panic in debug builds. Poisoning must instead reclaim
    // the backing storage without invoking further Ferlium cleanup.
    let mut observed_violation = false;
    for limit in 8..64 {
        let limits = ReferenceInterpreterLimits::default().with_environment_cell_limit(limit);
        let mut interpreter = Interpreter::with_limits(module_id, session.session(), limits);
        match interpreter.run_main(module_id, main_id) {
            Ok(value) => value.discard_storage(),
            Err(error) => {
                if matches!(
                    error.kind(),
                    RuntimeErrorKind::SandboxViolation(
                        SandboxViolationKind::EnvironmentCellLimitExceeded { .. }
                    )
                ) {
                    assert!(interpreter.is_poisoned());
                    observed_violation = true;
                }
            }
        }
    }
    assert!(
        observed_violation,
        "the swept limits should violate the environment-cell quota"
    );
}

#[test]
fn mir_completed_recursive_frames_reclaim_storage() {
    let mut session = TestSession::new();
    let source = r#"
        fn fibonacci(n: int) -> int {
            if n <= 1 { n } else { fibonacci(n - 1) + fibonacci(n - 2) }
        }

        fn main() -> int { fibonacci(20) }
    "#;

    assert_val_eq!(
        run_mir_with_limits(&mut session, source, 128, None).unwrap(),
        int(6765),
    );
}

#[test]
fn reused_mir_interpreter_reclaims_dropped_frames() {
    let mut session = TestSession::new();
    let source = r#"
        struct Probe(int)

        impl Value for Probe {
            fn eq(left: Probe, right: Probe) -> bool { left.0 == right.0 }
            fn to_string(value: Probe) -> string { to_string(value.0) }
            fn hash(value: Probe, state: &mut hasher) { hash(value.0, state) }
            fn clone(source: Probe) -> Probe { Probe(source.0) }
            fn drop(target: &mut Probe) { testing::record_tracked_drop(target.0) }
        }

        fn fibonacci(n: int) -> int {
            if n <= 1 { n } else { fibonacci(n - 1) + fibonacci(n - 2) }
        }

        fn main() -> int {
            testing::reset_tracked_drops();
            let owned = Probe(7);
            fibonacci(16)
        }
    "#;
    let module_id = session.compile(source).module_id;
    let main_id = session
        .session()
        .expect_fresh_module(module_id)
        .get_local_function_id(ustr::ustr("main"))
        .expect("test source must define `fn main`");
    prepare_mir(&mut session, module_id);
    let mut interpreter = Interpreter::new(module_id, session.session());

    for _ in 0..3 {
        let value = interpreter.run_main(module_id, main_id).unwrap();
        assert_val_eq!(value, int(987));
    }
    drop(interpreter);
    assert_val_eq!(session.run("testing::tracked_drop_log()"), int(7));
}

#[test]
fn load_place() {
    let mut session = TestSession::new();

    let src = "fn add() {
      let k: int = 1;
      let r = k + 3;

      r
    }
    ";

    // Print the HIR (with details, like `--print-std-full`).
    let module_id = session.compile(src).module_id;
    let module = session.session().expect_fresh_module(module_id);
    let hir = module
        .format_with(&ShowModuleWithOptions::new(
            session.session().modules(),
            true,
            false,
        ))
        .to_string();

    // let mir = session.emit_mir(src);
    println!("\n=== source ===\n{src}\n=== hir ===\n{hir}");
}

#[test]
fn use_mutable_arg() {
    let mut session = TestSession::new();

    let src = "
    ";

    // Print the HIR (with details, like `--print-std-full`).
    let module_id = session.compile(src).module_id;
    let module = session.session().expect_fresh_module(module_id);
    let hir = module
        .format_with(&ShowModuleWithOptions::new(
            session.session().modules(),
            true,
            false,
        ))
        .to_string();

    // let mir = session.emit_mir(src);
    println!("\n=== source ===\n{src}\n=== hir ===\n{hir}");
}

#[test]
fn factorial() {
    let mut sessions = TestSession::new();

    assert_eq_sans_flake!(
        sessions.emit_mir("fn factorial(x: int) {if x > 1 {x * factorial(x - 1)} else {1}}"),
        r#"fn factorial(%p0: @arg let int, %p1: @ret int):
  @c0: int = 1
  b0:
    check_call_depth
    %r0 = alloca int
    store @c0 to %r0
    %r1 = alloca int
    call std::Num<std::int>::from_int#impl:25eabc6b(%r0, %r1)
    %r2 = alloca bool
    call std::gt(dict(std::Ord<std::int>), %p0, %r1, %r2)
    br b1
  b1:
    %r3 = comp_eq %r2 true
    condbr %r3, b2, b3
  b2:
    %r4 = alloca int
    store @c0 to %r4
    %r5 = alloca int
    call std::Num<std::int>::from_int#impl:25eabc6b(%r4, %r5)
    %r6 = alloca int
    call std::Num<std::int>::sub#impl:6eee9827(%p0, %r5, %r6)
    %r7 = alloca int
    call <test>::factorial(%r6, %r7)
    call std::Num<std::int>::mul#impl:a3604103(%p0, %r7, %p1)
    br b4
  b3:
    %r8 = alloca int
    store @c0 to %r8
    call std::Num<std::int>::from_int#impl:25eabc6b(%r8, %p1)
    br b4
  b4:
    ret
"#
    );
}

#[test]
fn place_call_into_alias_local_branch() {
    // A `let` alias initialized from a non-place expression (an `if` over place calls) aliases a
    // materialized temporary: each branch copies its element value into the temporary, and the
    // alias reads through it.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(a: [int]) -> int { let x = if true { a[6] } else { a[4] }; x }"),
        r#"fn f(%p0: @arg let [int], %p1: @ret int):
  @c0: bool = true
  @c1: int = 6
  @c2: int = 4
  @c3: () = ()
  b0:
    %r0 = alloca int
    br b1
  b1:
    %r1 = comp_eq @c0 true
    condbr %r1, b2, b3
  b2:
    %r2 = alloca int
    store @c1 to %r2
    %r3 = alloca_place int
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r2, %r3) -> b5 error b6
  b3:
    %r5 = alloca int
    store @c2 to %r5
    %r6 = alloca_place int
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r5, %r6) -> b7 error b6
  b4:
    move %r0 to %p1
    ret
  b5:
    %r4 = load %r3
    memcpy %r4 to %r0
    br b4
  b6:
    propagate_error
  b7:
    %r7 = load %r6
    memcpy %r7 to %r0
    br b4
"#,
    );
}

#[test]
fn iter1_multi_param_value() {
    // Two by-value (TrivialCopy) params, both read -> bare %p0/%p1, no allocas.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x: int, y: int) { x + y }"),
        r#"fn f(%p0: @arg let int, %p1: @arg let int, %p2: @ret int):
  b0:
    call std::Num<std::int>::add#impl:7665d3ee(%p0, %p1, %p2)
    ret
"#,
    );
}

#[test]
fn iter1_mut_local_copy() {
    // `mut x` = mutable LOCAL COPY (Owned, slot 1) seeded from the by-value param
    // (%p0). The copy gets an `alloca`; the param itself stays `%p0`.
    // Caller is NOT affected (value semantics).
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn add_one(mut x: int) -> int { x = x + 1; x }"),
        r#"fn add_one(%p0: @arg let int, %p1: @ret int):
  @c0: () = ()
  @c1: int = 1
  b0:
    %r0 = alloca int
    memcpy %p0 to %r0
    %r1 = alloca int
    %r2 = alloca int
    store @c1 to %r2
    %r3 = alloca int
    call std::Num<std::int>::from_int#impl:25eabc6b(%r2, %r3)
    call std::Num<std::int>::add#impl:7665d3ee(%r0, %r3, %r1)
    move %r1 to %r0
    memcpy %r0 to %p1
    ret
"#,
    );
}

#[test]
fn iter1_let_mut_move_return() {
    // `let mut y = x` -> Owned local (alloca) initialized by a trivial-copy clone
    // of the by-value param; tail `y` is a `TakeLocalValue(MoveOwned)` -> load + no
    // drop (drop is Skip for int anyway).
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x: int) { let mut y = x; y = y + 1; y }"),
        r#"fn f(%p0: @arg let int, %p1: @ret int):
  @c0: () = ()
  @c1: int = 1
  b0:
    %r0 = alloca int
    memcpy %p0 to %r0
    %r1 = alloca int
    %r2 = alloca int
    store @c1 to %r2
    %r3 = alloca int
    call std::Num<std::int>::from_int#impl:25eabc6b(%r2, %r3)
    call std::Num<std::int>::add#impl:7665d3ee(%r0, %r3, %r1)
    move %r1 to %r0
    move %r0 to %p1
    ret
"#,
    );
}

#[test]
fn array_index_read() {
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn r(a: [bool]) -> int { if a[0] { 1 } else { 2 } }"),
        r#"fn r(%p0: @arg let [bool], %p1: @ret int):
  @c0: int = 0
  @c1: () = ()
  @c2: int = 1
  @c3: int = 2
  b0:
    %r0 = alloca bool
    %r1 = alloca int
    store @c0 to %r1
    %r2 = alloca_place bool
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r1, %r2) -> b1 error b2
  b1:
    %r3 = load %r2
    memcpy %r3 to %r0
    br b3
  b2:
    propagate_error
  b3:
    %r4 = comp_eq %r0 true
    condbr %r4, b4, b5
  b4:
    %r5 = alloca int
    store @c2 to %r5
    call std::Num<std::int>::from_int#impl:25eabc6b(%r5, %p1)
    br b6
  b5:
    %r6 = alloca int
    store @c3 to %r6
    call std::Num<std::int>::from_int#impl:25eabc6b(%r6, %p1)
    br b6
  b6:
    ret
"#,
    );
}

#[test]
fn array_index_assign() {
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn s(a: &mut [bool]) { a[1] = true; }"),
        r#"fn s(%p0: @arg &mut [bool], %p1: @ret ()):
  @c0: int = 1
  @c1: bool = true
  @c2: () = ()
  b0:
    %r0 = alloca int
    store @c0 to %r0
    %r1 = alloca_place bool
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r0, %r1) -> b1 error b2
  b1:
    %r2 = load %r1
    %r3 = alloca bool
    store @c1 to %r3
    move %r3 to %r2
    store @c2 to %p1
    ret
  b2:
    propagate_error
"#,
    );
}

#[test]
fn place_call_returned_as_value() {
    // A place-returning call in value position must resolve the place and copy the value out;
    // the value destination (here the return out-pointer) must NOT be passed as the place
    // out-slot of the call.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn first(a: [int]) -> int { a[0] }"),
        r#"fn first(%p0: @arg let [int], %p1: @ret int):
  @c0: int = 0
  b0:
    %r0 = alloca int
    store @c0 to %r0
    %r1 = alloca_place int
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r0, %r1) -> b1 error b2
  b1:
    %r2 = load %r1
    memcpy %r2 to %p1
    ret
  b2:
    propagate_error
"#,
    );
}

#[test]
fn place_call_into_owned_local() {
    // A place-returning call initializing an owned (`let mut`) local copies the element value
    // into the local's alloca; the local must hold the value, not the element address.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(a: [int]) -> int { let mut x = a[0]; x = x + 1; x }"),
        r#"fn f(%p0: @arg let [int], %p1: @ret int):
  @c0: int = 0
  @c1: () = ()
  @c2: int = 1
  b0:
    %r0 = alloca int
    %r1 = alloca int
    store @c0 to %r1
    %r2 = alloca_place int
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r1, %r2) -> b1 error b2
  b1:
    %r3 = load %r2
    memcpy %r3 to %r0
    %r4 = alloca int
    %r5 = alloca int
    store @c2 to %r5
    %r6 = alloca int
    call std::Num<std::int>::from_int#impl:25eabc6b(%r5, %r6)
    call std::Num<std::int>::add#impl:7665d3ee(%r0, %r6, %r4)
    move %r4 to %r0
    move %r0 to %p1
    ret
  b2:
    propagate_error
"#,
    );
}

#[test]
fn place_call_discarded() {
    // A discarded place-returning call still lowers (for its effects),
    // writing the place into a throwaway `alloca_place`.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(a: [int]) { a[0]; }"),
        r#"fn f(%p0: @arg let [int], %p1: @ret ()):
  @c0: int = 0
  @c1: () = ()
  b0:
    %r0 = alloca int
    %r1 = alloca int
    store @c0 to %r1
    %r2 = alloca_place int
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r1, %r2) -> b1 error b2
  b1:
    %r3 = load %r2
    memcpy %r3 to %r0
    store @c1 to %p1
    ret
  b2:
    propagate_error
"#,
    );
}

#[test]
fn nested_place_call() {
    // A place-returning call whose base is itself a place-returning call chains the loaded
    // place pointers.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(a: [[int]]) -> int { a[0][1] }"),
        r#"fn f(%p0: @arg let [[int]], %p1: @ret int):
  @c0: int = 0
  @c1: () = ()
  @c2: int = 1
  b0:
    %r0 = alloca [int]
    %r1 = alloca int
    %r2 = alloca int
    store @c0 to %r2
    %r3 = alloca_place [int]
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r2, %r3) -> b1 error b2
  b1:
    %r4 = load %r3
    clone [int] %r4 to %r0 via <test>::std::Value<[std::int]>::clone#impl:94a041f9
    %r5 = alloca int
    store @c2 to %r5
    %r6 = alloca_place int
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%r0, %r5, %r6) -> b3 error b2
  b2:
    drop [int] %r0 via <test>::std::Value<[std::int]>::drop#impl:a4f41aeb
    propagate_error
  b3:
    %r7 = load %r6
    memcpy %r7 to %r1
    move %r1 to %p1
    drop [int] %r0 via <test>::std::Value<[std::int]>::drop#impl:a4f41aeb
    ret

fn std::Value<[std::int]>::ALIGN#impl:90f3bfea(%p0: @ret int):
  @c0: int = 8
  b0:
    store @c0 to %p0
    ret

fn std::Value<[std::int]>::SIZE#impl:9ddb92fe(%p0: @ret int):
  @c0: int = 48
  b0:
    store @c0 to %p0
    ret

fn std::Value<[std::int]>::clone#impl:94a041f9(%p0: @arg let [int], %p1: @ret [int]):
  b0:
    call std::Value<[A]>::clone#impl:5d7e5692(dict(<test>::std::Value<[std::int]>), dict(std::Value<std::int>), %p0, %p1)
    ret

fn std::Value<[std::int]>::drop#impl:a4f41aeb(%p0: @arg &mut [int], %p1: @ret ()):
  b0:
    call std::Value<[A]>::drop#impl:4499dda8(dict(<test>::std::Value<[std::int]>), dict(std::Value<std::int>), %p0, %p1)
    ret

fn std::Value<[std::int]>::eq#impl:7e1688d4(%p0: @arg let [int], %p1: @arg let [int], %p2: @ret bool):
  b0:
    call std::Value<[A]>::eq#impl:82e999e1(dict(<test>::std::Value<[std::int]>), dict(std::Value<std::int>), %p0, %p1, %p2)
    ret

fn std::Value<[std::int]>::hash#impl:0aca59c2(%p0: @arg let [int], %p1: @arg &mut hasher, %p2: @ret ()):
  b0:
    call std::Value<[A]>::hash#impl:2f76a94b(dict(<test>::std::Value<[std::int]>), dict(std::Value<std::int>), %p0, %p1, %p2)
    ret

fn std::Value<[std::int]>::to_string#impl:892a091b(%p0: @arg let [int], %p1: @ret string):
  b0:
    call std::Value<[A]>::to_string#impl:c74a3a78(dict(<test>::std::Value<[std::int]>), dict(std::Value<std::int>), %p0, %p1)
    ret
"#,
    );
}

#[test]
fn place_call_as_let_argument() {
    // A place-returning call passed as a `Let` argument forwards the loaded place
    // pointer directly, with no copy.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn g(s: [int]) { } fn f(a: [[int]]) { g(a[0]) }"),
        r#"fn f(%p0: @arg let [[int]], %p1: @ret ()):
  @c0: int = 0
  b0:
    %r0 = alloca int
    store @c0 to %r0
    %r1 = alloca_place [int]
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r0, %r1) -> b1 error b2
  b1:
    %r2 = load %r1
    call <test>::g(%r2, %p1)
    ret
  b2:
    propagate_error

fn g(%p0: @arg let [int], %p1: @ret ()):
  @c0: () = ()
  b0:
    store @c0 to %p1
    ret
"#,
    );
}

#[test]
fn place_call_as_mutable_ref_argument() {
    // A place-returning call passed as a mutable-reference argument forwards the loaded place
    // pointer directly, with no copy.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn g(s: &mut [int]) { } fn f(a: &mut [[int]]) { g(a[0]) }"),
        r#"fn f(%p0: @arg &mut [[int]], %p1: @ret ()):
  @c0: int = 0
  b0:
    %r0 = alloca int
    store @c0 to %r0
    %r1 = alloca_place [int]
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r0, %r1) -> b1 error b2
  b1:
    %r2 = load %r1
    call <test>::g(%r2, %p1)
    ret
  b2:
    propagate_error

fn g(%p0: @arg &mut [int], %p1: @ret ()):
  @c0: () = ()
  b0:
    store @c0 to %p1
    ret
"#,
    );
}

#[test]
fn projection_of_place_call() {
    // A projection rooted in a place-returning call projects out of the loaded place pointer.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(a: [(int, bool)]) -> bool { a[0].1 }"),
        r#"fn f(%p0: @arg let [(int, bool)], %p1: @ret bool):
  @c0: int = 0
  @c1: () = ()
  @c2: int = 1
  b0:
    %r0 = alloca (int, bool)
    %r1 = alloca bool
    %r2 = alloca int
    store @c0 to %r2
    %r3 = alloca_place (int, bool)
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r2, %r3) -> b1 error b2
  b1:
    %r4 = load %r3
    memcpy %r4 to %r0
    %r5 = subfield @c2 from %r0
    memcpy %r5 to %r1
    move %r1 to %p1
    ret
  b2:
    propagate_error

fn std::Value<(std::int, std::bool)>::ALIGN#impl:9cca4d8c(%p0: @ret int):
  @c0: int = 8
  b0:
    store @c0 to %p0
    ret

fn std::Value<(std::int, std::bool)>::SIZE#impl:1462ea00(%p0: @ret int):
  @c0: int = 16
  b0:
    store @c0 to %p0
    ret

fn std::Value<(std::int, std::bool)>::clone#impl:c6a2252d(%p0: @arg let (int, bool), %p1: @ret (int, bool)):
  @c0: int = 0
  @c1: int = 1
  b0:
    %r0 = subfield @c0 from %p1
    %r1 = subfield @c0 from %p0
    call std::Value<std::int>::clone#impl:2d38cab9(%r1, %r0)
    %r2 = subfield @c1 from %p1
    %r3 = subfield @c1 from %p0
    call std::Value<std::bool>::clone#impl:0e47e282(%r3, %r2)
    ret

fn std::Value<(std::int, std::bool)>::drop#impl:2f5156cf(%p0: @arg &mut (int, bool), %p1: @ret ()):
  @c0: int = 0
  @c1: int = 1
  @c2: () = ()
  b0:
    %r0 = subfield @c0 from %p0
    %r1 = alloca ()
    call std::Value<std::int>::drop#impl:76f3f2ef(%r0, %r1)
    %r2 = subfield @c1 from %p0
    %r3 = alloca ()
    call std::Value<std::bool>::drop#impl:17fb3d04(%r2, %r3)
    store @c2 to %p1
    ret

fn std::Value<(std::int, std::bool)>::eq#impl:8240623e(%p0: @arg let (int, bool), %p1: @arg let (int, bool), %p2: @ret bool):
  @c0: int = 0
  @c1: int = 1
  @c2: bool = true
  @c3: bool = false
  b0:
    %r0 = subfield @c0 from %p0
    %r1 = subfield @c0 from %p1
    %r2 = alloca bool
    call std::Value<std::int>::eq#impl:87044288(%r0, %r1, %r2)
    br b1
  b1:
    %r3 = comp_eq %r2 true
    condbr %r3, b2, b3
  b2:
    %r4 = subfield @c1 from %p0
    %r5 = subfield @c1 from %p1
    %r6 = alloca bool
    call std::Value<std::bool>::eq#impl:fd9b066d(%r4, %r5, %r6)
    br b5
  b3:
    store @c3 to %p2
    br b4
  b4:
    ret
  b5:
    %r7 = comp_eq %r6 true
    condbr %r7, b6, b7
  b6:
    store @c2 to %p2
    br b8
  b7:
    store @c3 to %p2
    br b8
  b8:
    br b4

fn std::Value<(std::int, std::bool)>::hash#impl:d83c2054(%p0: @arg let (int, bool), %p1: @arg &mut hasher, %p2: @ret ()):
  @c0: int = 0
  @c1: int = 1
  @c2: () = ()
  b0:
    %r0 = subfield @c0 from %p0
    %r1 = alloca ()
    call std::Value<std::int>::hash#impl:bdc2934a(%r0, %p1, %r1)
    %r2 = subfield @c1 from %p0
    %r3 = alloca ()
    call std::Value<std::bool>::hash#impl:7e2c0813(%r2, %p1, %r3)
    store @c2 to %p2
    ret

fn std::Value<(std::int, std::bool)>::to_string#impl:8f2e215f(%p0: @arg let (int, bool), %p1: @ret string):
  @c0: StaticStr = "("
  @c1: () = ()
  @c2: int = 0
  @c3: StaticStr = ", "
  @c4: int = 1
  @c5: StaticStr = ")"
  b0:
    %r0 = alloca string
    %r1 = alloca string
    %r2 = alloca string
    %r3 = alloca StaticStr
    store @c0 to %r3
    call std::string_from_static(%r3, %r0)
    %r4 = subfield @c2 from %p0
    call std::Value<std::int>::to_string#impl:a5db1d9f(%r4, %r1)
    %r5 = alloca ()
    call std::string_push_str(%r0, %r1, %r5)
    drop string %r1 via std::Value<std::string>::drop#impl:1d429675
    %r6 = alloca StaticStr
    store @c3 to %r6
    %r7 = alloca ()
    call std::string_push_static_str(%r0, %r6, %r7)
    %r8 = subfield @c4 from %p0
    call std::Value<std::bool>::to_string#impl:044f2674(%r8, %r2)
    %r9 = alloca ()
    call std::string_push_str(%r0, %r2, %r9)
    drop string %r2 via std::Value<std::string>::drop#impl:1d429675
    %r10 = alloca StaticStr
    store @c5 to %r10
    %r11 = alloca ()
    call std::string_push_static_str(%r0, %r10, %r11)
    move %r0 to %p1
    ret
"#,
    );
}

#[test]
fn place_call_value_in_branches() {
    // Each branch resolves its own place and copies the value into the shared destination.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(a: [int], c: bool) -> int { if c { a[0] } else { a[1] } }"),
        r#"fn f(%p0: @arg let [int], %p1: @arg let bool, %p2: @ret int):
  @c0: int = 0
  @c1: int = 1
  b0:
    br b1
  b1:
    %r0 = comp_eq %p1 true
    condbr %r0, b2, b3
  b2:
    %r1 = alloca int
    store @c0 to %r1
    %r2 = alloca_place int
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r1, %r2) -> b5 error b6
  b3:
    %r4 = alloca int
    store @c1 to %r4
    %r5 = alloca_place int
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r4, %r5) -> b7 error b6
  b4:
    ret
  b5:
    %r3 = load %r2
    memcpy %r3 to %p2
    br b4
  b6:
    propagate_error
  b7:
    %r6 = load %r5
    memcpy %r6 to %p2
    br b4
"#,
    );
}

#[test]
fn place_call_into_alias_local() {
    // `let x = a[0]` makes `x` a `NonOwning` alias local: the local is rebound to the place
    // denoted by its initializer, with no store; the read goes through the alias.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(a: [int]) -> int { let x = a[0]; x }"),
        r#"fn f(%p0: @arg let [int], %p1: @ret int):
  @c0: int = 0
  @c1: () = ()
  b0:
    %r0 = alloca int
    %r1 = alloca int
    store @c0 to %r1
    %r2 = alloca_place int
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r1, %r2) -> b1 error b2
  b1:
    %r3 = load %r2
    memcpy %r3 to %r0
    move %r0 to %p1
    ret
  b2:
    propagate_error
"#,
    );
}

#[test]
fn iter1_apply() {
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x: int) { f(x) }"),
        r#"fn f(%p0: @arg let int, %p1: @ret never):
  b0:
    check_call_depth
    call <test>::f(%p0, %p1)
    ret
"#,
    );
}
#[test]
fn let_param_non_trivial() {
    // A concrete non-`TrivialCopy` parameter (`string`) uses the `Let` convention. In this
    // storage-explicit MIR form the parameter is a place, not a by-value register.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(s: string) { }"),
        r#"fn f(%p0: @arg let string, %p1: @ret ()):
  @c0: () = ()
  b0:
    store @c0 to %p1
    ret
"#,
    );
}

#[test]
fn let_param_generic() {
    // A generic parameter uses the `Let` convention regardless of any later concrete
    // instantiation, giving the polymorphic function one stable convention.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x) { }"),
        r#"fn f(%p0: @arg let A, %p1: @ret ()):
  @c0: () = ()
  b0:
    store @c0 to %p1
    ret
"#,
    );
}

#[test]
fn let_argument_forwards_existing_place() {
    // A `Let` argument that already denotes the required snapshot forwards its place directly,
    // with no additional copy or materialized temporary.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn u(s: string) { } fn caller(s: string) { u(s) }"),
        r#"fn caller(%p0: @arg let string, %p1: @ret ()):
  b0:
    call <test>::u(%p0, %p1)
    ret

fn u(%p0: @arg let string, %p1: @ret ()):
  @c0: () = ()
  b0:
    store @c0 to %p1
    ret
"#,
    );
}

#[test]
fn recursive_trivial_copy_call_uses_let_convention() {
    // `TrivialCopy` affects how snapshots are produced, not the high-level argument convention.
    // The storage-explicit MIR call passes the owned local's place under `Let`.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir(
            r#"
            fn f(a: int) {
                let n = 1;
                f(n)
            }
        "#
        ),
        r#"fn f(%p0: @arg let int, %p1: @ret never):
  @c0: int = 1
  @c1: () = ()
  b0:
    %r0 = alloca int
    check_call_depth
    %r1 = alloca int
    store @c0 to %r1
    call std::Num<std::int>::from_int#impl:25eabc6b(%r1, %r0)
    call <test>::f(%r0, %p1)
    ret
"#,
    );
}

#[test]
fn trivial_copy_call_uses_let_convention() {
    // `TrivialCopy` determines snapshot construction, not the call convention. The incoming `Let`
    // place is already a stable snapshot and is forwarded directly.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(a: int) { f(a) }"),
        r#"fn f(%p0: @arg let int, %p1: @ret never):
  b0:
    check_call_depth
    call <test>::f(%p0, %p1)
    ret
"#,
    );
}

#[test]
fn call_mutable_reference_argument_passes_owned_local_place() {
    // A `&mut` argument backed by an owned local forwards the local's `alloca` place so the callee
    // mutates the caller's storage.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir(
            r#"
        fn callee(m: &mut int) { }
        fn caller() {
            let mut m = 0;
            callee(m)
        }
        "#
        ),
        r#"fn callee(%p0: @arg &mut int, %p1: @ret ()):
  @c0: () = ()
  b0:
    store @c0 to %p1
    ret

fn caller(%p0: @ret ()):
  @c0: int = 0
  @c1: () = ()
  b0:
    %r0 = alloca int
    %r1 = alloca int
    store @c0 to %r1
    call std::Num<std::int>::from_int#impl:25eabc6b(%r1, %r0)
    call <test>::callee(%r0, %p0)
    ret
"#,
    );
}

#[test]
fn call_passes_all_argument_conventions() {
    // A single call covers both semantic argument conventions:
    //   `a: int`       (`Let`)        -> the materialized `from_int(1)` snapshot;
    //   `m: &mut int`  (`MutableRef`) -> the owned local's `alloca` place;
    //   `s: string`    (`Let`)        -> the incoming immutable place, forwarded directly.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir(
            r#"
            fn callee(a: int, m: &mut int, s: string) { }
            fn caller(s: string) {
                let mut m = 0;
                callee(1, m, s)
            }
            "#,
        ),
        r#"fn callee(%p0: @arg let int, %p1: @arg &mut int, %p2: @arg let string, %p3: @ret ()):
  @c0: () = ()
  b0:
    store @c0 to %p3
    ret

fn caller(%p0: @arg let string, %p1: @ret ()):
  @c0: int = 0
  @c1: () = ()
  @c2: int = 1
  b0:
    %r0 = alloca int
    %r1 = alloca int
    store @c0 to %r1
    call std::Num<std::int>::from_int#impl:25eabc6b(%r1, %r0)
    %r2 = alloca int
    store @c2 to %r2
    %r3 = alloca int
    call std::Num<std::int>::from_int#impl:25eabc6b(%r2, %r3)
    call <test>::callee(%r3, %r0, %p0, %p1)
    ret
"#,
    );
}

#[test]
fn mutable_reference_parameter() {
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x: &mut int) { x = 2; }"),
        r#"fn f(%p0: @arg &mut int, %p1: @ret ()):
  @c0: int = 2
  @c1: () = ()
  b0:
    %r0 = alloca int
    %r1 = alloca int
    store @c0 to %r1
    call std::Num<std::int>::from_int#impl:25eabc6b(%r1, %r0)
    move %r0 to %p0
    store @c1 to %p1
    ret
"#,
    );
}

#[test]
fn generic_apply() {
    let mut session = TestSession::new();
    // There is a dynamic stack allocation due to the conversion of the int 2 to A.
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x) { x * 2 }"),
        r#"fn f(%p0: @extra ((A, A) -> A, (A, A) -> A, (A, A) -> A, (A) -> A, (A) -> A, (A) -> A, (int) -> A), %p1: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A) -> A, (&mut A) -> (), () -> int, () -> int), %p2: @arg let A, %p3: @ret A):
  @c0: int = 2
  @c1: () = ()
  b0:
    %r0 = alloca A using %p1
    %r1 = dict_entry 2 from %p0
    %r2 = dict_entry 6 from %p0
    %r3 = alloca int
    store @c0 to %r3
    call %r2(%r3, %r0)
    call %r1(%p2, %r0, %p3)
    %r4 = dict_entry 4 from %p1
    drop A %r0 via %r4
    ret
"#,
    );
}

#[test]
fn dynamic_apply() {
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn apply_fn(f, x: int) { f(x) }"),
        r#"fn apply_fn(%p0: @arg let (int) -> A ! e₀, %p1: @arg let int, %p2: @ret A):
  b0:
    invoke call %p0(%p1, %p2) -> b1 error b2
  b1:
    ret
  b2:
    propagate_error
"#,
    );
}

#[test]
fn value_capturing_closure() {
    // A value-capturing closure (no hidden dictionary evidence): the captured `b` is snapshotted
    // into a temporary (`memcpy %r0 to %r5`), bundled into the closure value by `build_closure`, the
    // closure is called by borrowing its place (`call %r1`, no intervening load — so it survives
    // repeated calls and is dropped once), and dropped at scope exit through the generated
    // `Value::drop` for the closure type (whose body lowers `drop_closure_env`). The lambda body
    // reads its captured environment slot (`%p0`) directly.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn capture() -> int { let b = 1; let g = || b; g() }"),
        r#"fn $_ferlium_function_value_drop(%p0: @arg &mut A, %p1: @ret ()):
  @c0: () = ()
  b0:
    drop_closure_env %p0
    store @c0 to %p1
    ret

fn $lambda$1(%p0: @arg &mut int, %p1: @ret int):
  b0:
    memcpy %p0 to %p1
    ret

fn capture(%p0: @ret int):
  @c0: int = 1
  @c1: () = ()
  b0:
    %r0 = alloca int
    %r1 = alloca () -> int
    %r2 = alloca int
    store @c0 to %r2
    call std::Num<std::int>::from_int#impl:25eabc6b(%r2, %r0)
    %r3 = alloca int
    memcpy %r0 to %r3
    %r4 = build_closure <test>::$lambda$1(%r3, dict(<test>::std::Value<(std::int,)>))
    store %r4 to %r1
    call %r1(%p0)
    drop () -> int %r1 via <test>::$_ferlium_function_value_drop
    ret

fn std::Value<(std::int,)>::ALIGN#impl:2b73eccb(%p0: @ret int):
  @c0: int = 8
  b0:
    store @c0 to %p0
    ret

fn std::Value<(std::int,)>::SIZE#impl:ad9d7fe7(%p0: @ret int):
  @c0: int = 8
  b0:
    store @c0 to %p0
    ret

fn std::Value<(std::int,)>::clone#impl:7414fc52(%p0: @arg let (int,), %p1: @ret (int,)):
  @c0: int = 0
  b0:
    %r0 = subfield @c0 from %p1
    %r1 = subfield @c0 from %p0
    call std::Value<std::int>::clone#impl:2d38cab9(%r1, %r0)
    ret

fn std::Value<(std::int,)>::drop#impl:d5ec4f8c(%p0: @arg &mut (int,), %p1: @ret ()):
  @c0: int = 0
  @c1: () = ()
  b0:
    %r0 = subfield @c0 from %p0
    %r1 = alloca ()
    call std::Value<std::int>::drop#impl:76f3f2ef(%r0, %r1)
    store @c1 to %p1
    ret

fn std::Value<(std::int,)>::eq#impl:b00d2abd(%p0: @arg let (int,), %p1: @arg let (int,), %p2: @ret bool):
  @c0: int = 0
  @c1: bool = true
  @c2: bool = false
  b0:
    %r0 = subfield @c0 from %p0
    %r1 = subfield @c0 from %p1
    %r2 = alloca bool
    call std::Value<std::int>::eq#impl:87044288(%r0, %r1, %r2)
    br b1
  b1:
    %r3 = comp_eq %r2 true
    condbr %r3, b2, b3
  b2:
    store @c1 to %p2
    br b4
  b3:
    store @c2 to %p2
    br b4
  b4:
    ret

fn std::Value<(std::int,)>::hash#impl:58218263(%p0: @arg let (int,), %p1: @arg &mut hasher, %p2: @ret ()):
  @c0: int = 0
  @c1: () = ()
  b0:
    %r0 = subfield @c0 from %p0
    %r1 = alloca ()
    call std::Value<std::int>::hash#impl:bdc2934a(%r0, %p1, %r1)
    store @c1 to %p2
    ret

fn std::Value<(std::int,)>::to_string#impl:30b07f9c(%p0: @arg let (int,), %p1: @ret string):
  @c0: StaticStr = "("
  @c1: () = ()
  @c2: int = 0
  @c3: StaticStr = ")"
  b0:
    %r0 = alloca string
    %r1 = alloca string
    %r2 = alloca StaticStr
    store @c0 to %r2
    call std::string_from_static(%r2, %r0)
    %r3 = subfield @c2 from %p0
    call std::Value<std::int>::to_string#impl:a5db1d9f(%r3, %r1)
    %r4 = alloca ()
    call std::string_push_str(%r0, %r1, %r4)
    drop string %r1 via std::Value<std::string>::drop#impl:1d429675
    %r5 = alloca StaticStr
    store @c3 to %r5
    %r6 = alloca ()
    call std::string_push_static_str(%r0, %r5, %r6)
    move %r0 to %p1
    ret
"#,
    );
}

// ============================================================================
// Generic handling tests
// ============================================================================

#[test]
fn generic_two_same_type_params() {
    // Two parameters of the same generic type share the same Num dictionary; the call forwards
    // both `Let` argument places and the result pointer directly without an intermediate alloca.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x, y) { x + y }"),
        r#"fn f(%p0: @extra ((A, A) -> A, (A, A) -> A, (A, A) -> A, (A) -> A, (A) -> A, (A) -> A, (int) -> A), %p1: @arg let A, %p2: @arg let A, %p3: @ret A):
  b0:
    %r0 = dict_entry 0 from %p0
    call %r0(%p1, %p2, %p3)
    ret
"#,
    );
}

#[test]
fn generic_higher_order_function_param() {
    // A higher-order parameter `f: (A) -> A` uses `Let` with a function value whose generic
    // variable appears only under the function type (function-surface). The
    // call directly threads the incoming pointers with no intermediate alloca.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn apply(f: (A) -> A, x) { f(x) }"),
        r#"fn apply(%p0: @arg let (A) -> A ! e₀, %p1: @arg let A, %p2: @ret A):
  b0:
    invoke call %p0(%p1, %p2) -> b1 error b2
  b1:
    ret
  b2:
    propagate_error
"#,
    );
}

#[test]
fn generic_multiple_ops_reuse_witness() {
    // `x * x + x` requires two intermediate generic temporaries.  Both are allocated with
    // `alloca A using %p1`, confirming that the single Value dictionary witness (%p1) is reused
    // for every dynamic allocation of type A within the function.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x) { x * x + x }"),
        r#"fn f(%p0: @extra ((A, A) -> A, (A, A) -> A, (A, A) -> A, (A) -> A, (A) -> A, (A) -> A, (int) -> A), %p1: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A) -> A, (&mut A) -> (), () -> int, () -> int), %p2: @arg let A, %p3: @ret A):
  @c0: () = ()
  b0:
    %r0 = alloca A using %p1
    %r1 = dict_entry 0 from %p0
    %r2 = dict_entry 2 from %p0
    call %r2(%p2, %p2, %r0)
    call %r1(%r0, %p2, %p3)
    %r3 = dict_entry 4 from %p1
    drop A %r0 via %r3
    ret
"#,
    );
}

#[test]
fn generic_comparison() {
    // Comparing two generic values calls `Value::eq` projected from the Value dictionary (%p0).
    // The result is a concrete `bool`, so the return place needs no dynamic alloca.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x, y) { x == y }"),
        r#"fn f(%p0: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A) -> A, (&mut A) -> (), () -> int, () -> int), %p1: @arg let A, %p2: @arg let A, %p3: @ret bool):
  b0:
    %r0 = dict_entry 0 from %p0
    call %r0(%p1, %p2, %p3)
    ret
"#,
    );
}

// ============================================================================
// Copy and Move Tests
// ============================================================================

#[test]
fn copy_int() {
    // Copying an int (TrivialCopy) - should use trivial copy, not call clone
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x: int) { let y = x; y + 1 }"),
        r#"fn f(%p0: @arg let int, %p1: @ret int):
  @c0: () = ()
  @c1: int = 1
  b0:
    %r0 = alloca int
    memcpy %p0 to %r0
    %r1 = alloca int
    store @c1 to %r1
    %r2 = alloca int
    call std::Num<std::int>::from_int#impl:25eabc6b(%r1, %r2)
    call std::Num<std::int>::add#impl:7665d3ee(%r0, %r2, %p1)
    ret
"#,
    );
}

#[test]
fn construct_struct() {
    // Copying an int (TrivialCopy) - should use trivial copy, not call clone
    let mut session = TestSession::new();
    let mir = session.emit_mir(
        "struct A{ x: int, y: int }\
        \
        struct Wrapper { left: A, right: A }\
        \
        fn make_a() -> A {\
          A { x: 1, y: 2 }\
        }\
        \
        fn make_wrapper() -> Wrapper {\
          Wrapper { left: make_a(), right: make_a() }\
        }",
    );

    assert_eq_sans_flake!(
        mir,
        r#"fn make_a(%p0: @ret A):
  @c0: int = 0
  @c1: int = 1
  @c2: int = 2
  b0:
    %r0 = subfield @c0 from %p0
    %r1 = alloca int
    store @c1 to %r1
    call std::Num<std::int>::from_int#impl:25eabc6b(%r1, %r0)
    %r2 = subfield @c1 from %p0
    %r3 = alloca int
    store @c2 to %r3
    call std::Num<std::int>::from_int#impl:25eabc6b(%r3, %r2)
    ret

fn make_wrapper(%p0: @ret Wrapper):
  @c0: int = 0
  @c1: int = 1
  b0:
    %r0 = subfield @c0 from %p0
    call <test>::make_a(%r0)
    %r1 = subfield @c1 from %p0
    call <test>::make_a(%r1)
    ret

fn std::Value<<test>::A>::ALIGN#impl:b9fa7ef7(%p0: @ret int):
  @c0: int = 8
  b0:
    store @c0 to %p0
    ret

fn std::Value<<test>::A>::SIZE#impl:b6651763(%p0: @ret int):
  @c0: int = 16
  b0:
    store @c0 to %p0
    ret

fn std::Value<<test>::A>::clone#impl:3b26fee6(%p0: @arg let A, %p1: @ret A):
  @c0: int = 0
  @c1: int = 1
  b0:
    %r0 = subfield @c0 from %p1
    %r1 = subfield @c0 from %p0
    call std::Value<std::int>::clone#impl:2d38cab9(%r1, %r0)
    %r2 = subfield @c1 from %p1
    %r3 = subfield @c1 from %p0
    call std::Value<std::int>::clone#impl:2d38cab9(%r3, %r2)
    ret

fn std::Value<<test>::A>::drop#impl:e48f46c8(%p0: @arg &mut A, %p1: @ret ()):
  @c0: int = 0
  @c1: int = 1
  @c2: () = ()
  b0:
    %r0 = subfield @c0 from %p0
    %r1 = alloca ()
    call std::Value<std::int>::drop#impl:76f3f2ef(%r0, %r1)
    %r2 = subfield @c1 from %p0
    %r3 = alloca ()
    call std::Value<std::int>::drop#impl:76f3f2ef(%r2, %r3)
    store @c2 to %p1
    ret

fn std::Value<<test>::A>::eq#impl:601557a9(%p0: @arg let A, %p1: @arg let A, %p2: @ret bool):
  @c0: int = 0
  @c1: int = 1
  @c2: bool = true
  @c3: bool = false
  b0:
    %r0 = subfield @c0 from %p0
    %r1 = subfield @c0 from %p1
    %r2 = alloca bool
    call std::Value<std::int>::eq#impl:87044288(%r0, %r1, %r2)
    br b1
  b1:
    %r3 = comp_eq %r2 true
    condbr %r3, b2, b3
  b2:
    %r4 = subfield @c1 from %p0
    %r5 = subfield @c1 from %p1
    %r6 = alloca bool
    call std::Value<std::int>::eq#impl:87044288(%r4, %r5, %r6)
    br b5
  b3:
    store @c3 to %p2
    br b4
  b4:
    ret
  b5:
    %r7 = comp_eq %r6 true
    condbr %r7, b6, b7
  b6:
    store @c2 to %p2
    br b8
  b7:
    store @c3 to %p2
    br b8
  b8:
    br b4

fn std::Value<<test>::A>::hash#impl:2d1a24bf(%p0: @arg let A, %p1: @arg &mut hasher, %p2: @ret ()):
  @c0: int = 0
  @c1: int = 1
  @c2: () = ()
  b0:
    %r0 = subfield @c0 from %p0
    %r1 = alloca ()
    call std::Value<std::int>::hash#impl:bdc2934a(%r0, %p1, %r1)
    %r2 = subfield @c1 from %p0
    %r3 = alloca ()
    call std::Value<std::int>::hash#impl:bdc2934a(%r2, %p1, %r3)
    store @c2 to %p2
    ret

fn std::Value<<test>::A>::to_string#impl:78412598(%p0: @arg let A, %p1: @ret string):
  @c0: StaticStr = "A { "
  @c1: () = ()
  @c2: StaticStr = "x"
  @c3: StaticStr = ": "
  @c4: int = 0
  @c5: StaticStr = ", "
  @c6: StaticStr = "y"
  @c7: int = 1
  @c8: StaticStr = " }"
  b0:
    %r0 = alloca string
    %r1 = alloca string
    %r2 = alloca string
    %r3 = alloca StaticStr
    store @c0 to %r3
    call std::string_from_static(%r3, %r0)
    %r4 = alloca StaticStr
    store @c2 to %r4
    %r5 = alloca ()
    call std::string_push_static_str(%r0, %r4, %r5)
    %r6 = alloca StaticStr
    store @c3 to %r6
    %r7 = alloca ()
    call std::string_push_static_str(%r0, %r6, %r7)
    %r8 = subfield @c4 from %p0
    call std::Value<std::int>::to_string#impl:a5db1d9f(%r8, %r1)
    %r9 = alloca ()
    call std::string_push_str(%r0, %r1, %r9)
    drop string %r1 via std::Value<std::string>::drop#impl:1d429675
    %r10 = alloca StaticStr
    store @c5 to %r10
    %r11 = alloca ()
    call std::string_push_static_str(%r0, %r10, %r11)
    %r12 = alloca StaticStr
    store @c6 to %r12
    %r13 = alloca ()
    call std::string_push_static_str(%r0, %r12, %r13)
    %r14 = alloca StaticStr
    store @c3 to %r14
    %r15 = alloca ()
    call std::string_push_static_str(%r0, %r14, %r15)
    %r16 = subfield @c7 from %p0
    call std::Value<std::int>::to_string#impl:a5db1d9f(%r16, %r2)
    %r17 = alloca ()
    call std::string_push_str(%r0, %r2, %r17)
    drop string %r2 via std::Value<std::string>::drop#impl:1d429675
    %r18 = alloca StaticStr
    store @c8 to %r18
    %r19 = alloca ()
    call std::string_push_static_str(%r0, %r18, %r19)
    move %r0 to %p1
    ret

fn std::Value<<test>::Wrapper>::ALIGN#impl:a9f8abbf(%p0: @ret int):
  @c0: int = 8
  b0:
    store @c0 to %p0
    ret

fn std::Value<<test>::Wrapper>::SIZE#impl:21b54a2b(%p0: @ret int):
  @c0: int = 32
  b0:
    store @c0 to %p0
    ret

fn std::Value<<test>::Wrapper>::clone#impl:e02c4c62(%p0: @arg let Wrapper, %p1: @ret Wrapper):
  @c0: int = 0
  @c1: int = 1
  b0:
    %r0 = subfield @c0 from %p1
    %r1 = subfield @c0 from %p0
    call <test>::std::Value<<test>::A>::clone#impl:3b26fee6(%r1, %r0)
    %r2 = subfield @c1 from %p1
    %r3 = subfield @c1 from %p0
    call <test>::std::Value<<test>::A>::clone#impl:3b26fee6(%r3, %r2)
    ret

fn std::Value<<test>::Wrapper>::drop#impl:c2860560(%p0: @arg &mut Wrapper, %p1: @ret ()):
  @c0: int = 0
  @c1: int = 1
  @c2: () = ()
  b0:
    %r0 = subfield @c0 from %p0
    %r1 = alloca ()
    call <test>::std::Value<<test>::A>::drop#impl:e48f46c8(%r0, %r1)
    %r2 = subfield @c1 from %p0
    %r3 = alloca ()
    call <test>::std::Value<<test>::A>::drop#impl:e48f46c8(%r2, %r3)
    store @c2 to %p1
    ret

fn std::Value<<test>::Wrapper>::eq#impl:d6883255(%p0: @arg let Wrapper, %p1: @arg let Wrapper, %p2: @ret bool):
  @c0: int = 0
  @c1: int = 1
  @c2: bool = true
  @c3: bool = false
  b0:
    %r0 = subfield @c0 from %p0
    %r1 = subfield @c0 from %p1
    %r2 = alloca bool
    call <test>::std::Value<<test>::A>::eq#impl:601557a9(%r0, %r1, %r2)
    br b1
  b1:
    %r3 = comp_eq %r2 true
    condbr %r3, b2, b3
  b2:
    %r4 = subfield @c1 from %p0
    %r5 = subfield @c1 from %p1
    %r6 = alloca bool
    call <test>::std::Value<<test>::A>::eq#impl:601557a9(%r4, %r5, %r6)
    br b5
  b3:
    store @c3 to %p2
    br b4
  b4:
    ret
  b5:
    %r7 = comp_eq %r6 true
    condbr %r7, b6, b7
  b6:
    store @c2 to %p2
    br b8
  b7:
    store @c3 to %p2
    br b8
  b8:
    br b4

fn std::Value<<test>::Wrapper>::hash#impl:65f26de7(%p0: @arg let Wrapper, %p1: @arg &mut hasher, %p2: @ret ()):
  @c0: int = 0
  @c1: int = 1
  @c2: () = ()
  b0:
    %r0 = subfield @c0 from %p0
    %r1 = alloca ()
    call <test>::std::Value<<test>::A>::hash#impl:2d1a24bf(%r0, %p1, %r1)
    %r2 = subfield @c1 from %p0
    %r3 = alloca ()
    call <test>::std::Value<<test>::A>::hash#impl:2d1a24bf(%r2, %p1, %r3)
    store @c2 to %p2
    ret

fn std::Value<<test>::Wrapper>::to_string#impl:7f6f6750(%p0: @arg let Wrapper, %p1: @ret string):
  @c0: StaticStr = "Wrapper { "
  @c1: () = ()
  @c2: StaticStr = "left"
  @c3: StaticStr = ": "
  @c4: int = 0
  @c5: StaticStr = ", "
  @c6: StaticStr = "right"
  @c7: int = 1
  @c8: StaticStr = " }"
  b0:
    %r0 = alloca string
    %r1 = alloca string
    %r2 = alloca string
    %r3 = alloca StaticStr
    store @c0 to %r3
    call std::string_from_static(%r3, %r0)
    %r4 = alloca StaticStr
    store @c2 to %r4
    %r5 = alloca ()
    call std::string_push_static_str(%r0, %r4, %r5)
    %r6 = alloca StaticStr
    store @c3 to %r6
    %r7 = alloca ()
    call std::string_push_static_str(%r0, %r6, %r7)
    %r8 = subfield @c4 from %p0
    call <test>::std::Value<<test>::A>::to_string#impl:78412598(%r8, %r1)
    %r9 = alloca ()
    call std::string_push_str(%r0, %r1, %r9)
    drop string %r1 via std::Value<std::string>::drop#impl:1d429675
    %r10 = alloca StaticStr
    store @c5 to %r10
    %r11 = alloca ()
    call std::string_push_static_str(%r0, %r10, %r11)
    %r12 = alloca StaticStr
    store @c6 to %r12
    %r13 = alloca ()
    call std::string_push_static_str(%r0, %r12, %r13)
    %r14 = alloca StaticStr
    store @c3 to %r14
    %r15 = alloca ()
    call std::string_push_static_str(%r0, %r14, %r15)
    %r16 = subfield @c7 from %p0
    call <test>::std::Value<<test>::A>::to_string#impl:78412598(%r16, %r2)
    %r17 = alloca ()
    call std::string_push_str(%r0, %r2, %r17)
    drop string %r2 via std::Value<std::string>::drop#impl:1d429675
    %r18 = alloca StaticStr
    store @c8 to %r18
    %r19 = alloca ()
    call std::string_push_static_str(%r0, %r18, %r19)
    move %r0 to %p1
    ret
"#
    );
}

#[test]
fn copy_struct_with_explicit_clone() {
    // Copying a struct with explicit clone function - should call Value::clone
    let mut session = TestSession::new();
    let mir = session.emit_mir(
        r#"
            struct Probe(int)

            impl Value for Probe {
                fn eq(left: Probe, right: Probe) -> bool { left.0 == right.0 }
                fn to_string(value: Probe) -> string { to_string(value.0) }
                fn hash(value: Probe, state: &mut hasher) { hash(value.0, state) }
                fn clone(source: Probe) -> Probe {
                    Probe(source.0 + 100)
                }
                fn drop(target: &mut Probe) {}
            }

            fn f(x: Probe) { let y = x; y }
        "#,
    );

    assert_eq_sans_flake!(
        mir,
        r#"fn f(%p0: @arg let Probe, %p1: @ret Probe):
  b0:
    clone Probe %p0 to %p1 via <test>::std::Value<<test>::Probe>::clone#impl:a879cee3
    ret

fn std::Value<<test>::Probe>::ALIGN#impl:79916c32(%p0: @ret int):
  @c0: int = 8
  b0:
    store @c0 to %p0
    ret

fn std::Value<<test>::Probe>::SIZE#impl:99ef601e(%p0: @ret int):
  @c0: int = 8
  b0:
    store @c0 to %p0
    ret

fn std::Value<<test>::Probe>::clone#impl:a879cee3(%p0: @arg let Probe, %p1: @ret Probe):
  @c0: int = 0
  @c1: int = 100
  b0:
    %r0 = subfield @c0 from %p1
    %r1 = subfield @c0 from %p0
    %r2 = alloca int
    store @c1 to %r2
    %r3 = alloca int
    call std::Num<std::int>::from_int#impl:25eabc6b(%r2, %r3)
    call std::Num<std::int>::add#impl:7665d3ee(%r1, %r3, %r0)
    ret

fn std::Value<<test>::Probe>::drop#impl:c816a941(%p0: @arg &mut Probe, %p1: @ret ()):
  @c0: () = ()
  b0:
    store @c0 to %p1
    ret

fn std::Value<<test>::Probe>::eq#impl:938075a8(%p0: @arg let Probe, %p1: @arg let Probe, %p2: @ret bool):
  @c0: int = 0
  b0:
    %r0 = subfield @c0 from %p0
    %r1 = subfield @c0 from %p1
    call std::Value<std::int>::eq#impl:87044288(%r0, %r1, %p2)
    ret

fn std::Value<<test>::Probe>::hash#impl:d7e4d34a(%p0: @arg let Probe, %p1: @arg &mut hasher, %p2: @ret ()):
  @c0: int = 0
  b0:
    %r0 = subfield @c0 from %p0
    call std::Value<std::int>::hash#impl:bdc2934a(%r0, %p1, %p2)
    ret

fn std::Value<<test>::Probe>::to_string#impl:367ced11(%p0: @arg let Probe, %p1: @ret string):
  @c0: int = 0
  b0:
    %r0 = subfield @c0 from %p0
    call std::Value<std::int>::to_string#impl:a5db1d9f(%r0, %p1)
    ret
"#
    );
    // TODO pattern based matching
}

#[test]
fn clone_value_generic_return() {
    // Returning a generic parameter clones it through the Value dictionary.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f<T>(x: T) -> T { x }"),
        r#"fn f(%p0: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A) -> A, (&mut A) -> (), () -> int, () -> int), %p1: @arg let A, %p2: @ret A):
  b0:
    %r0 = dict_entry 3 from %p0
    clone A %p1 to %p2 via %r0
    ret
"#,
    );
}

#[test]
fn clone_value_generic_branch() {
    // A generic parameter used in both branches of an if-else clones through the Value
    // dictionary in each branch, storing directly into the shared return out-pointer.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f<T>(x: T) -> T { if true { x } else { x } }"),
        r#"fn f(%p0: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A) -> A, (&mut A) -> (), () -> int, () -> int), %p1: @arg let A, %p2: @ret A):
  @c0: bool = true
  b0:
    br b1
  b1:
    %r0 = comp_eq @c0 true
    condbr %r0, b2, b3
  b2:
    %r1 = dict_entry 3 from %p0
    clone A %p1 to %p2 via %r1
    br b4
  b3:
    %r2 = dict_entry 3 from %p0
    clone A %p1 to %p2 via %r2
    br b4
  b4:
    ret
"#,
    );
}

#[test]
fn store_local_generic_clone_dictionary() {
    // Initializing an owned mutable local from a generic parameter clones through the
    // Value dictionary into dynamically-allocated storage (alloca_dynamic via the dictionary
    // witness). The local is then passed by mutable reference without an extra copy.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn g<T>(x: &mut T) {} fn f<T>(x: T) { let mut y = x; g(y); }"),
        r#"fn f(%p0: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A) -> A, (&mut A) -> (), () -> int, () -> int), %p1: @arg let A, %p2: @ret ()):
  @c0: () = ()
  b0:
    %r0 = alloca A using %p0
    %r1 = dict_entry 3 from %p0
    clone A %p1 to %r0 via %r1
    %r2 = alloca ()
    call <test>::g(%r0, %r2)
    store @c0 to %p2
    %r3 = dict_entry 4 from %p0
    drop A %r0 via %r3
    ret

fn g(%p0: @arg &mut A, %p1: @ret ()):
  @c0: () = ()
  b0:
    store @c0 to %p1
    ret
"#,
    );
}

#[test]
fn return_local_int_move() {
    // Returning a local int variable - should move (trivial copy for int)
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f() { let x: int = 42; x }"),
        r#"fn f(%p0: @ret int):
  @c0: int = 42
  @c1: () = ()
  b0:
    %r0 = alloca int
    store @c0 to %r0
    move %r0 to %p0
    ret
"#,
    );
}

// ============================================================================
// (Re)assignment tests
// ============================================================================

#[test]
fn reassign_local_literal() {
    // Reassigning an owned int local overwrites its alloca in place; the old value
    // needs no semantic drop (Skip for int).
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f() -> int { let mut y: int = 1; y = 2; y }"),
        r#"fn f(%p0: @ret int):
  @c0: int = 1
  @c1: () = ()
  @c2: int = 2
  b0:
    %r0 = alloca int
    store @c0 to %r0
    %r1 = alloca int
    %r2 = alloca int
    store @c2 to %r2
    call std::Num<std::int>::from_int#impl:25eabc6b(%r2, %r1)
    move %r1 to %r0
    move %r0 to %p0
    ret
"#,
    );
}

#[test]
fn reassign_local_from_param() {
    // Reassigning an owned local from a by-value param is a trivial copy: load %p0,
    // store into the local's alloca.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x: int) -> int { let mut y: int = 0; y = x; y }"),
        r#"fn f(%p0: @arg let int, %p1: @ret int):
  @c0: int = 0
  @c1: () = ()
  b0:
    %r0 = alloca int
    store @c0 to %r0
    %r1 = alloca int
    memcpy %p0 to %r1
    move %r1 to %r0
    move %r0 to %p1
    ret
"#,
    );
}

#[test]
fn reassign_in_branches() {
    // Each branch writes its value directly into the same owned local's alloca.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir(
            "fn f(c: bool) -> int { let mut y: int = 0; if c { y = 1 } else { y = 2 }; y }"
        ),
        r#"fn f(%p0: @arg let bool, %p1: @ret int):
  @c0: int = 0
  @c1: () = ()
  @c2: int = 1
  @c3: int = 2
  b0:
    %r0 = alloca int
    %r1 = alloca ()
    store @c0 to %r0
    br b1
  b1:
    %r2 = comp_eq %p0 true
    condbr %r2, b2, b3
  b2:
    %r3 = alloca int
    %r4 = alloca int
    store @c2 to %r4
    call std::Num<std::int>::from_int#impl:25eabc6b(%r4, %r3)
    move %r3 to %r0
    store @c1 to %r1
    br b4
  b3:
    %r5 = alloca int
    %r6 = alloca int
    store @c3 to %r6
    call std::Num<std::int>::from_int#impl:25eabc6b(%r6, %r5)
    move %r5 to %r0
    store @c1 to %r1
    br b4
  b4:
    move %r0 to %p1
    ret
"#,
    );
}

#[test]
fn reassign_mutable_ref_param_from_local() {
    // Assigning through a `&mut` param writes into the caller's storage via the
    // incoming pointer; the source local is read with a trivial-copy load.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x: &mut int) { let y: int = 1; x = y; }"),
        r#"fn f(%p0: @arg &mut int, %p1: @ret ()):
  @c0: int = 1
  @c1: () = ()
  b0:
    %r0 = alloca int
    store @c0 to %r0
    %r1 = alloca int
    memcpy %r0 to %r1
    move %r1 to %p0
    store @c1 to %p1
    ret
"#,
    );
}

#[test]
fn reassign_array_element_from_param() {
    // Assigning into an array element resolves the element place and stores the
    // param's trivially-copied value into it.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(a: &mut [int], v: int) { a[0] = v; }"),
        r#"fn f(%p0: @arg &mut [int], %p1: @arg let int, %p2: @ret ()):
  @c0: int = 0
  @c1: () = ()
  b0:
    %r0 = alloca int
    store @c0 to %r0
    %r1 = alloca_place int
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r0, %r1) -> b1 error b2
  b1:
    %r2 = load %r1
    %r3 = alloca int
    memcpy %p1 to %r3
    move %r3 to %r2
    store @c1 to %p2
    ret
  b2:
    propagate_error
"#,
    );
}

#[test]
fn reassign_generic() {
    // Evaluate the new value (cloning `b` through `Value::clone` into a fresh temporary), then drop
    // the destination's old value through `Value::drop`, then move the temporary into the
    // destination. Mirrors the interpreter's `eval_assign` order (value, drop, store): the new value
    // is materialized before the old one is dropped, so a right-hand side that reads the destination
    // (e.g. `a = a / 2`) never observes dropped storage.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn set<A>(a: &mut A, b: A) { a = b }"),
        r#"fn set(%p0: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A) -> A, (&mut A) -> (), () -> int, () -> int), %p1: @arg &mut A, %p2: @arg let A, %p3: @ret ()):
  @c0: () = ()
  b0:
    %r0 = alloca A using %p0
    %r1 = dict_entry 3 from %p0
    clone A %p2 to %r0 via %r1
    %r2 = dict_entry 4 from %p0
    drop A %p1 via %r2
    move %r0 to %p1 using %p0
    store @c0 to %p3
    ret
"#
    )
}

// A `()`-returning function's `@ret` starts a husk, so the body must write `()` into it; a body that
// forgets is caught by the call-boundary check. These pin that a `()`-typed tail which produces no
// value itself (an assignment, a closure-env drop) still initializes `@ret`.

#[test]
fn void_body_tail_assignment_writes_ret() {
    // Body tail is a bare assignment (no trailing `;`), so the assignment is the `()`-typed tail.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn set(a: &mut int, v: int) { a = v }"),
        r#"fn set(%p0: @arg &mut int, %p1: @arg let int, %p2: @ret ()):
  @c0: () = ()
  b0:
    %r0 = alloca int
    memcpy %p1 to %r0
    move %r0 to %p0
    store @c0 to %p2
    ret
"#,
    );
    // And it runs (the caller observes the write; the boundary check passes).
    assert_val_eq!(
        session.run("fn set(a: &mut int, v: int) { a = v }\nfn driver() -> int { let mut x = 0; set(x, 5); x }\ndriver()"),
        int(5)
    );
}

#[test]
fn reassign_local_literal_overwrites_resource_free_in_place() {
    // `store` may overwrite storage that owns no resource (a scalar reassigned in place) and drops
    // nothing; only overwriting a resource-owner without a prior `drop` is a bug.
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run("fn f() -> int { let mut i = 0; i = 1; i = i + 40; i } f()"),
        int(41)
    );
}

#[test]
fn generic_match_composite_scrutinee_compares_whole_value() {
    // A tuple-pattern `match` compares the *whole* scrutinee against the *whole* pattern in one
    // `comp_eq`: the scrutinee is borrowed as a place (`%p0`, never loaded/moved) and the composite
    // pattern is carried whole as a literal (`(true, true)`). This mirrors the HIR interpreter's
    // `eval_case` (`scrutinee.to_literal_value() == pattern`, structural) — the MIR does not
    // decompose the tuple.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn g(x) -> int { match x { (true, true) => 1, _ => 2 } }"),
        r#"fn g(%p0: @arg let A, %p1: @ret int):
  @c0: int = 1
  @c1: int = 2
  b0:
    br b1
  b1:
    %r0 = comp_eq %p0 (true, true)
    condbr %r0, b2, b3
  b2:
    %r1 = alloca int
    store @c0 to %r1
    call std::Num<std::int>::from_int#impl:25eabc6b(%r1, %p1)
    br b4
  b3:
    %r2 = alloca int
    store @c1 to %r2
    call std::Num<std::int>::from_int#impl:25eabc6b(%r2, %p1)
    br b4
  b4:
    ret
"#,
    );
}

#[test]
fn generic_match_nested_composite_scrutinee_compares_whole_value() {
    // A nested tuple pattern is still one whole-value `comp_eq`: the literal `(true, (false, true))`
    // is carried whole and compared against the borrowed scrutinee place structurally (no nesting in
    // the IR — the structure lives in the literal and is compared by `LiteralValue` equality).
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn n(x) -> int { match x { (true, (false, true)) => 1, _ => 2 } }"),
        r#"fn n(%p0: @arg let A, %p1: @ret int):
  @c0: int = 1
  @c1: int = 2
  b0:
    br b1
  b1:
    %r0 = comp_eq %p0 (true, (false, true))
    condbr %r0, b2, b3
  b2:
    %r1 = alloca int
    store @c0 to %r1
    call std::Num<std::int>::from_int#impl:25eabc6b(%r1, %p1)
    br b4
  b3:
    %r2 = alloca int
    store @c1 to %r2
    call std::Num<std::int>::from_int#impl:25eabc6b(%r2, %p1)
    br b4
  b4:
    ret
"#,
    );
}

#[test]
fn generic_match_string_scrutinee_compares_borrowed_place() {
    // A `string` scrutinee is compared with the same `comp_eq` shape as any other: the scrutinee is
    // borrowed as a place (`%p0`, never moved — so it survives multiple alternatives and the arm
    // body) and compared against the literal. At run time the comparison is structural `LiteralValue`
    // equality (`comp_eq` borrows both operands and compares their `to_literal_value()`, mirroring
    // the HIR interpreter's `eval_case`), so it handles `string` — not just `int`/`bool`.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(s) -> int { match s { \"a\" => 1, _ => 2 } }"),
        r#"fn f(%p0: @arg let A, %p1: @ret int):
  @c0: int = 1
  @c1: int = 2
  b0:
    br b1
  b1:
    %r0 = comp_eq %p0 "a"
    condbr %r0, b2, b3
  b2:
    %r1 = alloca int
    store @c0 to %r1
    call std::Num<std::int>::from_int#impl:25eabc6b(%r1, %p1)
    br b4
  b3:
    %r2 = alloca int
    store @c1 to %r2
    call std::Num<std::int>::from_int#impl:25eabc6b(%r2, %p1)
    br b4
  b4:
    ret
"#,
    );
}

#[test]
fn generic_match_scrutinee_compares_borrowed_place() {
    // A `match`/`if` condition carries a `Repr<Is = U>` bound, so its scrutinee may be a bare
    // generic (`x: A`) whose run-time representation `U` is a primitive (here `int`). The scrutinee
    // is borrowed as a place (`%p0`) and compared against the literal pattern — `comp_eq` borrows it
    // non-consumingly and compares `to_literal_value()`s, mirroring the HIR interpreter's `eval_case`.
    // No `Value` dictionary is needed.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x) -> int { match x { 0 => 1, _ => 2 } }"),
        r#"fn f(%p0: @arg let A, %p1: @ret int):
  @c0: int = 1
  @c1: int = 2
  b0:
    br b1
  b1:
    %r0 = comp_eq %p0 0
    condbr %r0, b2, b3
  b2:
    %r1 = alloca int
    store @c0 to %r1
    call std::Num<std::int>::from_int#impl:25eabc6b(%r1, %p1)
    br b4
  b3:
    %r2 = alloca int
    store @c1 to %r2
    call std::Num<std::int>::from_int#impl:25eabc6b(%r2, %p1)
    br b4
  b4:
    ret
"#,
    );
}

#[test]
fn copy_int_param_to_local() {
    // Copying int parameter to a mutable local - uses trivial copy
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x: int) { let mut y = x; y = y + 1; y }"),
        r#"fn f(%p0: @arg let int, %p1: @ret int):
  @c0: () = ()
  @c1: int = 1
  b0:
    %r0 = alloca int
    memcpy %p0 to %r0
    %r1 = alloca int
    %r2 = alloca int
    store @c1 to %r2
    %r3 = alloca int
    call std::Num<std::int>::from_int#impl:25eabc6b(%r2, %r3)
    call std::Num<std::int>::add#impl:7665d3ee(%r0, %r3, %r1)
    move %r1 to %r0
    move %r0 to %p1
    ret
"#,
    );
}

#[test]
fn variants() {
    let mut session = TestSession::new();

    assert_eq_sans_flake!(
        session.emit_mir("fn f(x: Y | X(string)) { let r = x; } "),
        r#"fn f(%p0: @arg let X (string) | Y, %p1: @ret ()):
  @c0: () = ()
  b0:
    store @c0 to %p1
    ret
"#
    );
}

#[test]
fn named_subscript_read() {
    let mut session = TestSession::new();
    session.allow_experimental();
    assert_eq_sans_flake!(
        session.emit_mir(
            "subscript first(values: &mut [int]) -> int { ref mut { return values[0] } }\nfn f(a: &mut [int]) -> int { a->[first] }",
        ),
        r#"fn f(%p0: @arg &mut [int], %p1: @ret int):
  b0:
    %r0 = alloca_place int
    invoke call <test>::first::ref_mut#subscript:19d196cf(%p0, %r0) -> b1 error b2
  b1:
    %r1 = load %r0
    memcpy %r1 to %p1
    ret
  b2:
    propagate_error

fn first::ref_mut#subscript:19d196cf(%p0: @arg &mut [int], %p1: @ret int):
  @c0: int = 0
  b0:
    %r0 = alloca int
    store @c0 to %r0
    %r1 = alloca_place int
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r0, %r1) -> b1 error b2
  b1:
    %r2 = load %r1
    store %r2 to %p1
    ret
  b2:
    propagate_error
"#,
    );
}

#[test]
fn named_subscript_assign() {
    let mut session = TestSession::new();
    session.allow_experimental();
    assert_eq_sans_flake!(
        session.emit_mir(
            "subscript first(values: &mut [int]) -> int { ref mut { return values[0] } }\nfn f(a: &mut [int], v: int) { a->[first] = v }",
        ),
        r#"fn f(%p0: @arg &mut [int], %p1: @arg let int, %p2: @ret ()):
  @c0: () = ()
  b0:
    %r0 = alloca_place int
    invoke call <test>::first::ref_mut#subscript:19d196cf(%p0, %r0) -> b1 error b2
  b1:
    %r1 = load %r0
    %r2 = alloca int
    memcpy %p1 to %r2
    move %r2 to %r1
    store @c0 to %p2
    ret
  b2:
    propagate_error

fn first::ref_mut#subscript:19d196cf(%p0: @arg &mut [int], %p1: @ret int):
  @c0: int = 0
  b0:
    %r0 = alloca int
    store @c0 to %r0
    %r1 = alloca_place int
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r0, %r1) -> b1 error b2
  b1:
    %r2 = load %r1
    store %r2 to %p1
    ret
  b2:
    propagate_error
"#,
    );
}

#[test]
fn named_subscript_compound_assign() {
    let mut session = TestSession::new();
    session.allow_experimental();
    assert_eq_sans_flake!(
        session.emit_mir(
            "subscript first(values: &mut [int]) -> int { ref mut { return values[0] } }\nfn f(a: &mut [int], v: int) { a->[first] += v }",
        ),
        r#"fn f(%p0: @arg &mut [int], %p1: @arg let int, %p2: @ret ()):
  @c0: () = ()
  b0:
    %r0 = alloca_place int
    invoke call <test>::first::ref_mut#subscript:19d196cf(%p0, %r0) -> b1 error b2
  b1:
    %r1 = load %r0
    %r2 = alloca int
    call std::Num<std::int>::add#impl:7665d3ee(%r1, %p1, %r2)
    move %r2 to %r1
    store @c0 to %p2
    ret
  b2:
    propagate_error

fn first::ref_mut#subscript:19d196cf(%p0: @arg &mut [int], %p1: @ret int):
  @c0: int = 0
  b0:
    %r0 = alloca int
    store @c0 to %r0
    %r1 = alloca_place int
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r0, %r1) -> b1 error b2
  b1:
    %r2 = load %r1
    store %r2 to %p1
    ret
  b2:
    propagate_error
"#,
    );
}

#[test]
fn explicit_return_value() {
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn g(x: int) -> int { return x }"),
        r#"fn g(%p0: @arg let int, %p1: @ret int):
  b0:
    memcpy %p0 to %p1
    ret
"#,
    );
}

#[test]
fn addressor_subscript_member_returns_place() {
    let mut session = TestSession::new();
    session.allow_experimental();
    // The addressor member is emitted by the top-level `emit_mir` (subscript members are part of
    // the module). Its body returns the *place pointer* through its return out-pointer: the final
    // `store %r4 to %p1` writes the `*int` place into the `**int` slot.
    assert_eq_sans_flake!(
        session.emit_mir(
            "subscript first(values: &mut [int]) -> int { ref mut { return values[0] } }",
        ),
        r#"fn first::ref_mut#subscript:19d196cf(%p0: @arg &mut [int], %p1: @ret int):
  @c0: int = 0
  b0:
    %r0 = alloca int
    store @c0 to %r0
    %r1 = alloca_place int
    invoke call std::array_index::ref_mut#subscript:cb69b6f4(%p0, %r0, %r1) -> b1 error b2
  b1:
    %r2 = load %r1
    store %r2 to %p1
    ret
  b2:
    propagate_error
"#,
    );
}

#[test]
fn yielded_subscript_member_emitted_standalone() {
    // A scoped (`yield`) member has YieldedOnce convention and is emitted standalone as a suspendable
    // accessor: its ramp (`let mut local = slot`) runs, the `yield` exposes the place of `local`, and
    // the slide (`slot = local`) runs only when the driver resumes via `end_project`.
    let mut session = TestSession::new();
    session.allow_experimental();
    assert_eq_sans_flake!(
        session.emit_mir(
            "subscript cell(slot: &mut int) -> int { ref mut { let mut local = slot; yield local; slot = local } }",
        ),
        r#"fn cell::ref_mut#subscript:f3d0ec43(%p0: @arg &mut int, %p1: @ret int):
  @c0: () = ()
  b0:
    %r0 = alloca int
    memcpy %p0 to %r0
    yield %r0 -> b1
  b1:
    %r1 = alloca int
    memcpy %r0 to %r1
    move %r1 to %p0
    ret
"#,
    );
}

/// A `yield`-based subscript member, used by the read/assign/compound-assign golden tests below.
const CELL_SUBSCRIPT: &str = "subscript cell(slot: &mut int) -> int { ref mut { let mut local = slot; yield local; slot = local } }\n";

#[test]
fn yielded_subscript_read() {
    // A read `a->[cell]` runs the accessor to its yield with `project` (exposing the yielded place),
    // copies the value out, then `end_project` runs the slide.
    let mut session = TestSession::new();
    session.allow_experimental();
    assert_eq_sans_flake!(
        session.emit_mir(&format!(
            "{CELL_SUBSCRIPT}fn f(a: &mut int) -> int {{ a->[cell] }}"
        )),
        r#"fn cell::ref_mut#subscript:f3d0ec43(%p0: @arg &mut int, %p1: @ret int):
  @c0: () = ()
  b0:
    %r0 = alloca int
    memcpy %p0 to %r0
    yield %r0 -> b1
  b1:
    %r1 = alloca int
    memcpy %r0 to %r1
    move %r1 to %p0
    ret

fn f(%p0: @arg &mut int, %p1: @ret int):
  b0:
    %r0 = project <test>::cell::ref_mut#subscript:f3d0ec43(%p0)
    memcpy %r0 to %p1
    end_project %r0
    ret
"#,
    );
}

#[test]
fn yielded_subscript_assign() {
    // An assignment `a->[cell] = v` writes through the yielded place, then `end_project` runs the
    // slide (the accessor's write-back).
    let mut session = TestSession::new();
    session.allow_experimental();
    assert_eq_sans_flake!(
        session.emit_mir(&format!(
            "{CELL_SUBSCRIPT}fn f(a: &mut int, v: int) {{ a->[cell] = v }}"
        )),
        r#"fn cell::ref_mut#subscript:f3d0ec43(%p0: @arg &mut int, %p1: @ret int):
  @c0: () = ()
  b0:
    %r0 = alloca int
    memcpy %p0 to %r0
    yield %r0 -> b1
  b1:
    %r1 = alloca int
    memcpy %r0 to %r1
    move %r1 to %p0
    ret

fn f(%p0: @arg &mut int, %p1: @arg let int, %p2: @ret ()):
  @c0: () = ()
  b0:
    %r0 = project <test>::cell::ref_mut#subscript:f3d0ec43(%p0)
    %r1 = alloca int
    memcpy %p1 to %r1
    move %r1 to %r0
    store @c0 to %p2
    end_project %r0
    ret
"#,
    );
}

#[test]
fn yielded_subscript_compound_assign() {
    // A compound assignment `a->[cell] += v` reads and writes the single yielded place inside one
    // projection, then `end_project` runs the slide.
    let mut session = TestSession::new();
    session.allow_experimental();
    assert_eq_sans_flake!(
        session.emit_mir(
            r#"
            subscript cell(slot: &mut int) -> int {
              ref mut {
                let mut local = slot;
                yield local;
                slot = local
              }
            }
            fn f(a: &mut int, v: int) {
              a->[cell] += v
            }
            "#
        ),
        r#"fn cell::ref_mut#subscript:f3d0ec43(%p0: @arg &mut int, %p1: @ret int):
  @c0: () = ()
  b0:
    %r0 = alloca int
    memcpy %p0 to %r0
    yield %r0 -> b1
  b1:
    %r1 = alloca int
    memcpy %r0 to %r1
    move %r1 to %p0
    ret

fn f(%p0: @arg &mut int, %p1: @arg let int, %p2: @ret ()):
  @c0: () = ()
  b0:
    %r0 = project <test>::cell::ref_mut#subscript:f3d0ec43(%p0)
    %r1 = alloca int
    call std::Num<std::int>::add#impl:7665d3ee(%r0, %p1, %r1)
    move %r1 to %r0
    store @c0 to %p2
    end_project %r0
    ret
"#,
    );
}

#[test]
fn yielded_subscript_fallible_body_runs_slide_on_unwind() {
    // When the body of a scoped subscript can raise (here a fallible `/`), the write into the yielded
    // place is an `invoke`: on the error edge it diverts to a cleanup pad that runs `end_project` (the
    // accessor slide) before propagating the failure to the caller — the slide runs on the error path,
    // matching the HIR interpreter's epilogue-on-transfer.
    let mut session = TestSession::new();
    session.allow_experimental();
    assert_eq_sans_flake!(
        session.emit_mir(&format!(
            "{CELL_SUBSCRIPT}fn f(a: &mut int, v: int, w: int) {{ a->[cell] = idiv(v, w) }}"
        )),
        r#"fn cell::ref_mut#subscript:f3d0ec43(%p0: @arg &mut int, %p1: @ret int):
  @c0: () = ()
  b0:
    %r0 = alloca int
    memcpy %p0 to %r0
    yield %r0 -> b1
  b1:
    %r1 = alloca int
    memcpy %r0 to %r1
    move %r1 to %p0
    ret

fn f(%p0: @arg &mut int, %p1: @arg let int, %p2: @arg let int, %p3: @ret ()):
  @c0: () = ()
  b0:
    %r0 = project <test>::cell::ref_mut#subscript:f3d0ec43(%p0)
    %r1 = alloca int
    invoke call std::idiv(%p1, %p2, %r1) -> b1 error b2
  b1:
    move %r1 to %r0
    store @c0 to %p3
    end_project %r0
    ret
  b2:
    end_project %r0
    propagate_error
"#,
    );
}

// Dual-backend value tests for the scoped (`yield`) subscript: each runs under both the HIR and the
// MIR interpreter and asserts they agree, so the MIR `project`/`yield`/`end_project` suspend-resume
// matches the HIR interpreter's `WithYielded` drive (including the slide write-back and the error
// path).

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn yielded_subscript_read_runs() {
    let mut session = TestSession::new();
    session.allow_experimental();
    // A read returns the yielded value; the slide write-back is a no-op for the read.
    assert_val_eq!(
        session.run(&format!(
            "{CELL_SUBSCRIPT}fn read(a: &mut int) -> int {{ a->[cell] }}\nfn driver() -> int {{ let mut x = 7; read(x) }}\ndriver()"
        )),
        int(7)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn yielded_subscript_assign_runs_slide_writeback() {
    let mut session = TestSession::new();
    session.allow_experimental();
    // The assignment writes through the yielded place; the slide (`slot = local`) writes the new
    // value back, so the caller's `x` observes it.
    assert_val_eq!(
        session.run(&format!(
            "{CELL_SUBSCRIPT}fn set(a: &mut int, v: int) {{ a->[cell] = v }}\nfn driver() -> int {{ let mut x = 0; set(x, 42); x }}\ndriver()"
        )),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn yielded_subscript_compound_assign_runs_slide_writeback() {
    let mut session = TestSession::new();
    session.allow_experimental();
    // A compound assignment reads and writes the single yielded place, then the slide writes back.
    assert_val_eq!(
        session.run(&format!(
            "{CELL_SUBSCRIPT}fn bump(a: &mut int) {{ a->[cell] += 10 }}\nfn driver() -> int {{ let mut x = 5; bump(x); x }}\ndriver()"
        )),
        int(15)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn yielded_subscript_body_error_propagates() {
    let mut session = TestSession::new();
    session.allow_experimental();
    // A raise in the body unwinds out of the projection on both backends (the MIR cleanup runs the
    // slide and then propagates); the outcomes agree — a `DivisionByZero` runtime error.
    assert_eq!(
        session.fail_run(&format!(
            "{CELL_SUBSCRIPT}fn bad(a: &mut int, w: int) {{ a->[cell] = idiv(1, w) }}\nfn driver() -> int {{ let mut x = 5; bad(x, 0); x }}\ndriver()"
        )),
        SourceFailureKind::DivisionByZero,
    );
}

#[test]
fn closure_over_generic_in_concrete_caller() {
    // 2a: a generic function used first-class in a CONCRETE caller. The dictionary the generic
    // needs is statically known, so it is captured as a symbolic `dict(...)` operand on
    // `build_closure` (a leading hidden-dictionary operand; there are no value captures).
    let mut session = TestSession::new();
    let out = session.emit_mir("fn id<T>(x: T) -> T { x } fn use_id() -> int { let f = id; f(5) }");
    assert!(
        out.contains("build_closure <test>::id(dict("),
        "expected a symbolic dict operand on build_closure, got:\n{out}"
    );
}

#[test]
fn closure_forwarding_enclosing_generic_dict() {
    // 2b: a generic-bodied lambda built inside a generic function forwards that function's own
    // dictionary `@extra` parameters. `build_closure` carries the forwarded `%p` dict operands
    // (the hidden dicts and the trailing env dictionary) alongside the cloned value capture.
    let mut session = TestSession::new();
    let out = session.emit_mir("fn adder(n) { |x| x + n }");
    assert!(
        out.contains("build_closure <test>::$lambda$1(%p0, %p1, %p2, %r0, %p1)"),
        "expected forwarded %p dict operands on build_closure, got:\n{out}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn closure_over_generic_in_concrete_caller_runs() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run("fn id<T>(x: T) -> T { x } let f = id; f(5)"),
        int(5)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn closure_over_constrained_native_runs() {
    let mut session = TestSession::new();
    let source = "fn use_probe() { let f = testing::constrained_native_probe; f(0) } use_probe()";
    let out = session.emit_mir(source);
    assert!(
        out.contains("build_closure testing::constrained_native_probe(dict("),
        "expected the constrained native's dictionary to be captured, got:\n{out}"
    );
    assert_val_eq!(session.run(source), int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn closure_forwarding_enclosing_generic_dict_runs() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run("fn adder(n) { |x| x + n } let a = adder(10); a(5)"),
        int(15)
    );
}

// A tuple/record/array literal in non-tail statement position has no destination — its value is
// discarded. Lowering must still materialize it into a throwaway temporary so each element's side
// effects are emitted (it used to `panic!("ignored … construction not yet implemented")`).

#[test]
fn discarded_tuple_construction_lowers_into_throwaway_temp() {
    // The discarded `(x, x)` is built into a fresh `alloca (int, int)`; both fields are still
    // written, then `x` is returned into the out-pointer.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x: int) { (x, x); x }"),
        r#"fn f(%p0: @arg let int, %p1: @ret int):
  @c0: int = 0
  @c1: int = 1
  b0:
    %r0 = alloca (int, int)
    %r1 = subfield @c0 from %r0
    memcpy %p0 to %r1
    %r2 = subfield @c1 from %r0
    memcpy %p0 to %r2
    memcpy %p0 to %p1
    ret
"#,
    );
}

#[test]
fn discarded_record_construction_lowers_into_throwaway_temp() {
    // As for the tuple, the discarded `{ a: x, b: x }` is materialized into a fresh record temp so
    // both field writes still happen.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_mir("fn f(x: int) { { a: x, b: x }; x }"),
        r#"fn f(%p0: @arg let int, %p1: @ret int):
  @c0: int = 0
  @c1: int = 1
  b0:
    %r0 = alloca { a: int, b: int }
    %r1 = subfield @c0 from %r0
    memcpy %p0 to %r1
    %r2 = subfield @c1 from %r0
    memcpy %p0 to %r2
    memcpy %p0 to %p1
    ret
"#,
    );
}

// Each discarded literal must still *evaluate* every element, so a side effect inside an element
// (here a counter mutation) is observable after the discarded construction.

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn discarded_tuple_evaluates_elements() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run("fn f() { let mut c = 0; ({ c = c + 1; c }, { c = c + 1; c }); c } f()"),
        int(2)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn discarded_array_evaluates_elements() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run("fn f() { let mut c = 0; [{ c = c + 1; c }, { c = c + 1; c }]; c } f()"),
        int(2)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn discarded_record_evaluates_elements() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session
            .run("fn f() { let mut c = 0; { a: { c = c + 1; c }, b: { c = c + 1; c } }; c } f()"),
        int(2)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assign_aggregate_swap_matches_hir() {
    // An assignment whose right-hand side reads the destination it overwrites must agree across
    // both backends. Every aggregate destination carries a drop obligation, so lowering routes the
    // right-hand side through a fresh temporary before moving it into the destination; this pins
    // that the move-not-alias path is correct for tuples, records, arrays, variants, and the
    // scalar-call (no-drop) case. The HIR/MIR parity check inside `run` is the real assertion.
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run("fn f() { let mut a = (true, false); a = (a.1, a.0); a } f()"),
        expected_tuple([bool(false), bool(true)])
    );
    assert_val_eq!(
        session.run("fn f() { let mut a = {x: 1, y: 2}; a = {x: a.y, y: a.x}; (a.x, a.y) } f()"),
        expected_tuple([int(2), int(1)])
    );
    assert_val_eq!(
        session.run("fn f() { let mut a = [1, 2]; a = [a[1], a[0]]; a } f()"),
        session.run("[2, 1]")
    );
    assert_val_eq!(
        session.run("fn f() { let mut a = (1, 2); a = (a.0 + a.1, a.0); a } f()"),
        expected_tuple([int(3), int(1)])
    );
}
