use test_log::test;

use ferlium::{format::FormatWith, module::ShowModuleWithOptions};

use crate::harness::TestSession;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

/// Print the elaborated HIR of `src` for parameter-passing experiments.
/// Run with: `cargo nextest run hir_param --no-capture`
fn print_param_hir(label: &str, src: &str) {
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
    assert_eq!(
        session.emit_ssa("fn t(x:int) {x}"),
        r#"u!("t")
fn t(%p0: @arg int):
  0:
    %r0 = ret %p0
"#,
    );
}

#[test]
fn call_functions() {
    let mut session = TestSession::new();

    assert_eq!(
        session.emit_ssa("fn a0(x:int) {x + 1}"),
        r#"u!("a0")
fn a0(%p0: @arg int):
  0:
    %r0 = call std::Num<0-5>::from_int(i32 1)
    %r1 = call std::Num<0-5>::add(%p0, %r0)
    %r2 = ret %r1
"#
    );

    assert_eq!(
        session.emit_ssa("fn a0(x: int) { let y: int = 2 * x; y }"),
        r#"u!("a0")
fn a0(%p0: @arg int):
  0:
    %r0 = alloca int
    %r1 = call std::Num<0-5>::from_int(i32 2)
    %r2 = call std::Num<0-5>::mul(%r1, %p0)
    %r3 = store %r2 to %r0
    %r4 = load %r0
    %r5 = ret %r4
"#
    );
}

#[test]
fn match_case_functions() {
    let mut session = TestSession::new();

    assert_eq!(
        session.emit_ssa("fn a0(x:int) {if true {x} else {2}}"),
        r#"u!("a0")
fn a0(%p0: @arg int):
  0:
    %r0 = alloca int
    %r1 = br 1
  1:
    %r2 = comp_eq i1 1 i1 1
    %r3 = condbr %r2, %b2, &b3
  2:
    %r4 = store %p0 to %r0
    %r5 = br 4
  3:
    %r6 = call std::Num<0-5>::from_int(i32 2)
    %r7 = store %r6 to %r0
    %r8 = br 4
  4:
    %r9 = load %r0
    %r10 = ret %r9
"#
    );

    assert_eq!(
        session.emit_ssa("fn a0(x:int) {match x { 0 => x, 1 => x - 1, _ => -1 }}"),
        r#"u!("a0")
fn a0(%p0: @arg int):
  0:
    %r0 = alloca int
    %r1 = br 1
  1:
    %r2 = comp_eq %p0 i32 0
    %r3 = condbr %r2, %b2, &b3
  2:
    %r4 = store %p0 to %r0
    %r5 = br 6
  3:
    %r6 = comp_eq %p0 i32 1
    %r7 = condbr %r6, %b4, &b5
  4:
    %r8 = call std::Num<0-5>::from_int(i32 1)
    %r9 = call std::Num<0-5>::sub(%p0, %r8)
    %r10 = store %r9 to %r0
    %r11 = br 6
  5:
    %r12 = call std::Num<0-5>::from_int(i32 1)
    %r13 = call std::Num<0-5>::neg(%r12)
    %r14 = store %r13 to %r0
    %r15 = br 6
  6:
    %r16 = load %r0
    %r17 = ret %r16
"#
    );
}
//
// #[test]
// fn generic_functions() {
//     let mut sessions = TestSession::new();
//
//     print_param_hir("generic", "fn a0(x) { x < 2 }");
//
//     assert_eq!(
//         sessions.emit_ssa("fn a0(x) { x < 2 }"),
//         r#"u!("a0")
// fn a0(%p0: @extra ((A, A) -> Ordering,), %p1: @extra ((A, A) -> A, (A, A) -> A, (A, A) -> A, (A) -> A, (A) -> A, (A) -> A, (int) -> A), %p2: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A, &mut A) -> (), (&mut A) -> (), int, int), %p3: @arg A):
//   0:
//     %r0 = project 6 from %p1
//     %r1 = call %r0(i32 2)
//     %r2 = call std::lt(%p0, %p3, %r1)
//     %r3 = ret %r2
// "#
//     )
// }

#[test]
fn user_function_call() {
    let mut sessions = TestSession::new();

    assert_eq!(
        sessions.emit_ssa("fn a0(x: int) {a0(x)}"),
        r#"u!("a0")
fn a0(%p0: @arg int):
  0:
    %r0 = call <test>::a0(%p0)
    %r1 = ret %r0
"#
    )
}

/// Scratch test for experimenting with SSA lowering.
/// Edit the source below and run `cargo nextest run experiment --no-capture`
/// to print the generated SSA. (No assertion, so it never fails.)
// #[test]
// fn experiment() {
//     let mut session = TestSession::new();
//
//     let src = "fn add(a, b) {
//       let k = loop {
//         break a + 3;
//       };
//
//       k
//     }
//     ";
//
//     // Print the HIR (with details, like `--print-std-full`).
//     let module_id = session.compile(src).module_id;
//     let module = session.session().expect_fresh_module(module_id);
//     let hir = module
//         .format_with(&ShowModuleWithOptions::new(
//             session.session().modules(),
//             true,
//             false,
//         ))
//         .to_string();
//
//     let ssa = session.emit_ssa(src);
//     println!("\n=== source ===\n{src}\n=== hir ===\n{hir}\n=== ssa ===\n{ssa}");
// }

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

    // let ssa = session.emit_ssa(src);
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

    // let ssa = session.emit_ssa(src);
    println!("\n=== source ===\n{src}\n=== hir ===\n{hir}");
}

#[test]
fn factorial() {
    let mut sessions = TestSession::new();

    assert_eq!(
        sessions.emit_ssa("fn factorial(x: int) {if x > 1 {x * factorial(x - 1)} else {1}}"),
        r#"u!("factorial")
fn factorial(%p0: @arg int):
  0:
    %r0 = call std::Num<0-5>::from_int(i32 1)
    %r1 = call std::gt((std::Ord<0-5>::cmp), %p0, %r0)
    %r2 = alloca int
    %r3 = br 1
  1:
    %r4 = comp_eq %r1 i1 1
    %r5 = condbr %r4, %b2, &b3
  2:
    %r6 = call std::Num<0-5>::from_int(i32 1)
    %r7 = call std::Num<0-5>::sub(%p0, %r6)
    %r8 = call <test>::factorial(%r7)
    %r9 = call std::Num<0-5>::mul(%p0, %r8)
    %r10 = store %r9 to %r2
    %r11 = br 4
  3:
    %r12 = call std::Num<0-5>::from_int(i32 1)
    %r13 = store %r12 to %r2
    %r14 = br 4
  4:
    %r15 = load %r2
    %r16 = ret %r15
"#
    );
}

#[test]
fn hir_param_trivial_copy_value() {
    // 1) Concrete TrivialCopy param, read-only use.
    print_param_hir("trivial_copy_value", "fn f(x: int) { x }");
}

#[test]
fn hir_param_trivial_copy_passed_to_call() {
    // 2) How a TrivialCopy param is passed into another call.
    print_param_hir(
        "trivial_copy_passed_to_call",
        "fn f(x: int) { x + 1 } fn g(x: int) { f(x) }",
    );
}

#[test]
fn hir_param_mut_local_copy() {
    // 3a) `mut x` param = mutable LOCAL COPY; caller is NOT affected (value semantics).
    //     Syntax: `mut` precedes the name (Rust-style), optionally with a type.
    print_param_hir(
        "mut_local_copy",
        "fn add_one(mut x: int) -> int { x = x + 1; x }",
    );
}

#[test]
fn hir_param_inout_ref() {
    // 3b) Un-annotated param assigned in body -> inferred in/out MutableRef; caller IS affected.
    print_param_hir(
        "inout_ref",
        "fn set_1(a) { a = 1 } fn caller() { let mut x = 0; set_1(x); x }",
    );
}

#[test]
fn hir_param_non_trivial_shared_ref() {
    // 4) Non-TrivialCopy concrete param (string) returned -> SharedRef + take/clone.
    print_param_hir("non_trivial_shared_ref", "fn f(s: string) { s }");
}

#[test]
fn hir_param_generic_dictionary() {
    // 5) Generic param -> shared-ref passing + hidden dictionary extra params.
    print_param_hir("generic_dictionary", "fn f(x) { x < 2 }");
}

#[test]
fn hir_param_owned_let_from_param() {
    // 6) `let mut` initialized from a param -> clone into owned local storage.
    print_param_hir(
        "owned_let_from_param",
        "fn f(x: int) { let mut y = x; y = y + 1; y }",
    );
}

#[test]
fn hir_param_tuple_project() {
    // 7) Tuple param + projection -> Project, clone-out.
    print_param_hir("tuple_project", "fn f(p: (int, bool)) { p.0 }");
}

#[test]
fn hir_param_record_field() {
    // 8) Generic record param + field access -> ProjectAt / LoadFieldIndex.
    print_param_hir("record_field", "fn f(r) { r.x }");
}

#[test]
fn hir_param_array_mutation() {
    // 9) Array param mutated through index places -> Assign into projection, MutableRef.
    print_param_hir(
        "array_mutation",
        "fn swap(a, i, j) { let t = a[i]; a[i] = a[j]; a[j] = t }",
    );
}

#[test]
fn hir_param_higher_order() {
    // 10) Function-typed param applied -> Apply + closure/function passing.
    print_param_hir("higher_order", "fn apply_fn(f, x) { f(x) }");
}

#[test]
fn hir_param_variant_match() {
    // 11) Variant param matched -> ExtractTag / Case, with a fallback param.
    print_param_hir(
        "variant_match",
        "fn unwrap_or(o, d) { match o { Some(x) => x, _ => d } }",
    );
}

#[test]
fn hir_cf_early_return() {
    // 12) Early return between two owned (string) locals: cleanup obligations vs moved-out return.
    print_param_hir(
        "cf_early_return",
        "fn f(c: bool) -> string { let s = \"hello\"; if c { return s }; let t = \"world\"; t }",
    );
}

#[test]
fn hir_cf_break() {
    // 13) `break` out of a loop with an owned local in the body: where does cleanup attach?
    print_param_hir(
        "cf_break",
        "fn f() -> int { let mut total = 0; for x in [10, 20, 30] { let s = \"x\"; if x == 20 { break }; total = total + x }; total }",
    );
}

#[test]
fn hir_cf_nested_return() {
    // 14) `return` from a nested block: do enclosing blocks each carry their own cleanup list?
    print_param_hir(
        "cf_nested_return",
        "fn f(c: bool) -> string { let s = \"a\"; { let t = \"b\"; if c { return s } }; \"\" }",
    );
}

#[test]
fn hir_place_result_returned() {
    // 15) Returning an indexed element: place-result must be cloned to a value (MVS rule).
    print_param_hir("place_result_returned", "fn first(a) { a[0] }");
}

#[test]
fn hir_string_clone_vs_drop() {
    // 16) Same `string` local cloned (let t = s) AND dropped (end of scope): are clone and drop
    //     classifications consistent? (clone=Value::clone but drop=Skip would be an anomaly.)
    print_param_hir(
        "string_clone_vs_drop",
        "fn f(s: string) -> int { let t = s; 0 }",
    );
}

#[test]
fn hir_string_owned_snapshot() {
    // 17) `let mut t = s` forces an OWNED snapshot of a string -> clone on init, drop at scope end.
    //     This puts clone and drop of the SAME string local side by side.
    print_param_hir(
        "string_owned_snapshot",
        "fn f(s: string) -> int { let mut t = s; 0 }",
    );
}

#[test]
fn hir_string_literal_vs_cloned() {
    // 18) Two owned `string` locals in one fn: `a` from a literal, `b` cloned from a place.
    //     If `a` drops as Skip but `b` drops as Static, drop disposition depends on PROVENANCE,
    //     not just on the `string` type.
    print_param_hir(
        "string_literal_vs_cloned",
        "fn f(s: string) -> int { let a = \"lit\"; let mut b = s; 0 }",
    );
}

// ============================================================================
// Iteration 1 — basic argument passing (place-based SSA spec).
//
// Scope (locked, Decision 4): scalars + calls only. NO strings, NO arrays.
//
// Slot rule (locked, Decision 1 Option A): allocation follows `LocalStorage`:
//   - `Owned` local      -> `alloca`; place is the alloca; reads `load` it.
//   - `NonOwning` by-value param (`TrivialCopy`) -> no alloca, no seed;
//        the local's rvalue is `%pN` directly (trivial-copy clone == same reg).
//   - `NonOwning` by-ref param (`MutableRef`/`SharedRef`) -> no alloca;
//        place is the incoming pointer `%pN`; rvalue is `load %pN`.
//
// Consequence: read-only by-value scalar params stay as `%pN`, so the existing
// goldens already encode the by-value matrix:
//   - by-value identity / return : `simple_functions`      (fn t(x:int){x})
//   - by-value into arithmetic   : `call_functions`        (fn a0(x:int){x+1})
//   - by-value into user call    : `user_function_call`    (fn a0(x:int){a0(x)})
// The tests below cover the NEW coverage: multi-param and `Owned` locals
// (`mut` copy, `let mut` + move-return). They are the iteration-1 target and
// will be RED until `emit_ssa_fn` is rebuilt.
// ============================================================================

#[test]
fn hir_iter1_mutable_ref_bool() {
    // Concrete (non-generic) &mut param -> MutableRef passing with NO dictionaries.
    print_param_hir(
        "iter1_mutable_ref_bool",
        "fn setf(a) { a = false } fn caller() { let mut b = true; setf(b); b }",
    );
}

#[test]
fn iter1_multi_param_value() {
    // Two by-value (TrivialCopy) params, both read -> bare %p0/%p1, no allocas.
    let mut session = TestSession::new();
    assert_eq!(
        session.emit_ssa("fn f(x: int, y: int) { x + y }"),
        r#"u!("f")
fn f(%p0: @arg int, %p1: @arg int):
  0:
    %r0 = call std::Num<0-5>::add(%p0, %p1)
    %r1 = ret %r0
"#,
    );
}

#[test]
fn iter1_mut_local_copy() {
    // `mut x` = mutable LOCAL COPY (Owned, slot 1) seeded from the by-value param
    // (%p0). The copy gets an `alloca`; the param itself stays `%p0`.
    // Caller is NOT affected (value semantics).
    let mut session = TestSession::new();
    assert_eq!(
        session.emit_ssa("fn add_one(mut x: int) -> int { x = x + 1; x }"),
        r#"u!("add_one")
fn add_one(%p0: @arg int):
  0:
    %r0 = alloca int
    %r1 = store %p0 to %r0
    %r2 = load %r0
    %r3 = call std::Num<0-5>::from_int(i32 1)
    %r4 = call std::Num<0-5>::add(%r2, %r3)
    %r5 = store %r4 to %r0
    %r6 = load %r0
    %r7 = ret %r6
"#,
    );
}

#[test]
fn iter1_let_mut_move_return() {
    // `let mut y = x` -> Owned local (alloca) initialized by a trivial-copy clone
    // of the by-value param; tail `y` is a `TakeLocalValue(MoveOwned)` -> load + no
    // drop (drop is Skip for int anyway).
    let mut session = TestSession::new();
    assert_eq!(
        session.emit_ssa("fn f(x: int) { let mut y = x; y = y + 1; y }"),
        r#"u!("f")
fn f(%p0: @arg int):
  0:
    %r0 = alloca int
    %r1 = store %p0 to %r0
    %r2 = load %r0
    %r3 = call std::Num<0-5>::from_int(i32 1)
    %r4 = call std::Num<0-5>::add(%r2, %r3)
    %r5 = store %r4 to %r0
    %r6 = load %r0
    %r7 = ret %r6
"#,
    );
}

#[test]
fn iter1_apply() {
    let mut session = TestSession::new();
    assert_eq!(
        session.emit_ssa("fn f(x: int) { f(x) }"),
        r#"u!("f")
fn f(%p0: @arg int):
  0:
    %r0 = call <test>::f(%p0)
    %r1 = ret %r0
"#,
    );
}
#[test]
fn mutable_reference_parameter() {
    let mut session = TestSession::new();
    assert_eq!(
        session.emit_ssa("fn f(x: &mut int) { x = 2; }"),
        r#"u!("f")
fn f(%p0: @arg &mut int):
  0:
    %r0 = call std::Num<0-5>::from_int(i32 2)
    %r1 = store %r0 to %p0
    %r2 = ret ()
"#,
    );
}
