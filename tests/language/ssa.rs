use test_log::test;

use ferlium::{format::FormatWith, module::ShowModuleWithOptions};

use crate::harness::{TestSession, bool, expected_tuple, int};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

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
        session.emit_ssa("fn t(x: int) {x}"),
        r#"fn t(%p0: @arg int, %p1: @ret int):
  0:
    %r0 = memcpy %p0 to %p1
    %r1 = ret
"#,
    );
}

#[test]
fn call_functions() {
    let mut session = TestSession::new();

    assert_eq_sans_flake!(
        session.emit_ssa("fn a0(x: int) { x + 1 }"),
        r#"fn a0(%p0: @arg int, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = alloca int
    %r2 = store int 1 to %r1
    %r3 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r1, %r0)
    %r4 = call std::std::Num<std::int>::add#impl:7665d3ee(%p0, %r0, %p1)
    %r5 = ret
"#
    );

    assert_eq_sans_flake!(
        session.emit_ssa("fn a0(x: int) { let y: int = 2 * x; y }"),
        r#"fn a0(%p0: @arg int, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = alloca int
    %r2 = alloca int
    %r3 = store int 2 to %r2
    %r4 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r2, %r0)
    %r5 = call std::std::Num<std::int>::mul#impl:a3604103(%r0, %p0, %r1)
    %r6 = memcpy %r1 to %p1
    %r7 = ret
"#
    );
}

#[test]
fn match_case_functions() {
    let mut session = TestSession::new();

    assert_eq_sans_flake!(
        session.emit_ssa("fn a0(x:int) {if true {x} else {2}}"),
        r#"fn a0(%p0: @arg int, %p1: @ret int):
  0:
    %r0 = br 1
  1:
    %r1 = comp_eq i1 1 i1 1
    %r2 = condbr %r1, %b2, &b3
  2:
    %r3 = memcpy %p0 to %p1
    %r4 = br 4
  3:
    %r5 = alloca int
    %r6 = store int 2 to %r5
    %r7 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r5, %p1)
    %r8 = br 4
  4:
    %r9 = ret
"#
    );

    assert_eq_sans_flake!(
        session.emit_ssa("fn a0(x:int) {match x { 0 => x, 1 => x - 1, _ => -1 }}"),
        r#"fn a0(%p0: @arg int, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = alloca int
    %r2 = br 1
  1:
    %r3 = comp_eq %p0 int 0
    %r4 = condbr %r3, %b2, &b3
  2:
    %r5 = memcpy %p0 to %p1
    %r6 = br 6
  3:
    %r7 = comp_eq %p0 int 1
    %r8 = condbr %r7, %b4, &b5
  4:
    %r9 = alloca int
    %r10 = store int 1 to %r9
    %r11 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r9, %r1)
    %r12 = call std::std::Num<std::int>::sub#impl:6eee9827(%p0, %r1, %p1)
    %r13 = br 6
  5:
    %r14 = alloca int
    %r15 = store int 1 to %r14
    %r16 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r14, %r0)
    %r17 = call std::std::Num<std::int>::neg#impl:6b873453(%r0, %p1)
    %r18 = br 6
  6:
    %r19 = ret
"#
    );
}

#[test]
fn user_function_call() {
    let mut sessions = TestSession::new();

    assert_eq_sans_flake!(
        sessions.emit_ssa("fn a0(x: int) { a0(x) }"),
        r#"fn a0(%p0: @arg int, %p1: @ret never):
  0:
    %r0 = call <test>::a0(%p0, %p1)
    %r1 = ret
"#
    )
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

    assert_eq_sans_flake!(
        sessions.emit_ssa("fn factorial(x: int) {if x > 1 {x * factorial(x - 1)} else {1}}"),
        r#"fn factorial(%p0: @arg int, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = alloca int
    %r2 = alloca int
    %r3 = alloca bool
    %r4 = alloca int
    %r5 = store int 1 to %r4
    %r6 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r4, %r0)
    %r7 = call std::gt(dict(m<...>:i20), %p0, %r0, %r3)
    %r8 = br 1
  1:
    %r9 = comp_eq %r3 i1 1
    %r10 = condbr %r9, %b2, &b3
  2:
    %r11 = alloca int
    %r12 = alloca int
    %r13 = store int 1 to %r12
    %r14 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r12, %r1)
    %r15 = call std::std::Num<std::int>::sub#impl:6eee9827(%p0, %r1, %r11)
    %r16 = call <test>::factorial(%r11, %r2)
    %r17 = call std::std::Num<std::int>::mul#impl:a3604103(%p0, %r2, %p1)
    %r18 = br 4
  3:
    %r19 = alloca int
    %r20 = store int 1 to %r19
    %r21 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r19, %p1)
    %r22 = br 4
  4:
    %r23 = ret
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
        session.emit_ssa("fn f(a: [int]) -> int { let x = if true { a[6] } else { a[4] }; x }"),
        r#"fn f(%p0: @arg & [int], %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = br 1
  1:
    %r2 = comp_eq i1 1 i1 1
    %r3 = condbr %r2, %b2, &b3
  2:
    %r4 = alloca int
    %r5 = store int 6 to %r4
    %r6 = alloca_place int
    %r7 = call std::array_index(%p0, %r4, %r6)
    %r8 = load %r6
    %r9 = memcpy %r8 to %r0
    %r10 = br 4
  3:
    %r11 = alloca int
    %r12 = store int 4 to %r11
    %r13 = alloca_place int
    %r14 = call std::array_index(%p0, %r11, %r13)
    %r15 = load %r13
    %r16 = memcpy %r15 to %r0
    %r17 = br 4
  4:
    %r18 = memcpy %r0 to %p1
    %r19 = ret
"#,
    );
}

#[test]
fn iter1_multi_param_value() {
    // Two by-value (TrivialCopy) params, both read -> bare %p0/%p1, no allocas.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(x: int, y: int) { x + y }"),
        r#"fn f(%p0: @arg int, %p1: @arg int, %p2: @ret int):
  0:
    %r0 = call std::std::Num<std::int>::add#impl:7665d3ee(%p0, %p1, %p2)
    %r1 = ret
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
        session.emit_ssa("fn add_one(mut x: int) -> int { x = x + 1; x }"),
        r#"fn add_one(%p0: @arg int, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = alloca int
    %r2 = memcpy %p0 to %r0
    %r3 = alloca int
    %r4 = store int 1 to %r3
    %r5 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r3, %r1)
    %r6 = call std::std::Num<std::int>::add#impl:7665d3ee(%r0, %r1, %r0)
    %r7 = memcpy %r0 to %p1
    %r8 = ret
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
        session.emit_ssa("fn f(x: int) { let mut y = x; y = y + 1; y }"),
        r#"fn f(%p0: @arg int, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = alloca int
    %r2 = memcpy %p0 to %r0
    %r3 = alloca int
    %r4 = store int 1 to %r3
    %r5 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r3, %r1)
    %r6 = call std::std::Num<std::int>::add#impl:7665d3ee(%r0, %r1, %r0)
    %r7 = memcpy %r0 to %p1
    %r8 = ret
"#,
    );
}

#[test]
fn array_index_read() {
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn r(a: [bool]) -> int { if a[0] { 1 } else { 2 } }"),
        r#"fn r(%p0: @arg & [bool], %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = store int 0 to %r0
    %r2 = alloca_place bool
    %r3 = call std::array_index(%p0, %r0, %r2)
    %r4 = load %r2
    %r5 = br 1
  1:
    %r6 = comp_eq %r4 i1 1
    %r7 = condbr %r6, %b2, &b3
  2:
    %r8 = alloca int
    %r9 = store int 1 to %r8
    %r10 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r8, %p1)
    %r11 = br 4
  3:
    %r12 = alloca int
    %r13 = store int 2 to %r12
    %r14 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r12, %p1)
    %r15 = br 4
  4:
    %r16 = ret
"#,
    );
}

#[test]
fn array_index_assign() {
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn s(a: &mut [bool]) { a[1] = true; }"),
        r#"fn s(%p0: @arg &mut [bool], %p1: @ret ()):
  0:
    %r0 = alloca int
    %r1 = store int 1 to %r0
    %r2 = alloca_place bool
    %r3 = call std::array_index(%p0, %r0, %r2)
    %r4 = load %r2
    %r5 = store i1 1 to %r4
    %r6 = store () to %p1
    %r7 = ret
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
        session.emit_ssa("fn first(a: [int]) -> int { a[0] }"),
        r#"fn first(%p0: @arg & [int], %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = store int 0 to %r0
    %r2 = alloca_place int
    %r3 = call std::array_index(%p0, %r0, %r2)
    %r4 = load %r2
    %r5 = memcpy %r4 to %p1
    %r6 = ret
"#,
    );
}

#[test]
fn place_call_into_owned_local() {
    // A place-returning call initializing an owned (`let mut`) local copies the element value
    // into the local's alloca; the local must hold the value, not the element address.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(a: [int]) -> int { let mut x = a[0]; x = x + 1; x }"),
        r#"fn f(%p0: @arg & [int], %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = alloca int
    %r2 = alloca int
    %r3 = store int 0 to %r2
    %r4 = alloca_place int
    %r5 = call std::array_index(%p0, %r2, %r4)
    %r6 = load %r4
    %r7 = memcpy %r6 to %r0
    %r8 = alloca int
    %r9 = store int 1 to %r8
    %r10 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r8, %r1)
    %r11 = call std::std::Num<std::int>::add#impl:7665d3ee(%r0, %r1, %r0)
    %r12 = memcpy %r0 to %p1
    %r13 = ret
"#,
    );
}

#[test]
fn place_call_discarded() {
    // A discarded place-returning call still lowers (for its effects),
    // writing the place into a throwaway `alloca_place`.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(a: [int]) { a[0]; }"),
        r#"fn f(%p0: @arg & [int], %p1: @ret ()):
  0:
    %r0 = alloca int
    %r1 = store int 0 to %r0
    %r2 = alloca_place int
    %r3 = call std::array_index(%p0, %r0, %r2)
    %r4 = load %r2
    %r5 = store () to %p1
    %r6 = ret
"#,
    );
}

#[test]
fn nested_place_call() {
    // A place-returning call whose base is itself a place-returning call chains the loaded
    // place pointers.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(a: [[int]]) -> int { a[0][1] }"),
        r#"fn f(%p0: @arg & [[int]], %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = store int 0 to %r0
    %r2 = alloca_place [int]
    %r3 = call std::array_index(%p0, %r0, %r2)
    %r4 = load %r2
    %r5 = alloca int
    %r6 = store int 1 to %r5
    %r7 = alloca_place int
    %r8 = call std::array_index(%r4, %r5, %r7)
    %r9 = load %r7
    %r10 = memcpy %r9 to %p1
    %r11 = ret
"#,
    );
}

#[test]
fn place_call_as_shared_ref_argument() {
    // A place-returning call passed as a shared-reference argument forwards the loaded place
    // pointer directly, with no copy.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn g(s: [int]) { } fn f(a: [[int]]) { g(a[0]) }"),
        r#"fn f(%p0: @arg & [[int]], %p1: @ret ()):
  0:
    %r0 = alloca int
    %r1 = store int 0 to %r0
    %r2 = alloca_place [int]
    %r3 = call std::array_index(%p0, %r0, %r2)
    %r4 = load %r2
    %r5 = call <test>::g(%r4, %p1)
    %r6 = ret

fn g(%p0: @arg & [int], %p1: @ret ()):
  0:
    %r0 = store () to %p1
    %r1 = ret
"#,
    );
}

#[test]
fn place_call_as_mutable_ref_argument() {
    // A place-returning call passed as a mutable-reference argument forwards the loaded place
    // pointer directly, with no copy.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn g(s: &mut [int]) { } fn f(a: &mut [[int]]) { g(a[0]) }"),
        r#"fn f(%p0: @arg &mut [[int]], %p1: @ret ()):
  0:
    %r0 = alloca int
    %r1 = store int 0 to %r0
    %r2 = alloca_place [int]
    %r3 = call std::array_index(%p0, %r0, %r2)
    %r4 = load %r2
    %r5 = call <test>::g(%r4, %p1)
    %r6 = ret

fn g(%p0: @arg &mut [int], %p1: @ret ()):
  0:
    %r0 = store () to %p1
    %r1 = ret
"#,
    );
}

#[test]
fn projection_of_place_call() {
    // A projection rooted in a place-returning call projects out of the loaded place pointer.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(a: [(int, bool)]) -> bool { a[0].1 }"),
        r#"fn f(%p0: @arg & [(int, bool)], %p1: @ret bool):
  0:
    %r0 = alloca int
    %r1 = store int 0 to %r0
    %r2 = alloca_place (int, bool)
    %r3 = call std::array_index(%p0, %r0, %r2)
    %r4 = load %r2
    %r5 = subfield int 1 from %r4
    %r6 = memcpy %r5 to %p1
    %r7 = ret
"#,
    );
}

#[test]
fn place_call_value_in_branches() {
    // Each branch resolves its own place and copies the value into the shared destination.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(a: [int], c: bool) -> int { if c { a[0] } else { a[1] } }"),
        r#"fn f(%p0: @arg & [int], %p1: @arg bool, %p2: @ret int):
  0:
    %r0 = br 1
  1:
    %r1 = comp_eq %p1 i1 1
    %r2 = condbr %r1, %b2, &b3
  2:
    %r3 = alloca int
    %r4 = store int 0 to %r3
    %r5 = alloca_place int
    %r6 = call std::array_index(%p0, %r3, %r5)
    %r7 = load %r5
    %r8 = memcpy %r7 to %p2
    %r9 = br 4
  3:
    %r10 = alloca int
    %r11 = store int 1 to %r10
    %r12 = alloca_place int
    %r13 = call std::array_index(%p0, %r10, %r12)
    %r14 = load %r12
    %r15 = memcpy %r14 to %p2
    %r16 = br 4
  4:
    %r17 = ret
"#,
    );
}

#[test]
fn place_call_into_alias_local() {
    // `let x = a[0]` makes `x` a `NonOwning` alias local: the local is rebound to the place
    // denoted by its initializer, with no store; the read goes through the alias.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(a: [int]) -> int { let x = a[0]; x }"),
        r#"fn f(%p0: @arg & [int], %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = store int 0 to %r0
    %r2 = alloca_place int
    %r3 = call std::array_index(%p0, %r0, %r2)
    %r4 = load %r2
    %r5 = memcpy %r4 to %p1
    %r6 = ret
"#,
    );
}

#[test]
fn iter1_apply() {
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(x: int) { f(x) }"),
        r#"fn f(%p0: @arg int, %p1: @ret never):
  0:
    %r0 = call <test>::f(%p0, %p1)
    %r1 = ret
"#,
    );
}
#[test]
fn shared_ref_param_non_trivial() {
    // A concrete non-`TrivialCopy` param (`string`) is conveyed by shared reference: the parameter
    // is a place (`@arg &`), not a by-value register.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(s: string) { }"),
        r#"fn f(%p0: @arg & string, %p1: @ret ()):
  0:
    %r0 = store () to %p1
    %r1 = ret
"#,
    );
}

#[test]
fn shared_ref_param_generic() {
    // A generic param is conveyed by shared reference regardless of any later concrete
    // instantiation, giving the function one stable parameter convention.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(x) { }"),
        r#"fn f(%p0: @arg & A, %p1: @ret ()):
  0:
    %r0 = store () to %p1
    %r1 = ret
"#,
    );
}

#[test]
fn shared_ref_argument_passes_place() {
    // Passing a shared-reference argument that already denotes a place forwards the incoming
    // pointer directly, with no copy and no materialized temporary.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn u(s: string) { } fn caller(s: string) { u(s) }"),
        r#"fn caller(%p0: @arg & string, %p1: @ret ()):
  0:
    %r0 = call <test>::u(%p0, %p1)
    %r1 = ret

fn u(%p0: @arg & string, %p1: @ret ()):
  0:
    %r0 = store () to %p1
    %r1 = ret
"#,
    );
}

#[test]
fn call_trivial_copy_argument_passes_value_recursive() {
    // A `TrivialCopy` argument is passed by value.
    // The extra store and load are caused by the owned local emission.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa(
            r#"
            fn f(a: int) {
                let n = 1;
                f(n)
            }
        "#
        ),
        r#"fn f(%p0: @arg int, %p1: @ret never):
  0:
    %r0 = alloca int
    %r1 = alloca int
    %r2 = store int 1 to %r1
    %r3 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r1, %r0)
    %r4 = call <test>::f(%r0, %p1)
    %r5 = ret
"#,
    );
}

#[test]
fn return_value_is_trivially_passed() {
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(a: int) { f(a) }"),
        r#"fn f(%p0: @arg int, %p1: @ret never):
  0:
    %r0 = call <test>::f(%p0, %p1)
    %r1 = ret
"#,
    );
}

#[test]
fn call_trivial_copy_argument_passes_value() {
    // A `TrivialCopy` argument is conveyed by value: the by-value parameter register is forwarded
    // directly to the call.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(a: int) { f(a) }"),
        r#"fn f(%p0: @arg int, %p1: @ret never):
  0:
    %r0 = call <test>::f(%p0, %p1)
    %r1 = ret
"#,
    );
}

#[test]
fn call_mutable_reference_argument_passes_owned_local_place() {
    // A `&mut` argument backed by an owned local forwards the local's `alloca` place so the callee
    // mutates the caller's storage.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa(
            r#"
        fn callee(m: &mut int) { }
        fn caller() {
            let mut m = 0;
            callee(m)
        }
        "#
        ),
        r#"fn callee(%p0: @arg &mut int, %p1: @ret ()):
  0:
    %r0 = store () to %p1
    %r1 = ret

fn caller(%p0: @ret ()):
  0:
    %r0 = alloca int
    %r1 = alloca int
    %r2 = store int 0 to %r1
    %r3 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r1, %r0)
    %r4 = call <test>::callee(%r0, %p0)
    %r5 = ret
"#,
    );
}

#[test]
fn call_passes_all_argument_conventions() {
    // A single call covers every Layer-1 passing convention at once:
    //   `a: int`       (`TrivialCopy`) -> by value, the `from_int(1)` rvalue;
    //   `m: &mut int`  (`MutableRef`)  -> the owned local's `alloca` place;
    //   `s: string`    (`SharedRef`)   -> the incoming shared-reference pointer, forwarded directly.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa(
            r#"
            fn callee(a: int, m: &mut int, s: string) { }
            fn caller(s: string) {
                let mut m = 0;
                callee(1, m, s)
            }
            "#,
        ),
        r#"fn callee(%p0: @arg int, %p1: @arg &mut int, %p2: @arg & string, %p3: @ret ()):
  0:
    %r0 = store () to %p3
    %r1 = ret

fn caller(%p0: @arg & string, %p1: @ret ()):
  0:
    %r0 = alloca int
    %r1 = alloca int
    %r2 = store int 0 to %r1
    %r3 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r1, %r0)
    %r4 = alloca int
    %r5 = store int 1 to %r4
    %r6 = alloca int
    %r7 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r4, %r6)
    %r8 = call <test>::callee(%r6, %r0, %p0, %p1)
    %r9 = ret
"#,
    );
}

#[test]
fn mutable_reference_parameter() {
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(x: &mut int) { x = 2; }"),
        r#"fn f(%p0: @arg &mut int, %p1: @ret ()):
  0:
    %r0 = alloca int
    %r1 = store int 2 to %r0
    %r2 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r0, %p0)
    %r3 = store () to %p1
    %r4 = ret
"#,
    );
}

#[test]
fn generic_apply() {
    let mut session = TestSession::new();
    // There is a dynamic stack allocation due to the conversion of the int 2 to A.
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(x) { x * 2 }"),
        r#"fn f(%p0: @extra ((A, A) -> A, (A, A) -> A, (A, A) -> A, (A) -> A, (A) -> A, (A) -> A, (int) -> A), %p1: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A) -> A, (&mut A) -> (), int, int), %p2: @arg & A, %p3: @ret A):
  0:
    %r0 = alloca A using %p1
    %r1 = dict_entry 6 from %p0
    %r2 = alloca int
    %r3 = store int 2 to %r2
    %r4 = call %r1(%r2, %r0)
    %r5 = dict_entry 2 from %p0
    %r6 = call %r5(%p2, %r0, %p3)
    %r7 = dict_entry 4 from %p1
    %r8 = drop %r0 via %r7
    %r9 = ret
"#,
    );
}

#[test]
fn dynamic_apply() {
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn apply_fn(f, x: int) { f(x) }"),
        r#"fn apply_fn(%p0: @arg & (int) -> A ! e₀, %p1: @arg int, %p2: @ret A):
  0:
    %r0 = call %p0(%p1, %p2)
    %r1 = ret
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
        session.emit_ssa("fn capture() -> int { let b = 1; let g = || b; g() }"),
        r#"fn $_ferlium_function_value_drop(%p0: @arg &mut A, %p1: @ret ()):
  0:
    %r0 = drop_closure_env %p0
    %r1 = store () to %p1
    %r2 = ret

fn $lambda$1(%p0: @arg &mut int, %p1: @ret int):
  0:
    %r0 = memcpy %p0 to %p1
    %r1 = ret

fn capture(%p0: @ret int):
  0:
    %r0 = alloca int
    %r1 = alloca () -> int
    %r2 = alloca int
    %r3 = store int 1 to %r2
    %r4 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r2, %r0)
    %r5 = alloca int
    %r6 = memcpy %r0 to %r5
    %r7 = build_closure <test>::$lambda$1(%r5, dict(m<...>:i0))
    %r8 = store %r7 to %r1
    %r9 = call %r1(%p0)
    %r10 = drop %r1 via <test>::$_ferlium_function_value_drop
    %r11 = ret

fn std::Value<(std::int,)>::clone#impl:7414fc52(%p0: @arg & (int,), %p1: @ret (int,)):
  0:
    %r0 = subfield int 0 from %p1
    %r1 = subfield int 0 from %p0
    %r2 = call std::std::Value<std::int>::clone#impl:2d38cab9(%r1, %r0)
    %r3 = ret

fn std::Value<(std::int,)>::drop#impl:d5ec4f8c(%p0: @arg &mut (int,), %p1: @ret ()):
  0:
    %r0 = subfield int 0 from %p0
    %r1 = alloca ()
    %r2 = call std::std::Value<std::int>::drop#impl:76f3f2ef(%r0, %r1)
    %r3 = store () to %p1
    %r4 = ret

fn std::Value<(std::int,)>::eq#impl:b00d2abd(%p0: @arg & (int,), %p1: @arg & (int,), %p2: @ret bool):
  0:
    %r0 = subfield int 0 from %p0
    %r1 = subfield int 0 from %p1
    %r2 = alloca bool
    %r3 = call std::std::Value<std::int>::eq#impl:87044288(%r0, %r1, %r2)
    %r4 = br 1
  1:
    %r5 = comp_eq %r2 i1 1
    %r6 = condbr %r5, %b2, &b3
  2:
    %r7 = store i1 1 to %p2
    %r8 = br 4
  3:
    %r9 = store i1 0 to %p2
    %r10 = br 4
  4:
    %r11 = ret

fn std::Value<(std::int,)>::hash#impl:58218263(%p0: @arg & (int,), %p1: @arg &mut hasher, %p2: @ret ()):
  0:
    %r0 = subfield int 0 from %p0
    %r1 = alloca ()
    %r2 = call std::std::Value<std::int>::hash#impl:bdc2934a(%r0, %p1, %r1)
    %r3 = store () to %p2
    %r4 = ret

fn std::Value<(std::int,)>::to_string#impl:30b07f9c(%p0: @arg & (int,), %p1: @ret string):
  0:
    %r0 = alloca string
    %r1 = alloca string
    %r2 = alloca string
    %r3 = store "(" to %r0
    %r4 = subfield int 0 from %p0
    %r5 = call std::std::Value<std::int>::to_string#impl:a5db1d9f(%r4, %r1)
    %r6 = alloca ()
    %r7 = call std::string_push_str(%r0, %r1, %r6)
    %r8 = drop %r1 via std::std::Value<std::string>::drop#impl:1d429675
    %r9 = store ")" to %r2
    %r10 = alloca ()
    %r11 = call std::string_push_str(%r0, %r2, %r10)
    %r12 = drop %r2 via std::std::Value<std::string>::drop#impl:1d429675
    %r13 = memcpy %r0 to %p1
    %r14 = ret
"#,
    );
}

// ============================================================================
// Generic handling tests
// ============================================================================

#[test]
fn generic_two_same_type_params() {
    // Two parameters of the same generic type share the same Num dictionary; the call forwards
    // both shared-ref args and the result pointer directly without an intermediate alloca.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(x, y) { x + y }"),
        r#"fn f(%p0: @extra ((A, A) -> A, (A, A) -> A, (A, A) -> A, (A) -> A, (A) -> A, (A) -> A, (int) -> A), %p1: @arg & A, %p2: @arg & A, %p3: @ret A):
  0:
    %r0 = dict_entry 0 from %p0
    %r1 = call %r0(%p1, %p2, %p3)
    %r2 = ret
"#,
    );
}

#[test]
fn generic_higher_order_function_param() {
    // A higher-order parameter `f: (A) -> A` is passed as a shared reference to a function
    // value whose generic variable appears only under the function type (function-surface).  The
    // call directly threads the incoming pointers with no intermediate alloca.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn apply(f: (A) -> A, x) { f(x) }"),
        r#"fn apply(%p0: @arg & (A) -> A ! e₀, %p1: @arg & A, %p2: @ret A):
  0:
    %r0 = call %p0(%p1, %p2)
    %r1 = ret
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
        session.emit_ssa("fn f(x) { x * x + x }"),
        r#"fn f(%p0: @extra ((A, A) -> A, (A, A) -> A, (A, A) -> A, (A) -> A, (A) -> A, (A) -> A, (int) -> A), %p1: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A) -> A, (&mut A) -> (), int, int), %p2: @arg & A, %p3: @ret A):
  0:
    %r0 = alloca A using %p1
    %r1 = dict_entry 2 from %p0
    %r2 = call %r1(%p2, %p2, %r0)
    %r3 = dict_entry 0 from %p0
    %r4 = call %r3(%r0, %p2, %p3)
    %r5 = dict_entry 4 from %p1
    %r6 = drop %r0 via %r5
    %r7 = ret
"#,
    );
}

#[test]
fn generic_comparison() {
    // Comparing two generic values calls `Value::eq` projected from the Value dictionary (%p0).
    // The result is a concrete `bool`, so the return place needs no dynamic alloca.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(x, y) { x == y }"),
        r#"fn f(%p0: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A) -> A, (&mut A) -> (), int, int), %p1: @arg & A, %p2: @arg & A, %p3: @ret bool):
  0:
    %r0 = dict_entry 0 from %p0
    %r1 = call %r0(%p1, %p2, %p3)
    %r2 = ret
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
        session.emit_ssa("fn f(x: int) { let y = x; y + 1 }"),
        r#"fn f(%p0: @arg int, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = alloca int
    %r2 = memcpy %p0 to %r0
    %r3 = alloca int
    %r4 = store int 1 to %r3
    %r5 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r3, %r1)
    %r6 = call std::std::Num<std::int>::add#impl:7665d3ee(%r0, %r1, %p1)
    %r7 = ret
"#,
    );
}

#[test]
fn construct_struct() {
    // Copying an int (TrivialCopy) - should use trivial copy, not call clone
    let mut session = TestSession::new();
    let ssa = session.emit_ssa(
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
        ssa,
        r#"fn make_a(%p0: @ret A):
  0:
    %r0 = subfield int 0 from %p0
    %r1 = alloca int
    %r2 = store int 1 to %r1
    %r3 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r1, %r0)
    %r4 = subfield int 1 from %p0
    %r5 = alloca int
    %r6 = store int 2 to %r5
    %r7 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r5, %r4)
    %r8 = ret

fn make_wrapper(%p0: @ret Wrapper):
  0:
    %r0 = subfield int 0 from %p0
    %r1 = call <test>::make_a(%r0)
    %r2 = subfield int 1 from %p0
    %r3 = call <test>::make_a(%r2)
    %r4 = ret

fn std::Value<<test>::A>::clone#impl:3b26fee6(%p0: @arg & A, %p1: @ret A):
  0:
    %r0 = subfield int 0 from %p1
    %r1 = subfield int 0 from %p0
    %r2 = call std::std::Value<std::int>::clone#impl:2d38cab9(%r1, %r0)
    %r3 = subfield int 1 from %p1
    %r4 = subfield int 1 from %p0
    %r5 = call std::std::Value<std::int>::clone#impl:2d38cab9(%r4, %r3)
    %r6 = ret

fn std::Value<<test>::A>::drop#impl:e48f46c8(%p0: @arg &mut A, %p1: @ret ()):
  0:
    %r0 = subfield int 0 from %p0
    %r1 = alloca ()
    %r2 = call std::std::Value<std::int>::drop#impl:76f3f2ef(%r0, %r1)
    %r3 = subfield int 1 from %p0
    %r4 = alloca ()
    %r5 = call std::std::Value<std::int>::drop#impl:76f3f2ef(%r3, %r4)
    %r6 = store () to %p1
    %r7 = ret

fn std::Value<<test>::A>::eq#impl:601557a9(%p0: @arg & A, %p1: @arg & A, %p2: @ret bool):
  0:
    %r0 = subfield int 0 from %p0
    %r1 = subfield int 0 from %p1
    %r2 = alloca bool
    %r3 = call std::std::Value<std::int>::eq#impl:87044288(%r0, %r1, %r2)
    %r4 = br 1
  1:
    %r5 = comp_eq %r2 i1 1
    %r6 = condbr %r5, %b2, &b3
  2:
    %r7 = subfield int 1 from %p0
    %r8 = subfield int 1 from %p1
    %r9 = alloca bool
    %r10 = call std::std::Value<std::int>::eq#impl:87044288(%r7, %r8, %r9)
    %r11 = br 5
  3:
    %r19 = store i1 0 to %p2
    %r20 = br 4
  4:
    %r21 = ret
  5:
    %r12 = comp_eq %r9 i1 1
    %r13 = condbr %r12, %b6, &b7
  6:
    %r14 = store i1 1 to %p2
    %r15 = br 8
  7:
    %r16 = store i1 0 to %p2
    %r17 = br 8
  8:
    %r18 = br 4

fn std::Value<<test>::A>::hash#impl:2d1a24bf(%p0: @arg & A, %p1: @arg &mut hasher, %p2: @ret ()):
  0:
    %r0 = subfield int 0 from %p0
    %r1 = alloca ()
    %r2 = call std::std::Value<std::int>::hash#impl:bdc2934a(%r0, %p1, %r1)
    %r3 = subfield int 1 from %p0
    %r4 = alloca ()
    %r5 = call std::std::Value<std::int>::hash#impl:bdc2934a(%r3, %p1, %r4)
    %r6 = store () to %p2
    %r7 = ret

fn std::Value<<test>::A>::to_string#impl:78412598(%p0: @arg & A, %p1: @ret string):
  0:
    %r0 = alloca string
    %r1 = alloca string
    %r2 = alloca string
    %r3 = alloca string
    %r4 = alloca string
    %r5 = alloca string
    %r6 = alloca string
    %r7 = alloca string
    %r8 = alloca string
    %r9 = store "A { " to %r0
    %r10 = store "x" to %r1
    %r11 = alloca ()
    %r12 = call std::string_push_str(%r0, %r1, %r11)
    %r13 = drop %r1 via std::std::Value<std::string>::drop#impl:1d429675
    %r14 = store ": " to %r2
    %r15 = alloca ()
    %r16 = call std::string_push_str(%r0, %r2, %r15)
    %r17 = drop %r2 via std::std::Value<std::string>::drop#impl:1d429675
    %r18 = subfield int 0 from %p0
    %r19 = call std::std::Value<std::int>::to_string#impl:a5db1d9f(%r18, %r3)
    %r20 = alloca ()
    %r21 = call std::string_push_str(%r0, %r3, %r20)
    %r22 = drop %r3 via std::std::Value<std::string>::drop#impl:1d429675
    %r23 = store ", " to %r4
    %r24 = alloca ()
    %r25 = call std::string_push_str(%r0, %r4, %r24)
    %r26 = drop %r4 via std::std::Value<std::string>::drop#impl:1d429675
    %r27 = store "y" to %r5
    %r28 = alloca ()
    %r29 = call std::string_push_str(%r0, %r5, %r28)
    %r30 = drop %r5 via std::std::Value<std::string>::drop#impl:1d429675
    %r31 = store ": " to %r6
    %r32 = alloca ()
    %r33 = call std::string_push_str(%r0, %r6, %r32)
    %r34 = drop %r6 via std::std::Value<std::string>::drop#impl:1d429675
    %r35 = subfield int 1 from %p0
    %r36 = call std::std::Value<std::int>::to_string#impl:a5db1d9f(%r35, %r7)
    %r37 = alloca ()
    %r38 = call std::string_push_str(%r0, %r7, %r37)
    %r39 = drop %r7 via std::std::Value<std::string>::drop#impl:1d429675
    %r40 = store " }" to %r8
    %r41 = alloca ()
    %r42 = call std::string_push_str(%r0, %r8, %r41)
    %r43 = drop %r8 via std::std::Value<std::string>::drop#impl:1d429675
    %r44 = memcpy %r0 to %p1
    %r45 = ret

fn std::Value<<test>::Wrapper>::clone#impl:e02c4c62(%p0: @arg & Wrapper, %p1: @ret Wrapper):
  0:
    %r0 = subfield int 0 from %p1
    %r1 = subfield int 0 from %p0
    %r2 = call <test>::std::Value<<test>::A>::clone#impl:3b26fee6(%r1, %r0)
    %r3 = subfield int 1 from %p1
    %r4 = subfield int 1 from %p0
    %r5 = call <test>::std::Value<<test>::A>::clone#impl:3b26fee6(%r4, %r3)
    %r6 = ret

fn std::Value<<test>::Wrapper>::drop#impl:c2860560(%p0: @arg &mut Wrapper, %p1: @ret ()):
  0:
    %r0 = subfield int 0 from %p0
    %r1 = alloca ()
    %r2 = call <test>::std::Value<<test>::A>::drop#impl:e48f46c8(%r0, %r1)
    %r3 = subfield int 1 from %p0
    %r4 = alloca ()
    %r5 = call <test>::std::Value<<test>::A>::drop#impl:e48f46c8(%r3, %r4)
    %r6 = store () to %p1
    %r7 = ret

fn std::Value<<test>::Wrapper>::eq#impl:d6883255(%p0: @arg & Wrapper, %p1: @arg & Wrapper, %p2: @ret bool):
  0:
    %r0 = subfield int 0 from %p0
    %r1 = subfield int 0 from %p1
    %r2 = alloca bool
    %r3 = call <test>::std::Value<<test>::A>::eq#impl:601557a9(%r0, %r1, %r2)
    %r4 = br 1
  1:
    %r5 = comp_eq %r2 i1 1
    %r6 = condbr %r5, %b2, &b3
  2:
    %r7 = subfield int 1 from %p0
    %r8 = subfield int 1 from %p1
    %r9 = alloca bool
    %r10 = call <test>::std::Value<<test>::A>::eq#impl:601557a9(%r7, %r8, %r9)
    %r11 = br 5
  3:
    %r19 = store i1 0 to %p2
    %r20 = br 4
  4:
    %r21 = ret
  5:
    %r12 = comp_eq %r9 i1 1
    %r13 = condbr %r12, %b6, &b7
  6:
    %r14 = store i1 1 to %p2
    %r15 = br 8
  7:
    %r16 = store i1 0 to %p2
    %r17 = br 8
  8:
    %r18 = br 4

fn std::Value<<test>::Wrapper>::hash#impl:65f26de7(%p0: @arg & Wrapper, %p1: @arg &mut hasher, %p2: @ret ()):
  0:
    %r0 = subfield int 0 from %p0
    %r1 = alloca ()
    %r2 = call <test>::std::Value<<test>::A>::hash#impl:2d1a24bf(%r0, %p1, %r1)
    %r3 = subfield int 1 from %p0
    %r4 = alloca ()
    %r5 = call <test>::std::Value<<test>::A>::hash#impl:2d1a24bf(%r3, %p1, %r4)
    %r6 = store () to %p2
    %r7 = ret

fn std::Value<<test>::Wrapper>::to_string#impl:7f6f6750(%p0: @arg & Wrapper, %p1: @ret string):
  0:
    %r0 = alloca string
    %r1 = alloca string
    %r2 = alloca string
    %r3 = alloca string
    %r4 = alloca string
    %r5 = alloca string
    %r6 = alloca string
    %r7 = alloca string
    %r8 = alloca string
    %r9 = store "Wrapper { " to %r0
    %r10 = store "left" to %r1
    %r11 = alloca ()
    %r12 = call std::string_push_str(%r0, %r1, %r11)
    %r13 = drop %r1 via std::std::Value<std::string>::drop#impl:1d429675
    %r14 = store ": " to %r2
    %r15 = alloca ()
    %r16 = call std::string_push_str(%r0, %r2, %r15)
    %r17 = drop %r2 via std::std::Value<std::string>::drop#impl:1d429675
    %r18 = subfield int 0 from %p0
    %r19 = call <test>::std::Value<<test>::A>::to_string#impl:78412598(%r18, %r3)
    %r20 = alloca ()
    %r21 = call std::string_push_str(%r0, %r3, %r20)
    %r22 = drop %r3 via std::std::Value<std::string>::drop#impl:1d429675
    %r23 = store ", " to %r4
    %r24 = alloca ()
    %r25 = call std::string_push_str(%r0, %r4, %r24)
    %r26 = drop %r4 via std::std::Value<std::string>::drop#impl:1d429675
    %r27 = store "right" to %r5
    %r28 = alloca ()
    %r29 = call std::string_push_str(%r0, %r5, %r28)
    %r30 = drop %r5 via std::std::Value<std::string>::drop#impl:1d429675
    %r31 = store ": " to %r6
    %r32 = alloca ()
    %r33 = call std::string_push_str(%r0, %r6, %r32)
    %r34 = drop %r6 via std::std::Value<std::string>::drop#impl:1d429675
    %r35 = subfield int 1 from %p0
    %r36 = call <test>::std::Value<<test>::A>::to_string#impl:78412598(%r35, %r7)
    %r37 = alloca ()
    %r38 = call std::string_push_str(%r0, %r7, %r37)
    %r39 = drop %r7 via std::std::Value<std::string>::drop#impl:1d429675
    %r40 = store " }" to %r8
    %r41 = alloca ()
    %r42 = call std::string_push_str(%r0, %r8, %r41)
    %r43 = drop %r8 via std::std::Value<std::string>::drop#impl:1d429675
    %r44 = memcpy %r0 to %p1
    %r45 = ret
"#
    );
}

#[test]
fn copy_struct_with_explicit_clone() {
    // Copying a struct with explicit clone function - should call Value::clone
    let mut session = TestSession::new();
    let ssa = session.emit_ssa(
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
        ssa,
        r#"fn f(%p0: @arg & Probe, %p1: @ret Probe):
  0:
    %r0 = call <test>::std::Value<<test>::Probe>::clone#impl:a879cee3(%p0, %p1)
    %r1 = ret

fn std::Value<<test>::Probe>::clone#impl:a879cee3(%p0: @arg & Probe, %p1: @ret Probe):
  0:
    %r0 = alloca int
    %r1 = subfield int 0 from %p1
    %r2 = alloca int
    %r3 = store int 100 to %r2
    %r4 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r2, %r0)
    %r5 = subfield int 0 from %p0
    %r6 = call std::std::Num<std::int>::add#impl:7665d3ee(%r5, %r0, %r1)
    %r7 = ret

fn std::Value<<test>::Probe>::drop#impl:c816a941(%p0: @arg &mut Probe, %p1: @ret ()):
  0:
    %r0 = store () to %p1
    %r1 = ret

fn std::Value<<test>::Probe>::eq#impl:938075a8(%p0: @arg & Probe, %p1: @arg & Probe, %p2: @ret bool):
  0:
    %r0 = subfield int 0 from %p0
    %r1 = subfield int 0 from %p1
    %r2 = call std::std::Value<std::int>::eq#impl:87044288(%r0, %r1, %p2)
    %r3 = ret

fn std::Value<<test>::Probe>::hash#impl:d7e4d34a(%p0: @arg & Probe, %p1: @arg &mut hasher, %p2: @ret ()):
  0:
    %r0 = subfield int 0 from %p0
    %r1 = call std::std::Value<std::int>::hash#impl:bdc2934a(%r0, %p1, %p2)
    %r2 = ret

fn std::Value<<test>::Probe>::to_string#impl:367ced11(%p0: @arg & Probe, %p1: @ret string):
  0:
    %r0 = subfield int 0 from %p0
    %r1 = call std::std::Value<std::int>::to_string#impl:a5db1d9f(%r0, %p1)
    %r2 = ret
"#
    );
    // TODO pattern based matching
}

#[test]
fn clone_value_generic_return() {
    // Returning a generic parameter clones it through the Value dictionary.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f<T>(x: T) -> T { x }"),
        r#"fn f(%p0: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A) -> A, (&mut A) -> (), int, int), %p1: @arg & A, %p2: @ret A):
  0:
    %r0 = dict_entry 3 from %p0
    %r1 = call %r0(%p1, %p2)
    %r2 = ret
"#,
    );
}

#[test]
fn clone_value_generic_branch() {
    // A generic parameter used in both branches of an if-else clones through the Value
    // dictionary in each branch, storing directly into the shared return out-pointer.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f<T>(x: T) -> T { if true { x } else { x } }"),
        r#"fn f(%p0: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A) -> A, (&mut A) -> (), int, int), %p1: @arg & A, %p2: @ret A):
  0:
    %r0 = br 1
  1:
    %r1 = comp_eq i1 1 i1 1
    %r2 = condbr %r1, %b2, &b3
  2:
    %r3 = dict_entry 3 from %p0
    %r4 = call %r3(%p1, %p2)
    %r5 = br 4
  3:
    %r6 = dict_entry 3 from %p0
    %r7 = call %r6(%p1, %p2)
    %r8 = br 4
  4:
    %r9 = ret
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
        session.emit_ssa("fn g<T>(x: &mut T) {} fn f<T>(x: T) { let mut y = x; g(y); }"),
        r#"fn f(%p0: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A) -> A, (&mut A) -> (), int, int), %p1: @arg & A, %p2: @ret ()):
  0:
    %r0 = alloca A using %p0
    %r1 = dict_entry 3 from %p0
    %r2 = call %r1(%p1, %r0)
    %r3 = alloca ()
    %r4 = call <test>::g(%r0, %r3)
    %r5 = store () to %p2
    %r6 = dict_entry 4 from %p0
    %r7 = drop %r0 via %r6
    %r8 = ret

fn g(%p0: @arg &mut A, %p1: @ret ()):
  0:
    %r0 = store () to %p1
    %r1 = ret
"#,
    );
}

#[test]
fn return_local_int_move() {
    // Returning a local int variable - should move (trivial copy for int)
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f() { let x: int = 42; x }"),
        r#"fn f(%p0: @ret int):
  0:
    %r0 = alloca int
    %r1 = store int 42 to %r0
    %r2 = memcpy %r0 to %p0
    %r3 = ret
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
        session.emit_ssa("fn f() -> int { let mut y: int = 1; y = 2; y }"),
        r#"fn f(%p0: @ret int):
  0:
    %r0 = alloca int
    %r1 = store int 1 to %r0
    %r2 = alloca int
    %r3 = store int 2 to %r2
    %r4 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r2, %r0)
    %r5 = memcpy %r0 to %p0
    %r6 = ret
"#,
    );
}

#[test]
fn reassign_local_from_param() {
    // Reassigning an owned local from a by-value param is a trivial copy: load %p0,
    // store into the local's alloca.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(x: int) -> int { let mut y: int = 0; y = x; y }"),
        r#"fn f(%p0: @arg int, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = store int 0 to %r0
    %r2 = memcpy %p0 to %r0
    %r3 = memcpy %r0 to %p1
    %r4 = ret
"#,
    );
}

#[test]
fn reassign_in_branches() {
    // Each branch writes its value directly into the same owned local's alloca.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa(
            "fn f(c: bool) -> int { let mut y: int = 0; if c { y = 1 } else { y = 2 }; y }"
        ),
        r#"fn f(%p0: @arg bool, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = alloca ()
    %r2 = store int 0 to %r0
    %r3 = br 1
  1:
    %r4 = comp_eq %p0 i1 1
    %r5 = condbr %r4, %b2, &b3
  2:
    %r6 = alloca int
    %r7 = store int 1 to %r6
    %r8 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r6, %r0)
    %r9 = store () to %r1
    %r10 = br 4
  3:
    %r11 = alloca int
    %r12 = store int 2 to %r11
    %r13 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r11, %r0)
    %r14 = store () to %r1
    %r15 = br 4
  4:
    %r16 = memcpy %r0 to %p1
    %r17 = ret
"#,
    );
}

#[test]
fn reassign_mutable_ref_param_from_local() {
    // Assigning through a `&mut` param writes into the caller's storage via the
    // incoming pointer; the source local is read with a trivial-copy load.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(x: &mut int) { let y: int = 1; x = y; }"),
        r#"fn f(%p0: @arg &mut int, %p1: @ret ()):
  0:
    %r0 = alloca int
    %r1 = store int 1 to %r0
    %r2 = memcpy %r0 to %p0
    %r3 = store () to %p1
    %r4 = ret
"#,
    );
}

#[test]
fn reassign_array_element_from_param() {
    // Assigning into an array element resolves the element place and stores the
    // param's trivially-copied value into it.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(a: &mut [int], v: int) { a[0] = v; }"),
        r#"fn f(%p0: @arg &mut [int], %p1: @arg int, %p2: @ret ()):
  0:
    %r0 = alloca int
    %r1 = store int 0 to %r0
    %r2 = alloca_place int
    %r3 = call std::array_index(%p0, %r0, %r2)
    %r4 = load %r2
    %r5 = memcpy %p1 to %r4
    %r6 = store () to %p2
    %r7 = ret
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
        session.emit_ssa("fn set<A>(a: &mut A, b: A) { a = b }"),
        r#"fn set(%p0: @extra ((A, A) -> bool, (A) -> string, (A, &mut hasher) -> (), (A) -> A, (&mut A) -> (), int, int), %p1: @arg &mut A, %p2: @arg & A, %p3: @ret ()):
  0:
    %r0 = alloca A using %p0
    %r1 = dict_entry 3 from %p0
    %r2 = call %r1(%p2, %r0)
    %r3 = dict_entry 4 from %p0
    %r4 = drop %p1 via %r3
    %r5 = memcpy %r0 to %p1 using %p0
    %r6 = store () to %p3
    %r7 = ret
"#
    )
}

// A `()`-returning function's return out-pointer starts a **husk** (uninitialized) — it is *not*
// pre-seeded live — so the body must write the single `()` result into it before a normal return.
// A body that fails to do so is caught by the call-boundary check ("`@ret` must be fully initialized
// when the callee returns normally"). The following tests pin that every `()`-typed tail shape whose
// node does not itself produce a value into the destination (an assignment, a `let`, a closure-env
// drop) still initializes `@ret`. Before the fix these left `@ret` uninitialized and trapped.

#[test]
fn void_body_tail_assignment_writes_ret() {
    // Body tail is a bare assignment through a `&mut` (no trailing `;`), so the assignment itself is
    // the `()`-typed tail. It writes `store () to %p1` before returning.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn set(a: &mut int, v: int) { a = v }"),
        r#"fn set(%p0: @arg &mut int, %p1: @arg int, %p2: @ret ()):
  0:
    %r0 = memcpy %p1 to %p0
    %r1 = store () to %p2
    %r2 = ret
"#,
    );
    // And it runs: the caller observes the write, and the boundary check (that `@ret` is initialized)
    // passes.
    assert_val_eq!(
        session.run("fn set(a: &mut int, v: int) { a = v }\nfn driver() -> int { let mut x = 0; set(x, 5); x }\ndriver()"),
        int(5)
    );
}

#[test]
fn reassign_local_literal_overwrites_resource_free_in_place() {
    // The relaxed `store` invariant: a `store`/call result may overwrite storage that owns no live
    // resource (a scalar reassigned in place), which `store` never drops. Only overwriting a
    // resource-owning value without a prior `drop` is a lowering bug. This exercises the in-place
    // scalar overwrite that the strict "target must be a husk" rule would (wrongly) forbid.
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
    // `eval_case` (`scrutinee.to_literal_value() == pattern`, structural) — the SSA does not
    // decompose the tuple.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn g(x) -> int { match x { (true, true) => 1, _ => 2 } }"),
        r#"fn g(%p0: @arg & A, %p1: @ret int):
  0:
    %r0 = br 1
  1:
    %r1 = comp_eq %p0 (true, true)
    %r2 = condbr %r1, %b2, &b3
  2:
    %r3 = alloca int
    %r4 = store int 1 to %r3
    %r5 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r3, %p1)
    %r6 = br 4
  3:
    %r7 = alloca int
    %r8 = store int 2 to %r7
    %r9 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r7, %p1)
    %r10 = br 4
  4:
    %r11 = ret
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
        session.emit_ssa("fn n(x) -> int { match x { (true, (false, true)) => 1, _ => 2 } }"),
        r#"fn n(%p0: @arg & A, %p1: @ret int):
  0:
    %r0 = br 1
  1:
    %r1 = comp_eq %p0 (true, (false, true))
    %r2 = condbr %r1, %b2, &b3
  2:
    %r3 = alloca int
    %r4 = store int 1 to %r3
    %r5 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r3, %p1)
    %r6 = br 4
  3:
    %r7 = alloca int
    %r8 = store int 2 to %r7
    %r9 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r7, %p1)
    %r10 = br 4
  4:
    %r11 = ret
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
        session.emit_ssa("fn f(s) -> int { match s { \"a\" => 1, _ => 2 } }"),
        r#"fn f(%p0: @arg & A, %p1: @ret int):
  0:
    %r0 = br 1
  1:
    %r1 = comp_eq %p0 "a"
    %r2 = condbr %r1, %b2, &b3
  2:
    %r3 = alloca int
    %r4 = store int 1 to %r3
    %r5 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r3, %p1)
    %r6 = br 4
  3:
    %r7 = alloca int
    %r8 = store int 2 to %r7
    %r9 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r7, %p1)
    %r10 = br 4
  4:
    %r11 = ret
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
        session.emit_ssa("fn f(x) -> int { match x { 0 => 1, _ => 2 } }"),
        r#"fn f(%p0: @arg & A, %p1: @ret int):
  0:
    %r0 = br 1
  1:
    %r1 = comp_eq %p0 int 0
    %r2 = condbr %r1, %b2, &b3
  2:
    %r3 = alloca int
    %r4 = store int 1 to %r3
    %r5 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r3, %p1)
    %r6 = br 4
  3:
    %r7 = alloca int
    %r8 = store int 2 to %r7
    %r9 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r7, %p1)
    %r10 = br 4
  4:
    %r11 = ret
"#,
    );
}

#[test]
fn copy_int_param_to_local() {
    // Copying int parameter to a mutable local - uses trivial copy
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(x: int) { let mut y = x; y = y + 1; y }"),
        r#"fn f(%p0: @arg int, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = alloca int
    %r2 = memcpy %p0 to %r0
    %r3 = alloca int
    %r4 = store int 1 to %r3
    %r5 = call std::std::Num<std::int>::from_int#impl:25eabc6b(%r3, %r1)
    %r6 = call std::std::Num<std::int>::add#impl:7665d3ee(%r0, %r1, %r0)
    %r7 = memcpy %r0 to %p1
    %r8 = ret
"#,
    );
}

#[test]
fn variants() {
    let mut session = TestSession::new();

    assert_eq_sans_flake!(
        session.emit_ssa("fn f(x: Y | X(string)) { let r = x; } "),
        r#"fn f(%p0: @arg & X (string) | Y, %p1: @ret ()):
  0:
    %r0 = store () to %p1
    %r1 = ret
"#
    );
}

#[test]
fn named_subscript_read() {
    let mut session = TestSession::new();
    session.allow_experimental();
    assert_eq_sans_flake!(
        session.emit_ssa(
            "subscript first(values: &mut [int]) -> int { ref mut { return values[0] } }\nfn f(a: &mut [int]) -> int { a->[first] }",
        ),
        r#"fn f(%p0: @arg &mut [int], %p1: @ret int):
  0:
    %r0 = alloca_place int
    %r1 = call <test>::first(%p0, %r0)
    %r2 = load %r0
    %r3 = memcpy %r2 to %p1
    %r4 = ret

fn first(%p0: @arg &mut [int], %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = store int 0 to %r0
    %r2 = alloca_place int
    %r3 = call std::array_index(%p0, %r0, %r2)
    %r4 = load %r2
    %r5 = store %r4 to %p1
    %r6 = ret
"#,
    );
}

#[test]
fn named_subscript_assign() {
    let mut session = TestSession::new();
    session.allow_experimental();
    assert_eq_sans_flake!(
        session.emit_ssa(
            "subscript first(values: &mut [int]) -> int { ref mut { return values[0] } }\nfn f(a: &mut [int], v: int) { a->[first] = v }",
        ),
        r#"fn f(%p0: @arg &mut [int], %p1: @arg int, %p2: @ret ()):
  0:
    %r0 = alloca_place int
    %r1 = call <test>::first(%p0, %r0)
    %r2 = load %r0
    %r3 = memcpy %p1 to %r2
    %r4 = store () to %p2
    %r5 = ret

fn first(%p0: @arg &mut [int], %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = store int 0 to %r0
    %r2 = alloca_place int
    %r3 = call std::array_index(%p0, %r0, %r2)
    %r4 = load %r2
    %r5 = store %r4 to %p1
    %r6 = ret
"#,
    );
}

#[test]
fn named_subscript_compound_assign() {
    let mut session = TestSession::new();
    session.allow_experimental();
    assert_eq_sans_flake!(
        session.emit_ssa(
            "subscript first(values: &mut [int]) -> int { ref mut { return values[0] } }\nfn f(a: &mut [int], v: int) { a->[first] += v }",
        ),
        r#"fn f(%p0: @arg &mut [int], %p1: @arg int, %p2: @ret ()):
  0:
    %r0 = alloca_place int
    %r1 = call <test>::first(%p0, %r0)
    %r2 = load %r0
    %r3 = call std::std::Num<std::int>::add#impl:7665d3ee(%r2, %p1, %r2)
    %r4 = store () to %p2
    %r5 = ret

fn first(%p0: @arg &mut [int], %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = store int 0 to %r0
    %r2 = alloca_place int
    %r3 = call std::array_index(%p0, %r0, %r2)
    %r4 = load %r2
    %r5 = store %r4 to %p1
    %r6 = ret
"#,
    );
}

#[test]
fn explicit_return_value() {
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn g(x: int) -> int { return x }"),
        r#"fn g(%p0: @arg int, %p1: @ret int):
  0:
    %r0 = memcpy %p0 to %p1
    %r1 = ret
"#,
    );
}

#[test]
fn addressor_subscript_member_returns_place() {
    let mut session = TestSession::new();
    session.allow_experimental();
    // The addressor member is emitted by the top-level `emit_ssa` (subscript members are part of
    // the module). Its body returns the *place pointer* through its return out-pointer: the final
    // `store %r4 to %p1` writes the `*int` place into the `**int` slot.
    assert_eq_sans_flake!(
        session.emit_ssa(
            "subscript first(values: &mut [int]) -> int { ref mut { return values[0] } }",
        ),
        r#"fn first(%p0: @arg &mut [int], %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = store int 0 to %r0
    %r2 = alloca_place int
    %r3 = call std::array_index(%p0, %r0, %r2)
    %r4 = load %r2
    %r5 = store %r4 to %p1
    %r6 = ret
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
        session.emit_ssa(
            "subscript cell(slot: &mut int) -> int { ref mut { let mut local = slot; yield local; slot = local } }",
        ),
        r#"fn cell(%p0: @arg &mut int, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = memcpy %p0 to %r0
    %r2 = yield %r0
    %r3 = memcpy %r0 to %p0
    %r4 = ret
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
        session.emit_ssa(&format!(
            "{CELL_SUBSCRIPT}fn f(a: &mut int) -> int {{ a->[cell] }}"
        )),
        r#"fn cell(%p0: @arg &mut int, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = memcpy %p0 to %r0
    %r2 = yield %r0
    %r3 = memcpy %r0 to %p0
    %r4 = ret

fn f(%p0: @arg &mut int, %p1: @ret int):
  0:
    %r0 = project <test>::cell(%p0)
    %r1 = memcpy %r0 to %p1
    %r2 = end_project %r0
    %r3 = ret
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
        session.emit_ssa(&format!(
            "{CELL_SUBSCRIPT}fn f(a: &mut int, v: int) {{ a->[cell] = v }}"
        )),
        r#"fn cell(%p0: @arg &mut int, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = memcpy %p0 to %r0
    %r2 = yield %r0
    %r3 = memcpy %r0 to %p0
    %r4 = ret

fn f(%p0: @arg &mut int, %p1: @arg int, %p2: @ret ()):
  0:
    %r0 = project <test>::cell(%p0)
    %r1 = memcpy %p1 to %r0
    %r2 = store () to %p2
    %r3 = end_project %r0
    %r4 = ret
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
        session.emit_ssa(
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
        r#"fn cell(%p0: @arg &mut int, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = memcpy %p0 to %r0
    %r2 = yield %r0
    %r3 = memcpy %r0 to %p0
    %r4 = ret

fn f(%p0: @arg &mut int, %p1: @arg int, %p2: @ret ()):
  0:
    %r0 = project <test>::cell(%p0)
    %r1 = call std::std::Num<std::int>::add#impl:7665d3ee(%r0, %p1, %r0)
    %r2 = store () to %p2
    %r3 = end_project %r0
    %r4 = ret
"#,
    );
}

#[test]
fn yielded_subscript_fallible_body_runs_slide_on_unwind() {
    // When the body of a scoped subscript can raise (here a fallible `/`), the write into the yielded
    // place is an `invoke`: on the error edge it diverts to a cleanup pad that runs `end_project` (the
    // accessor slide) before `resume`ing the unwind to the caller — the slide runs on the error path,
    // matching the HIR interpreter's epilogue-on-transfer.
    let mut session = TestSession::new();
    session.allow_experimental();
    assert_eq_sans_flake!(
        session.emit_ssa(&format!(
            "{CELL_SUBSCRIPT}fn f(a: &mut int, v: int, w: int) {{ a->[cell] = idiv(v, w) }}"
        )),
        r#"fn cell(%p0: @arg &mut int, %p1: @ret int):
  0:
    %r0 = alloca int
    %r1 = memcpy %p0 to %r0
    %r2 = yield %r0
    %r3 = memcpy %r0 to %p0
    %r4 = ret

fn f(%p0: @arg &mut int, %p1: @arg int, %p2: @arg int, %p3: @ret ()):
  0:
    %r0 = project <test>::cell(%p0)
    %r1 = invoke std::idiv(%p1, %p2, %r0) -> b2 unwind b1
  1:
    %r5 = end_project %r0
    %r6 = resume
  2:
    %r2 = store () to %p3
    %r3 = end_project %r0
    %r4 = ret
"#,
    );
}

// Dual-backend value tests for the scoped (`yield`) subscript: each runs under both the HIR and the
// SSA interpreter and asserts they agree, so the SSA `project`/`yield`/`end_project` suspend-resume
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
    // A raise in the body unwinds out of the projection on both backends (the SSA pad runs the slide
    // then `resume`s); the outcomes agree — a `DivisionByZero` runtime error.
    assert_eq!(
        session.fail_run(&format!(
            "{CELL_SUBSCRIPT}fn bad(a: &mut int, w: int) {{ a->[cell] = idiv(1, w) }}\nfn driver() -> int {{ let mut x = 5; bad(x, 0); x }}\ndriver()"
        )),
        ferlium::compiler::error::RuntimeErrorKind::DivisionByZero,
    );
}

#[test]
fn closure_over_generic_in_concrete_caller() {
    // 2a: a generic function used first-class in a CONCRETE caller. The dictionary the generic
    // needs is statically known, so it is captured as a symbolic `dict(...)` operand on
    // `build_closure` (a leading hidden-dictionary operand; there are no value captures).
    let mut session = TestSession::new();
    let out = session.emit_ssa("fn id<T>(x: T) -> T { x } fn use_id() -> int { let f = id; f(5) }");
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
    let out = session.emit_ssa("fn adder(n) { |x| x + n }");
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
        session.emit_ssa("fn f(x: int) { (x, x); x }"),
        r#"fn f(%p0: @arg int, %p1: @ret int):
  0:
    %r0 = alloca (int, int)
    %r1 = subfield int 0 from %r0
    %r2 = memcpy %p0 to %r1
    %r3 = subfield int 1 from %r0
    %r4 = memcpy %p0 to %r3
    %r5 = memcpy %p0 to %p1
    %r6 = ret
"#,
    );
}

#[test]
fn discarded_record_construction_lowers_into_throwaway_temp() {
    // As for the tuple, the discarded `{ a: x, b: x }` is materialized into a fresh record temp so
    // both field writes still happen.
    let mut session = TestSession::new();
    assert_eq_sans_flake!(
        session.emit_ssa("fn f(x: int) { { a: x, b: x }; x }"),
        r#"fn f(%p0: @arg int, %p1: @ret int):
  0:
    %r0 = alloca { a: int, b: int }
    %r1 = subfield int 0 from %r0
    %r2 = memcpy %p0 to %r1
    %r3 = subfield int 1 from %r0
    %r4 = memcpy %p0 to %r3
    %r5 = memcpy %p0 to %p1
    %r6 = ret
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
    // scalar-call (no-drop) case. The HIR/SSA parity check inside `run` is the real assertion.
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
