use test_log::test;

use ferlium::{format::FormatWith, module::ShowModuleWithOptions};

use crate::harness::TestSession;

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
    %r3 = call std::Num<0-6>::from_int(%r1, %r0)
    %r4 = call std::Num<0-6>::add(%p0, %r0, %p1)
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
    %r4 = call std::Num<0-6>::from_int(%r2, %r0)
    %r5 = call std::Num<0-6>::mul(%r0, %p0, %r1)
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
    %r7 = call std::Num<...>::from_int(%r5, %p1)
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
    %r11 = call std::Num<...>::from_int(%r9, %r1)
    %r12 = call std::Num<...>::sub(%p0, %r1, %p1)
    %r13 = br 6
  5:
    %r14 = alloca int
    %r15 = store int 1 to %r14
    %r16 = call std::Num<...>::from_int(%r14, %r0)
    %r17 = call std::Num<...>::neg(%r0, %p1)
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
    %r6 = call std::Num<...>::from_int(%r4, %r0)
    %r7 = alloca ((int, int) -> Ordering,)
    %r8 = store (std::Ord<...>::cmp) to %r7
    %r9 = call std::gt(%r7, %p0, %r0, %r3)
    %r10 = br 1
  1:
    %r11 = comp_eq %r3 i1 1
    %r12 = condbr %r11, %b2, &b3
  2:
    %r13 = alloca int
    %r14 = alloca int
    %r15 = store int 1 to %r14
    %r16 = call std::Num<...>::from_int(%r14, %r1)
    %r17 = call std::Num<...>::sub(%p0, %r1, %r13)
    %r18 = call <test>::factorial(%r13, %r2)
    %r19 = call std::Num<...>::mul(%p0, %r2, %p1)
    %r20 = br 4
  3:
    %r21 = alloca int
    %r22 = store int 1 to %r21
    %r23 = call std::Num<...>::from_int(%r21, %p1)
    %r24 = br 4
  4:
    %r25 = ret
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
    %r0 = call std::Num<0-6>::add(%p0, %p1, %p2)
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
    %r5 = call std::Num<0-6>::from_int(%r3, %r1)
    %r6 = call std::Num<0-6>::add(%r0, %r1, %r0)
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
    %r5 = call std::Num<...>::from_int(%r3, %r1)
    %r6 = call std::Num<...>::add(%r0, %r1, %r0)
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
    %r10 = call std::Num<...>::from_int(%r8, %p1)
    %r11 = br 4
  3:
    %r12 = alloca int
    %r13 = store int 2 to %r12
    %r14 = call std::Num<...>::from_int(%r12, %p1)
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
    %r6 = ret
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
    %r10 = call std::Num<0-6>::from_int(%r8, %r1)
    %r11 = call std::Num<0-6>::add(%r0, %r1, %r0)
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
    %r5 = ret
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
    %r0 = ret
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
    %r0 = ret
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
    %r5 = project 1 from %r4
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
    %r0 = ret
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
    %r0 = ret
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
    %r0 = ret
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
    %r3 = call std::Num<0-6>::from_int(%r1, %r0)
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
    %r0 = ret

fn caller(%p0: @ret ()):
  0:
    %r0 = alloca int
    %r1 = alloca int
    %r2 = store int 0 to %r1
    %r3 = call std::Num<0-6>::from_int(%r1, %r0)
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
    %r0 = ret

fn caller(%p0: @arg & string, %p1: @ret ()):
  0:
    %r0 = alloca int
    %r1 = alloca int
    %r2 = store int 0 to %r1
    %r3 = call std::Num<0-6>::from_int(%r1, %r0)
    %r4 = alloca int
    %r5 = store int 1 to %r4
    %r6 = alloca int
    %r7 = call std::Num<0-6>::from_int(%r4, %r6)
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
    %r2 = call std::Num<0-6>::from_int(%r0, %p0)
    %r3 = ret
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
    %r1 = project 6 from %p0
    %r2 = load %r1
    %r3 = alloca int
    %r4 = store int 2 to %r3
    %r5 = call %r2(%r3, %r0)
    %r6 = project 2 from %p0
    %r7 = load %r6
    %r8 = call %r7(%p2, %r0, %p3)
    %r9 = project 4 from %p1
    %r10 = load %r9
    %r11 = drop %r0 via %r10
    %r12 = ret
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
    %r0 = load %p0
    %r1 = call %r0(%p1, %p2)
    %r2 = ret
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
    %r0 = project 0 from %p0
    %r1 = load %r0
    %r2 = call %r1(%p1, %p2, %p3)
    %r3 = ret
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
    %r0 = load %p0
    %r1 = call %r0(%p1, %p2)
    %r2 = ret
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
    %r1 = project 2 from %p0
    %r2 = load %r1
    %r3 = call %r2(%p2, %p2, %r0)
    %r4 = project 0 from %p0
    %r5 = load %r4
    %r6 = call %r5(%r0, %p2, %p3)
    %r7 = project 4 from %p1
    %r8 = load %r7
    %r9 = drop %r0 via %r8
    %r10 = ret
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
    %r0 = project 0 from %p0
    %r1 = load %r0
    %r2 = call %r1(%p1, %p2, %p3)
    %r3 = ret
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
    %r5 = call std::Num<...>::from_int(%r3, %r1)
    %r6 = call std::Num<...>::add(%r0, %r1, %p1)
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
        r#"fn Value<...>::clone(%p0: @arg & A, %p1: @ret A):
  0:
    %r0 = project 0 from %p1
    %r1 = project 0 from %p0
    %r2 = call std::Value<...>::clone(%r1, %r0)
    %r3 = project 1 from %p1
    %r4 = project 1 from %p0
    %r5 = call std::Value<...>::clone(%r4, %r3)
    %r6 = ret

fn Value<...>::drop(%p0: @arg &mut A, %p1: @ret ()):
  0:
    %r0 = project 0 from %p0
    %r1 = call std::Value<...>::drop(%r0, &())
    %r2 = project 1 from %p0
    %r3 = call std::Value<...>::drop(%r2, &())
    %r4 = ret

fn Value<...>::eq(%p0: @arg & A, %p1: @arg & A, %p2: @ret bool):
  0:
    %r0 = project 0 from %p0
    %r1 = project 0 from %p1
    %r2 = alloca bool
    %r3 = call std::Value<...>::eq(%r0, %r1, %r2)
    %r4 = br 1
  1:
    %r5 = comp_eq %r2 i1 1
    %r6 = condbr %r5, %b2, &b3
  2:
    %r7 = project 1 from %p0
    %r8 = project 1 from %p1
    %r9 = alloca bool
    %r10 = call std::Value<...>::eq(%r7, %r8, %r9)
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

fn Value<...>::hash(%p0: @arg & A, %p1: @arg &mut hasher, %p2: @ret ()):
  0:
    %r0 = project 0 from %p0
    %r1 = call std::Value<...>::hash(%r0, %p1, &())
    %r2 = project 1 from %p0
    %r3 = call std::Value<...>::hash(%r2, %p1, &())
    %r4 = ret

fn Value<...>::to_string(%p0: @arg & A, %p1: @ret string):
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
    %r11 = call std::string_push_str(%r0, %r1, &())
    %r12 = drop %r1 via std::Value<...>::drop
    %r13 = store ": " to %r2
    %r14 = call std::string_push_str(%r0, %r2, &())
    %r15 = drop %r2 via std::Value<...>::drop
    %r16 = project 0 from %p0
    %r17 = call std::Value<...>::to_string(%r16, %r3)
    %r18 = call std::string_push_str(%r0, %r3, &())
    %r19 = drop %r3 via std::Value<...>::drop
    %r20 = store ", " to %r4
    %r21 = call std::string_push_str(%r0, %r4, &())
    %r22 = drop %r4 via std::Value<...>::drop
    %r23 = store "y" to %r5
    %r24 = call std::string_push_str(%r0, %r5, &())
    %r25 = drop %r5 via std::Value<...>::drop
    %r26 = store ": " to %r6
    %r27 = call std::string_push_str(%r0, %r6, &())
    %r28 = drop %r6 via std::Value<...>::drop
    %r29 = project 1 from %p0
    %r30 = call std::Value<...>::to_string(%r29, %r7)
    %r31 = call std::string_push_str(%r0, %r7, &())
    %r32 = drop %r7 via std::Value<...>::drop
    %r33 = store " }" to %r8
    %r34 = call std::string_push_str(%r0, %r8, &())
    %r35 = drop %r8 via std::Value<...>::drop
    %r36 = memcpy %r0 to %p1
    %r37 = ret

fn Value<...>::clone(%p0: @arg & Wrapper, %p1: @ret Wrapper):
  0:
    %r0 = project 0 from %p1
    %r1 = project 0 from %p0
    %r2 = call <test>::Value<...>::clone(%r1, %r0)
    %r3 = project 1 from %p1
    %r4 = project 1 from %p0
    %r5 = call <test>::Value<...>::clone(%r4, %r3)
    %r6 = ret

fn Value<...>::drop(%p0: @arg &mut Wrapper, %p1: @ret ()):
  0:
    %r0 = project 0 from %p0
    %r1 = call <test>::Value<...>::drop(%r0, &())
    %r2 = project 1 from %p0
    %r3 = call <test>::Value<...>::drop(%r2, &())
    %r4 = ret

fn Value<...>::eq(%p0: @arg & Wrapper, %p1: @arg & Wrapper, %p2: @ret bool):
  0:
    %r0 = project 0 from %p0
    %r1 = project 0 from %p1
    %r2 = alloca bool
    %r3 = call <test>::Value<...>::eq(%r0, %r1, %r2)
    %r4 = br 1
  1:
    %r5 = comp_eq %r2 i1 1
    %r6 = condbr %r5, %b2, &b3
  2:
    %r7 = project 1 from %p0
    %r8 = project 1 from %p1
    %r9 = alloca bool
    %r10 = call <test>::Value<...>::eq(%r7, %r8, %r9)
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

fn Value<...>::hash(%p0: @arg & Wrapper, %p1: @arg &mut hasher, %p2: @ret ()):
  0:
    %r0 = project 0 from %p0
    %r1 = call <test>::Value<...>::hash(%r0, %p1, &())
    %r2 = project 1 from %p0
    %r3 = call <test>::Value<...>::hash(%r2, %p1, &())
    %r4 = ret

fn Value<...>::to_string(%p0: @arg & Wrapper, %p1: @ret string):
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
    %r11 = call std::string_push_str(%r0, %r1, &())
    %r12 = drop %r1 via std::Value<...>::drop
    %r13 = store ": " to %r2
    %r14 = call std::string_push_str(%r0, %r2, &())
    %r15 = drop %r2 via std::Value<...>::drop
    %r16 = project 0 from %p0
    %r17 = call <test>::Value<...>::to_string(%r16, %r3)
    %r18 = call std::string_push_str(%r0, %r3, &())
    %r19 = drop %r3 via std::Value<...>::drop
    %r20 = store ", " to %r4
    %r21 = call std::string_push_str(%r0, %r4, &())
    %r22 = drop %r4 via std::Value<...>::drop
    %r23 = store "right" to %r5
    %r24 = call std::string_push_str(%r0, %r5, &())
    %r25 = drop %r5 via std::Value<...>::drop
    %r26 = store ": " to %r6
    %r27 = call std::string_push_str(%r0, %r6, &())
    %r28 = drop %r6 via std::Value<...>::drop
    %r29 = project 1 from %p0
    %r30 = call <test>::Value<...>::to_string(%r29, %r7)
    %r31 = call std::string_push_str(%r0, %r7, &())
    %r32 = drop %r7 via std::Value<...>::drop
    %r33 = store " }" to %r8
    %r34 = call std::string_push_str(%r0, %r8, &())
    %r35 = drop %r8 via std::Value<...>::drop
    %r36 = memcpy %r0 to %p1
    %r37 = ret

fn make_a(%p0: @ret A):
  0:
    %r0 = project 0 from %p0
    %r1 = alloca int
    %r2 = store int 1 to %r1
    %r3 = call std::Num<...>::from_int(%r1, %r0)
    %r4 = project 1 from %p0
    %r5 = alloca int
    %r6 = store int 2 to %r5
    %r7 = call std::Num<...>::from_int(%r5, %r4)
    %r8 = ret

fn make_wrapper(%p0: @ret Wrapper):
  0:
    %r0 = project 0 from %p0
    %r1 = call <test>::make_a(%r0)
    %r2 = project 1 from %p0
    %r3 = call <test>::make_a(%r2)
    %r4 = ret
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
        r#"fn Value<...>::clone(%p0: @arg & Probe, %p1: @ret Probe):
  0:
    %r0 = alloca int
    %r1 = project 0 from %p1
    %r2 = alloca int
    %r3 = store int 100 to %r2
    %r4 = call std::Num<...>::from_int(%r2, %r0)
    %r5 = project 0 from %p0
    %r6 = call std::Num<...>::add(%r5, %r0, %r1)
    %r7 = ret

fn Value<...>::drop(%p0: @arg &mut Probe, %p1: @ret ()):
  0:
    %r0 = ret

fn Value<...>::eq(%p0: @arg & Probe, %p1: @arg & Probe, %p2: @ret bool):
  0:
    %r0 = project 0 from %p0
    %r1 = project 0 from %p1
    %r2 = call std::Value<...>::eq(%r0, %r1, %p2)
    %r3 = ret

fn Value<...>::hash(%p0: @arg & Probe, %p1: @arg &mut hasher, %p2: @ret ()):
  0:
    %r0 = project 0 from %p0
    %r1 = call std::Value<...>::hash(%r0, %p1, %p2)
    %r2 = ret

fn Value<...>::to_string(%p0: @arg & Probe, %p1: @ret string):
  0:
    %r0 = project 0 from %p0
    %r1 = call std::Value<...>::to_string(%r0, %p1)
    %r2 = ret

fn f(%p0: @arg & Probe, %p1: @ret Probe):
  0:
    %r0 = call <test>::Value<...>::clone(%p0, %p1)
    %r1 = ret
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
    %r0 = project 3 from %p0
    %r1 = load %r0
    %r2 = call %r1(%p1, %p2)
    %r3 = ret
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
    %r3 = project 3 from %p0
    %r4 = load %r3
    %r5 = call %r4(%p1, %p2)
    %r6 = br 4
  3:
    %r7 = project 3 from %p0
    %r8 = load %r7
    %r9 = call %r8(%p1, %p2)
    %r10 = br 4
  4:
    %r11 = ret
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
    %r1 = project 3 from %p0
    %r2 = load %r1
    %r3 = call %r2(%p1, %r0)
    %r4 = call <test>::g(%r0, &())
    %r5 = project 4 from %p0
    %r6 = load %r5
    %r7 = drop %r0 via %r6
    %r8 = ret

fn g(%p0: @arg &mut A, %p1: @ret ()):
  0:
    %r0 = ret
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
    %r4 = call std::Num<0-6>::from_int(%r2, %r0)
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
    %r8 = call std::Num<...>::from_int(%r6, %r0)
    %r9 = br 4
  3:
    %r10 = alloca int
    %r11 = store int 2 to %r10
    %r12 = call std::Num<...>::from_int(%r10, %r0)
    %r13 = br 4
  4:
    %r14 = memcpy %r0 to %p1
    %r15 = ret
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
    %r3 = ret
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
    %r6 = ret
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
    %r1 = project 3 from %p0
    %r2 = load %r1
    %r3 = call %r2(%p2, %r0)
    %r4 = project 4 from %p0
    %r5 = load %r4
    %r6 = drop %p1 via %r5
    %r7 = memcpy %r0 to %p1
    %r8 = ret
"#
    )
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
    %r5 = call std::Num<...>::from_int(%r3, %p1)
    %r6 = br 4
  3:
    %r7 = alloca int
    %r8 = store int 2 to %r7
    %r9 = call std::Num<...>::from_int(%r7, %p1)
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
    %r5 = call std::Num<...>::from_int(%r3, %p1)
    %r6 = br 4
  3:
    %r7 = alloca int
    %r8 = store int 2 to %r7
    %r9 = call std::Num<...>::from_int(%r7, %p1)
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
    %r5 = call std::Num<...>::from_int(%r3, %p1)
    %r6 = br 4
  3:
    %r7 = alloca int
    %r8 = store int 2 to %r7
    %r9 = call std::Num<...>::from_int(%r7, %p1)
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
    %r5 = call std::Num<...>::from_int(%r3, %p1)
    %r6 = br 4
  3:
    %r7 = alloca int
    %r8 = store int 2 to %r7
    %r9 = call std::Num<...>::from_int(%r7, %p1)
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
    %r5 = call std::Num<...>::from_int(%r3, %r1)
    %r6 = call std::Num<...>::add(%r0, %r1, %r0)
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
    %r0 = ret
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
    %r3 = call std::Num<...>::add(%r2, %p1, %r2)
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
fn yielded_subscript_member_is_not_emitted_standalone() {
    // A scoped (`yield`) member has YieldedOnce convention and no standalone SSA form: it is
    // consumed inline at its WithYielded site. The top-level `emit_ssa` skips it, so a module
    // defining only such a subscript lowers to nothing.
    let mut session = TestSession::new();
    session.allow_experimental();
    assert_eq!(
        session.emit_ssa(
            "subscript cell(slot: &mut int) -> int { ref mut { let mut local = slot; yield local; slot = local } }",
        ),
        "",
    );
}
