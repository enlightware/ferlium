use test_log::test;

use indoc::indoc;

use crate::harness::{TestSession};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
fn simple_functions() {
    let mut session = TestSession::new();
    assert_eq!(
        session.emit_ssa("fn t(x:int) {x}"),
        r#"u!("t")
fn t:
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
fn a0:
  0:
    %r0 = call imported function std::<impl Num for int>::from_int (slot #0)(i32 1)
    %r1 = call imported function std::<impl Num for int>::add (slot #1)(%p0, %r0)
    %r2 = ret %r1
"#
    );

    assert_eq!(
        session.emit_ssa("fn a0(x:int) {let y:int = 2 * x; y}"),
        r#"u!("a0")
fn a0:
  0:
    %r0 = call imported function std::<impl Num for int>::from_int (slot #0)(i32 2)
    %r1 = call imported function std::<impl Num for int>::mul (slot #1)(%r0, %p0)
    %r2 = ret %r1
"#
    );
}

#[test]
fn match_case_functions() {
    let mut session = TestSession::new();

    assert_eq!(
        session.emit_ssa("fn a0(x:int) {if true {x} else {2}}"),
        r#"u!("a0")
fn a0:
  0:
    %r0 = alloca Type { world: Some(0), index: 7 }
    %r1 = br 1
  1:
    %r2 = comp_eq i1 1 i1 1
    %r3 = condbr %r2, %b2, &b3
  2:
    %r4 = store %p0 to %r0
    %r5 = br 4
  3:
    %r6 = call imported function std::<impl Num for int>::from_int (slot #0)(i32 2)
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
fn a0:
  0:
    %r0 = alloca Type { world: Some(0), index: 7 }
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
    %r8 = call imported function std::<impl Num for int>::from_int (slot #0)(i32 1)
    %r9 = call imported function std::<impl Num for int>::sub (slot #1)(%p0, %r8)
    %r10 = store %r9 to %r0
    %r11 = br 6
  5:
    %r12 = call imported function std::<impl Num for int>::from_int (slot #0)(i32 1)
    %r13 = call imported function std::<impl Num for int>::neg (slot #2)(%r12)
    %r14 = store %r13 to %r0
    %r15 = br 6
  6:
    %r16 = load %r0
    %r17 = ret %r16
"#
    );
}

#[test]
fn generic_functions() {
    let mut sessions = TestSession::new();

    assert_eq!(
        sessions.emit_ssa("fn a0(x) { x < 2 }"),
        r#"u!("a0")
fn a0:
  0:
    %r0 = project 6 from %p0
    %r1 = call %r0(i32 2)
    %r2 = call imported function std::lt (slot #0)(%p1, %p2, %r1)
    %r3 = ret %r2
"#)
}

#[test]
fn user_function_call() {
    let mut sessions = TestSession::new();

    assert_eq!(
        sessions.emit_ssa("fn a0(x: int) {a0(x)}"),
        r#"u!("a0")
fn a0:
  0:
    %r0 = call local function a0 (#0)(%p0)
    %r1 = ret %r0
"#
    )
}


#[test]
fn factorial() {
    let mut sessions = TestSession::new();

    assert_eq!(
      sessions.emit_ssa("fn factorial(x: int) {if x > 1 {x * factorial(x - 1)} else {1}}"),
      r#"u!("factorial")
fn factorial:
  0:
    %r0 = call imported function std::<impl Num for int>::from_int (slot #1)(i32 1)
    %r1 = call imported function std::gt (slot #0)((local function Ord<0-7>::cmp (#42)), %p0, %r0)
    %r2 = alloca Type { world: Some(0), index: 7 }
    %r3 = br 1
  1:
    %r4 = comp_eq %r1 i1 1
    %r5 = condbr %r4, %b2, &b3
  2:
    %r6 = call imported function std::<impl Num for int>::from_int (slot #1)(i32 1)
    %r7 = call imported function std::<impl Num for int>::sub (slot #2)(%p0, %r6)
    %r8 = call local function factorial (#0)(%r7)
    %r9 = call imported function std::<impl Num for int>::mul (slot #3)(%p0, %r8)
    %r10 = store %r9 to %r2
    %r11 = br 4
  3:
    %r12 = call imported function std::<impl Num for int>::from_int (slot #1)(i32 1)
    %r13 = store %r12 to %r2
    %r14 = br 4
  4:
    %r15 = load %r2
    %r16 = ret %r15
"#
    );
}
