use test_log::test;

use indoc::indoc;

use crate::harness::TestSession;

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
    %r0 = call std::Num<0-5>::from_int(i32 1)
    %r1 = call std::Num<0-5>::add(%p0, %r0)
    %r2 = call std::Value<0-5>::drop(%r0)
    %r3 = ret %r1
"#
  );

  assert_eq!(
    session.emit_ssa("fn a0(x:int) {let y:int = 2 * x; y}"),
    r#"u!("a0")
fn a0:
  0:
    %r0 = call std::Num<0-5>::from_int(i32 2)
    %r1 = call std::Num<0-5>::mul(%r0, %p0)
    %r2 = call std::Value<0-5>::drop(%r0)
    %r3 = ret %r1
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
    %r0 = alloca Type { world: Some(0), index: 5 }
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
fn a0:
  0:
    %r0 = alloca Type { world: Some(0), index: 5 }
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
    %r10 = call std::Value<0-5>::drop(%r8)
    %r11 = store %r9 to %r0
    %r12 = br 6
  5:
    %r13 = call std::Num<0-5>::from_int(i32 1)
    %r14 = call std::Num<0-5>::neg(%r13)
    %r15 = call std::Value<0-5>::drop(%r13)
    %r16 = store %r14 to %r0
    %r17 = br 6
  6:
    %r18 = load %r0
    %r19 = ret %r18
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
    %r0 = project 6 from %p1
    %r1 = call %r0(i32 2)
    %r2 = call std::lt(%p0, %r1)
    %r3 = call %p2(%r1)
    %r4 = ret %r2
"#
  )
}

#[test]
fn user_function_call() {
  let mut sessions = TestSession::new();

  assert_eq!(
    sessions.emit_ssa("fn a0(x: int) {a0(x)}"),
    r#"u!("a0")
fn a0:
  0:
    %r0 = call <test>::a0(%p0)
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
    %r0 = call std::Num<0-5>::from_int(i32 1)
    %r1 = call std::gt(%p0, %r0)
    %r2 = call std::Value<0-5>::drop(%r0)
    %r3 = alloca Type { world: Some(0), index: 5 }
    %r4 = br 1
  1:
    %r5 = comp_eq %r1 i1 1
    %r6 = condbr %r5, %b2, &b3
  2:
    %r7 = call std::Num<0-5>::from_int(i32 1)
    %r8 = call std::Num<0-5>::sub(%p0, %r7)
    %r9 = call std::Value<0-5>::drop(%r7)
    %r10 = call <test>::factorial(%r8)
    %r11 = call std::Num<0-5>::mul(%p0, %r10)
    %r12 = call std::Value<0-5>::drop(%r10)
    %r13 = store %r11 to %r3
    %r14 = br 4
  3:
    %r15 = call std::Num<0-5>::from_int(i32 1)
    %r16 = store %r15 to %r3
    %r17 = br 4
  4:
    %r18 = load %r3
    %r19 = ret %r18
"#
  );
}
