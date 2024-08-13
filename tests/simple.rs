mod common;

use test_log::test;

use common::{fail_compilation, fail_run, run, unit};
use painturscript::{error::RuntimeError, std::array::Array, value::Value};

#[test]
fn whitespaces() {
    assert_eq!(run(""), unit());
    assert_eq!(run(" "), unit());
    assert_eq!(run("\t"), unit());
    assert_eq!(run(" \t"), unit());
    assert_eq!(run("\t "), unit());
    assert_eq!(run("\t \t  \t\t\t"), unit());
}

#[test]
fn literals() {
    assert_eq!(run("42"), int!(42));
    assert_eq!(run("true"), bool!(true));
    assert_eq!(run("false"), bool!(false));
}

#[test]
fn equalities() {
    assert_eq!(run("42 == 42"), bool!(true));
    assert_eq!(run("41 == 42"), bool!(false));
    assert_eq!(run("42 != 42"), bool!(false));
    assert_eq!(run("41 != 42"), bool!(true));
    fail_compilation("1 == true").expect_is_not_subtype("bool", "int");
    assert_eq!(run("true == true"), bool!(true));
    assert_eq!(run("true == false"), bool!(false));
    assert_eq!(run("true != true"), bool!(false));
    assert_eq!(run("true != false"), bool!(true));
    assert_eq!(run("() == ()"), bool!(true));
    assert_eq!(run("() != ()"), bool!(false));
    fail_compilation("() == (1,)").expect_is_not_subtype("(int)", "()");
    assert_eq!(run("(1,) == (1,)"), bool!(true));
    assert_eq!(run("(1,) != (1,)"), bool!(false));
    assert_eq!(run("(1,) == (2,)"), bool!(false));
    assert_eq!(run("(1,) != (2,)"), bool!(true));
    assert_eq!(run("(1,true) == (1,true)"), bool!(true));
    assert_eq!(run("(1,true) != (1,true)"), bool!(false));
    assert_eq!(run("(1,true) == (2,true)"), bool!(false));
    assert_eq!(run("(1,true) != (2,true)"), bool!(true));
    assert_eq!(run("(1,true) == (1,false)"), bool!(false));
    assert_eq!(run("(1,true) != (1,false)"), bool!(true));
    fail_compilation("[] == []").expect_unbound_ty_var();
    fail_compilation("[] != []").expect_unbound_ty_var();
    assert_eq!(run("[] == [1]"), bool!(false));
    assert_eq!(run("[] != [1]"), bool!(true));
    assert_eq!(run("[1] == [1]"), bool!(true));
    assert_eq!(run("[1] != [1]"), bool!(false));
    assert_eq!(run("[1] == [2]"), bool!(false));
    assert_eq!(run("[1] != [2]"), bool!(true));
    assert_eq!(run("let a = [1, 1]; a[0] == a[1]"), bool!(true));
    assert_eq!(run("let a = [1, 1]; a[0] != a[1]"), bool!(false));
}

#[test]
fn local_variables() {
    assert_eq!(run("let a = 1 ; a"), int!(1));
    assert_eq!(run("var a = 1 ; a"), int!(1));
    assert_eq!(run("var a = 1 ; a = 2; a"), int!(2));
    assert_eq!(run("let a = true ; a"), bool!(true));
    assert_eq!(run("var a = true ; a"), bool!(true));
    assert_eq!(run("var a = true ; a = false; a"), bool!(false));
    assert_eq!(run("var a = [1, 2]; a = [3, 4, 5]; a"), int_a![3, 4, 5]);
    assert_eq!(run("var a = [1, 2]; a = [3]; a == [3]"), bool!(true));
    assert_eq!(
        run("var a = (1, true); a = (2, false); a == (2, false)"),
        bool!(true)
    );
    assert_eq!(run("let f = || 1; let a = f(); a"), int!(1));
}

#[test]
fn mutability() {
    assert_eq!(run("var a = 1 ; a = 2; a"), int!(2));
    fail_compilation("let a = 1 ; a = 2; a").expect_must_be_mutable();
    assert_eq!(run("var a = (1,) ; a.0 = 2; a.0"), int!(2));
    fail_compilation("let a = (1,) ; a.0 = 2; a.0").expect_must_be_mutable();
    assert_eq!(run("var a = [1] ; a[0] = 2; a[0]"), int!(2));
    fail_compilation("let a = [1] ; a[0] = 2; a[0]").expect_must_be_mutable();
    assert_eq!(run("var a = ([1], 1) ; a.0[0] = 2; a.0[0]"), int!(2));
    fail_compilation("let a = ([1], 1) ; a.0[0] = 2; a.0[0]").expect_must_be_mutable();
}

#[test]
fn logic_operators() {
    assert_eq!(run("not true"), bool!(false));
    assert_eq!(run("not false"), bool!(true));
    assert_eq!(run("not not true"), bool!(true));
    assert_eq!(run("not not false"), bool!(false));
    assert_eq!(run("not not not true"), bool!(false));
    assert_eq!(run("not not not false"), bool!(true));
    assert_eq!(run("true or false"), bool!(true));
    assert_eq!(run("true and false"), bool!(false));
    assert_eq!(run("true or true and false"), bool!(true));
    assert_eq!(run("(true or true) and false"), bool!(false));
}

#[test]
fn arithmetic_operators() {
    assert_eq!(run("1+2"), int!(3));
    assert_eq!(run("  1  + 2 "), int!(3));
    assert_eq!(run("3*2"), int!(6));
    assert_eq!(run("7/2"), int!(3));
    assert_eq!(run("1-4"), int!(-3));
    assert_eq!(run("-1"), int!(-1));
    assert_eq!(run("--1"), int!(1));
    assert_eq!(run("---1"), int!(-1));
    assert_eq!(run("1---5"), int!(-4));
    assert_eq!(run("1+--5"), int!(6));
    assert_eq!(run("0-2-2"), int!(-4));
    assert_eq!(run("0-(2-2)"), int!(0));
    assert_eq!(run("1+2*3"), int!(7));
    assert_eq!(run("12/3/2"), int!(2));
    assert_eq!(run("12/(3/2)"), int!(12));
    assert_eq!(run("0%3"), int!(0));
    assert_eq!(run("1%3"), int!(1));
    assert_eq!(run("2%3"), int!(2));
    assert_eq!(run("3%3"), int!(0));
    assert_eq!(run("4%3"), int!(1));
    assert_eq!(run("5%3"), int!(2));
    assert_eq!(run("-1%3"), int!(-1));
    assert_eq!(run("-2%3"), int!(-2));
    assert_eq!(run("-3%3"), int!(-0));
    assert_eq!(run("-4%3"), int!(-1));
    assert_eq!(run("-5%3"), int!(-2));
}

#[test]
fn comparison_operators() {
    assert_eq!(run("1 < 2"), bool!(true));
    assert_eq!(run("1 <= 2"), bool!(true));
    assert_eq!(run("1 > 2"), bool!(false));
    assert_eq!(run("1 >= 2"), bool!(false));
    assert_eq!(run("1 != 2"), bool!(true));
    assert_eq!(run("1 == 2"), bool!(false));
    assert_eq!(run("2 < 2"), bool!(false));
    assert_eq!(run("2 <= 2"), bool!(true));
    assert_eq!(run("2 > 2"), bool!(false));
    assert_eq!(run("2 >= 2"), bool!(true));
    assert_eq!(run("2 != 2"), bool!(false));
    assert_eq!(run("2 == 2"), bool!(true));
}

#[test]
fn expression_grouping() {
    assert_eq!(run("(1)"), int!(1));
    assert_eq!(run("((1))"), int!(1));
    assert_eq!(run("(((1)))"), int!(1));
    assert_eq!(run("(((1)))+((2))"), int!(3));
    assert_eq!(run("1 + (2 * 3)"), int!(7));
    assert_eq!(run("(1 + 2) * 3"), int!(9));
    assert_eq!(run("1 + 2 * 3"), int!(7));
    assert_eq!(run("1 * 2 + 3"), int!(5));
    assert_eq!(run("1 * (2 + 3)"), int!(5));
}

#[test]
fn if_expr() {
    assert_eq!(run("if 1 < 2 { 1 } else { 2 }"), int!(1));
    assert_eq!(run("if 1 <= 2 { 1 } else { 2 }"), int!(1));
    assert_eq!(run("if 1 > 2 { 1 } else { 2 }"), int!(2));
    assert_eq!(run("if 1 >= 2 { 1 } else { 2 }"), int!(2));
    assert_eq!(run("if 1 != 2 { 1 } else { 2 }"), int!(1));
    assert_eq!(run("if 1 == 2 { 1 } else { 2 }"), int!(2));
    assert_eq!(run("if 2 < 2 { 1 } else { 2 }"), int!(2));
    assert_eq!(run("if 2 <= 2 { 1 } else { 2 }"), int!(1));
    assert_eq!(run("if 2 > 2 { 1 } else { 2 }"), int!(2));
    assert_eq!(run("if 2 >= 2 { 1 } else { 2 }"), int!(1));
    assert_eq!(run("if 2 != 2 { 1 } else { 2 }"), int!(2));
    assert_eq!(run("if 2 == 2 { 1 } else { 2 }"), int!(1));
}

#[test]
fn match_expr() {
    assert_eq!(run("match true { true => 0, _ => 1 }"), int!(0));
    assert_eq!(run("match false { true => 0, _ => 1 }"), int!(1));
    assert_eq!(run("match true { true => 0, _ => 1, }"), int!(0));
    assert_eq!(run("match true { false => 1, true => 0 }"), int!(0));
    assert_eq!(run("match true { false => 1, true => 0, }"), int!(0));
    assert_eq!(run("let a = 0; match a { 0 => 1, _ => 3 }"), int!(1));
    assert_eq!(run("let a = 1; match a { 0 => 1, _ => 3 }"), int!(3));
    assert_eq!(
        run("let a = 0; match a { 0 => 1, 1 => 2, _ => 3 }"),
        int!(1)
    );
    assert_eq!(
        run("let a = 1; match a { 0 => 1, 1 => 2, _ => 3 }"),
        int!(2)
    );
    assert_eq!(
        run("let a = 5; match a { 0 => 1, 1 => 2, _ => 3 }"),
        int!(3)
    );
    // TODO: add more complex literals (tuples, array) once optimisation is in place
}

#[test]
fn tuple_creation() {
    assert_eq!(run("()"), unit());
    assert_eq!(run("(1,)"), int_tuple!(1));
    assert_eq!(run("(1, 2)"), int_tuple!(1, 2));
    assert_eq!(run("(1, 2, )"), int_tuple!(1, 2));
    assert_eq!(run("(1, 1)"), int_tuple!(1, 1));
    assert_eq!(run("(3, 1, 7)"), int_tuple!(3, 1, 7));
}

#[test]
fn tuple_projection() {
    assert_eq!(run("(1,).0"), int!(1));
    assert_eq!(run("(1,2).1"), int!(2));
    assert_eq!(run("(1,(3, (2, 4, 5))).1.1.2"), int!(5));
    assert_eq!(run("let a = (1,2); a.0"), int!(1));
    assert_eq!(run("let a = (1,2); a.1"), int!(2));
    assert_eq!(run("let f = || (1,2); f().1"), int!(2));
    assert_eq!(
        run("let f = |x, y| (y == x.1.0); f((1,(2,1)), 2)"),
        bool!(true)
    );
    assert_eq!(
        run("let f = |x, y| (x.1, x.1.0, y == x.1); f((1,(2,1)), (2,1)); ()"),
        unit()
    );
    assert_eq!(run("fn f(v) { v.1.2.3 } ()"), unit());
}

#[test]
fn lambda() {
    assert_eq!(run("let f = || 1; f()"), int!(1));
    assert_eq!(run("let f = |x| x; f(1)"), int!(1));
    assert_eq!(run("let f = |x,| x; f(1)"), int!(1));
    assert_eq!(run("let f = |x, y| x + y; f(1, 2)"), int!(3));
    assert_eq!(run("let f = |x, y,| x + y; f(1, 2)"), int!(3));
    assert_eq!(run("let f = |x, y| x + y; f(1, f(2, 3))"), int!(6));
    assert_eq!(run("let f = |x, y| x + y; f(f(1, 2), 3)"), int!(6));
    assert_eq!(run("let f = |x, y| x + y; f(f(1, 2), f(3, 4))"), int!(10));
    assert_eq!(
        run("let sq = |x| x * x; let inc = |x| x + 1; sq(inc(inc(2)))"),
        int!(16)
    );
    assert_eq!(run("let id = |x| x; id(1); id(true)"), bool!(true));
    assert_eq!(
        run("let d = |x, y| (x, y + 1); d(true, 1); d(1, 2)"),
        int_tuple!(1, 3)
    );
    assert_eq!(run("(||1)()"), int!(1));
    assert_eq!(run("(|x| x.1)((1,2))"), int!(2));
}

#[test]
fn assignment() {
    assert_eq!(run("let a = 1; a"), int!(1));
    assert_eq!(run("var a = 1; a = 2"), unit());
    assert_eq!(run("var a = 1; a = 2; a"), int!(2));
    assert_eq!(run("var a = 1; let b = 2; a = b; a"), int!(2));
    assert_eq!(run("var a = 1; let b = 2; a = b; b"), int!(2));
    assert_eq!(run("var a = 1; var b = 2; a = b; b = a; b"), int!(2));
    assert_eq!(run("var a = (1, 2); a.0 = 3; a"), int_tuple!(3, 2));
    assert_eq!(run("var a = ((1, 2), 3); a.0.1 = 5; a.0"), int_tuple!(1, 5));
    assert_eq!(run("var a = [1, 2]; a[0] = 3; a"), int_a![3, 2]);
    assert_eq!(
        run("var a = [[1, 2], [3, 4]]; a[0][1] = 5; a[0]"),
        int_a![1, 5]
    );
}

#[test]
fn mutability_soundness() {
    fail_compilation("let f = |x| (x[0] = 1); let a = [1]; f(a)").expect_must_be_mutable();
    // TODO: add borrow checker tests
}

#[test]
fn for_loops() {
    assert_eq!(run("for i in 0..3 { () }"), unit());
    assert_eq!(run("var s = 0; for i in 1..4 { s = s + i }; s"), int!(6));
    assert_eq!(run("var s = 0; for i in -1..-4 { s = s + i }; s"), int!(-6));
    assert_eq!(
        run("var a = []; for i in 2..5 { array_append(a, i) }; a"),
        int_a![2, 3, 4]
    );
    assert_eq!(
        run("var a = []; for i in 5..2 { array_append(a, i) }; a"),
        int_a![5, 4, 3]
    );
}

#[test]
fn borrow_checker() {
    let swap_fn = "fn swap(a, b) { let temp = b; b = a; a = temp }";
    assert_eq!(run(&format!("{swap_fn} var a = [0, 1]; swap(a[0], a[1]); a")), int_a![1, 0]);
    fail_compilation(&format!("{swap_fn} var a = [0, 1]; swap(a[0], a[0]); a")).expect_mutable_paths_overlap();
    fail_compilation(&format!("{swap_fn} var a = [0, 1]; let i = 0; swap(a[0], a[i]); a")).expect_mutable_paths_overlap();
    assert_eq!(run(&format!("{swap_fn} var a = [0]; var b = [1]; swap(a[0], b[0]); a")), int_a![1]);
    assert_eq!(run(&format!("{swap_fn} var a = [0]; var b = [1]; swap(a[a[0]], b[0]); a")), int_a![1]);
    assert_eq!(run(&format!("{swap_fn} var a = [0]; var b = [1]; swap(a[a[0]], b[a[0]]); a")), int_a![1]);
    assert_eq!(run(&format!("{swap_fn} var a = ((0,1),2); swap(a.0.1, a.1); a.0")), int_tuple!(0, 2));
    assert_eq!(run(&format!("{swap_fn} var a = ((0,1),2); swap(a.0.1, a.0.0); a.0")), int_tuple!(1,0 ));
    fail_compilation(&format!("{swap_fn} var a = ((0,1),2); swap(a.0, a.0); a.0")).expect_mutable_paths_overlap();
}

#[test]
fn execution_errors() {
    use RuntimeError::*;
    assert_eq!(fail_run("1 / 0"), DivisionByZero);
    assert_eq!(fail_run("let v = || 0; 1 / v()"), DivisionByZero);
    assert_eq!(fail_run("1 % 0"), RemainderByZero);
    assert_eq!(fail_run("let v = || 0; 1 % v()"), RemainderByZero);
    assert_eq!(
        fail_run("[1][1]"),
        ArrayAccessOutOfBounds { index: 1, len: 1 }
    );
    assert_eq!(
        fail_run("let a = [1, 2]; a[3]"),
        ArrayAccessOutOfBounds { index: 3, len: 2 }
    );
    assert_eq!(
        fail_run("let a = [1, 2]; a[-3]"),
        ArrayAccessOutOfBounds { index: -3, len: 2 }
    );
    assert_eq!(
        fail_run("var a = [1, 2]; a[3] = 0"),
        ArrayAccessOutOfBounds { index: 3, len: 2 }
    );
    assert_eq!(
        fail_run("var a = [1, 2]; a[-3] = 0"),
        ArrayAccessOutOfBounds { index: -3, len: 2 }
    );
    assert_eq!(
        fail_run("let i = || 3; let a = [1, 2]; a[i()]"),
        ArrayAccessOutOfBounds { index: 3, len: 2 }
    );
    assert_eq!(
        fail_run("let i = || -3; let a = [1, 2]; a[i()]"),
        ArrayAccessOutOfBounds { index: -3, len: 2 }
    );
    assert_eq!(
        fail_run("let i = || 3; var a = [1, 2]; a[i()] = 0"),
        ArrayAccessOutOfBounds { index: 3, len: 2 }
    );
    assert_eq!(
        fail_run("let i = || -3; var a = [1, 2]; a[i()] = 0"),
        ArrayAccessOutOfBounds { index: -3, len: 2 }
    );
    assert_eq!(
        fail_run("fn rf() { rf() } rf()"),
        RecursionLimitExceeded { limit: 100 }
    );
}

#[test]
fn array_creation() {
    assert_eq!(run("[]"), int_a![]);
    assert_eq!(run("[1]"), int_a![1]);
    assert_eq!(run("[1,]"), int_a![1]);
    assert_eq!(run("[1, 2]"), int_a![1, 2]);
    assert_eq!(run("[1, 2,]"), int_a![1, 2]);
    assert_eq!(run("[1, 1]"), int_a![1, 1]);
    assert_eq!(run("[3, 1, 7]"), int_a![3, 1, 7]);
}

#[test]
fn array_index() {
    assert_eq!(run("[1][0]"), int!(1));
    assert_eq!(run("[1][-1]"), int!(1));
    assert_eq!(run("[1, 3][0]"), int!(1));
    assert_eq!(run("[1, 3][1]"), int!(3));
    assert_eq!(run("[1, 3][-1]"), int!(3));
    assert_eq!(run("[1, 3][-2]"), int!(1));
    assert_eq!(run("[[1, 2], [3, 4]][1][0]"), int!(3));
    assert_eq!(run("let a = [1, 3]; a[0]"), int!(1));
    assert_eq!(run("let a = [1, 3]; a[1]"), int!(3));
    assert_eq!(run("let i = 0; [1, 3][i]"), int!(1));
    assert_eq!(run("let i = 1; [1, 3][i]"), int!(3));
    assert_eq!(run("let i = -1; [1, 3][i]"), int!(3));
    assert_eq!(run("let i = -2; [1, 3][i]"), int!(1));
    assert_eq!(run("let i = 0; let j = 1; [[1, 2], [3, 4]][i][j]"), int!(2));
}

// TODO: add array from iterator

#[test]
fn array_append() {
    assert_eq!(run("var a = []; array_append(a, 1); a"), int_a![1]);
    assert_eq!(run("var a = [1]; array_append(a, 1); a"), int_a![1, 1]);
    assert_eq!(run("var a = [2]; array_append(a, 1); a"), int_a![2, 1]);
}

#[test]
fn array_prepend() {
    assert_eq!(run("var a = []; array_prepend(a, 1); a"), int_a![1]);
    assert_eq!(run("var a = [1]; array_prepend(a, 1); a"), int_a![1, 1]);
    assert_eq!(run("var a = [2]; array_prepend(a, 1); a"), int_a![1, 2]);
}

#[test]
fn array_len() {
    fail_compilation("let a = []; array_len(a)").expect_unbound_ty_var();
    assert_eq!(run("let a = [1]; array_len(a)"), int!(1));
    assert_eq!(run("let a = [1, 2]; array_len(a)"), int!(2));
    assert_eq!(run("let a = [[1], [1, 1]]; array_len(a)"), int!(2));
    assert_eq!(run("let a = [1, 1, 1]; array_len(a)"), int!(3));
}

#[test]
fn array_concat() {
    assert_eq!(run("array_concat([], [])"), int_a![]);
    assert_eq!(run("array_concat([1], [])"), int_a![1]);
    assert_eq!(run("array_concat([], [1])"), int_a![1]);
    assert_eq!(run("array_concat([1], [2])"), int_a![1, 2]);
    assert_eq!(run("array_concat([1, 2], [3])"), int_a![1, 2, 3]);
    assert_eq!(run("array_concat([1], [2, 3])"), int_a![1, 2, 3]);
    assert_eq!(run("array_concat([1, 2], [3, 4])"), int_a![1, 2, 3, 4]);
    assert_eq!(
        run("array_concat([1, 2], [3, 4, 5])"),
        int_a![1, 2, 3, 4, 5]
    );
}

#[test]
fn modules() {
    assert_eq!(run("fn a(x) { x }"), unit());
    assert_eq!(run("fn a(x) { x } a(1)"), int!(1));
    assert_eq!(run("fn a(x) { x + 1 } a(1)"), int!(2));
    assert_eq!(
        run("fn d(x) { 2 * x } fn s(x) { x + 1 } d(s(s(1)))"),
        int!(6)
    );
}

#[test]
fn recursive_functions() {
    assert_eq!(
        run("fn fact(x) { if x > 1 { x * fact(x-1) } else { 1 } } fact(5)"),
        int!(120)
    );
    assert_eq!(
        run(r#"fn is_even(n) {
                if n == 0 {
                    true
                } else {
                    is_odd(n - 1)
                }
            }

            fn is_odd(n) {
                if n == 0 {
                    false
                } else {
                    is_even(n - 1)
                }
            }

            is_even(10)"#),
        bool!(true)
    );
    assert_eq!(run("fn f(a) { let p = g(a) } fn g(a) { 0 }"), unit());
}
