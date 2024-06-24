mod common;

use test_log::test;

use common::{run, unit};
use painturscript::value::Value;

#[test]
fn logic_and_comparison() {
    assert_eq!(run("1 < 2 and 2 < 3"), bool!(true));
    assert_eq!(run("1 < 2 and 2 > 3"), bool!(false));
    assert_eq!(run("1 < 2 or 2 > 3"), bool!(true));
    assert_eq!(run("1 > 2 or 2 > 3"), bool!(false));
    assert_eq!(run("1 < 2 and 2 < 3 and 3 < 4"), bool!(true));
    assert_eq!(run("1 < 2 and 2 < 3 and 3 > 4"), bool!(false));
    assert_eq!(run("1 < 2 or 2 > 3 or 3 < 4"), bool!(true));
    assert_eq!(run("1 > 2 or 2 > 3 or 3 < 4"), bool!(true));
    assert_eq!(run("1 > 2 or 2 > 3 or 3 > 4"), bool!(false));
    assert_eq!(run("1 < 2 and 2 < 3 or 3 < 4"), bool!(true));
    assert_eq!(run("1 < 2 and 2 > 3 or 3 < 4"), bool!(true));
    assert_eq!(run("1 < 2 and 2 > 3 or 3 > 4"), bool!(false));
    assert_eq!(run("1 > 2 and 2 < 3 or 3 < 4"), bool!(true));
    assert_eq!(run("1 > 2 and 2 < 3 or 3 > 4"), bool!(false));
    assert_eq!(run("1 > 2 and 2 > 3 or 3 < 4"), bool!(true));
    assert_eq!(run("1 > 2 and 2 > 3 or 3 > 4"), bool!(false));
    assert_eq!(run("1 < 2 or 2 < 3 and 3 < 4"), bool!(true));
    assert_eq!(run("1 < 2 or 2 < 3 and 3 > 4"), bool!(true));
    assert_eq!(run("1 < 2 or 2 > 3 and 3 < 4"), bool!(true));
    assert_eq!(run("1 < 2 or 2 > 3 and 3 > 4"), bool!(true));
    assert_eq!(run("1 > 2 or 2 < 3 and 3 < 4"), bool!(true));
    assert_eq!(run("1 > 2 or 2 < 3 and 3 > 4"), bool!(false));
    assert_eq!(run("1 > 2 or 2 > 3 and 3 < 4"), bool!(false));
    assert_eq!(run("1 > 2 or 2 > 3 and 3 > 4"), bool!(false));
    assert_eq!(run("(1 < 2 or 2 < 3) and 3 < 4"), bool!(true));
    assert_eq!(run("(1 < 2 or 2 < 3) and 3 > 4"), bool!(false));
    assert_eq!(run("(1 < 2 or 2 > 3) and 3 < 4"), bool!(true));
    assert_eq!(run("(1 < 2 or 2 > 3) and 3 > 4"), bool!(false));
    assert_eq!(run("(1 > 2 or 2 < 3) and 3 < 4"), bool!(true));
    assert_eq!(run("(1 > 2 or 2 < 3) and 3 > 4"), bool!(false));
    assert_eq!(run("(1 > 2 or 2 > 3) and 3 < 4"), bool!(false));
    assert_eq!(run("(1 > 2 or 2 > 3) and 3 > 4"), bool!(false));
}

#[test]
fn lambdas_in_containers() {
    assert_eq!(run("(|| 1,).0()"), int!(1));
    assert_eq!(run("[|| 1][0]()"), int!(1));
    assert_eq!(run("let i = 0; [|| 1][i]()"), int!(1));
    assert_eq!(run("let i = 0; [|| 1][i + 0]()"), int!(1));
    assert_eq!(
        run("let f = ([|i| i + 1, |x| x*x], 3); let i = 1; f.0[0](f.0[i](f.1))"),
        int!(10)
    );
}

#[test]
fn exprs_in_match() {
    assert_eq!(
        run("match 0 { 0 => let a = 1; a, _ => let a = 2; 2 }"),
        int!(1)
    );
    assert_eq!(
        run("match 5 { 0 => let a = 1; a, _ => let a = 2; 2 }"),
        int!(2)
    );
    assert_eq!(
        run("match 0 { 0 => |x| x * 2, _ => |x| x * x } (3)"),
        int!(6)
    );
    assert_eq!(
        run("match 1 { 0 => |x| x * 2, _ => |x| x * x } (3)"),
        int!(9)
    );
    assert_eq!(run("match 0 { 0 => (1,2), _ => (2,3) }"), int_tuple!(1, 2));
    assert_eq!(run("match 1 { 0 => (1,2), _ => (2,3) }"), int_tuple!(2, 3));
}

#[test]
fn stuff_in_single_if() {
    assert_eq!(run("var a = 0; if true { a = a + 1}; a"), int!(1));
    assert_eq!(
        run("var a = [1]; if true { a[-1] = a[0] + 1 }; a"),
        int_a![2]
    );
}

#[test]
fn array_and_let_polymorphism() {
    assert_eq!(
        run("let f = || []; var a = f(); array_append(a, 1); a[0]"),
        int!(1)
    );
    // FIXME: this should fail with access error
    // assert_eq!(run("let f = || []; let a = f(); array_append(a, 1); a[0]"), int!(1));
}

#[test]
fn array_access_in_module_functions() {
    assert_eq!(run("fn p(a) { let x = a[0] }"), unit());
    assert_eq!(run("fn p(a) { let x = a[0]; x }"), unit());
    assert_eq!(run("fn p(a, i) { let x = a[i]; 0 }"), unit());
}
