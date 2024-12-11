use test_log::test;

use crate::effects::test_mod as test_mod_for_effects;

use super::common::{fail_compilation, run};
use painturscript::{
    effects::{effect, no_effects, PrimitiveEffect},
    std::array::Array,
    value::Value,
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

// TODO: add array from iterator

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_append() {
    assert_eq!(run("let mut a = []; array_append(a, 1); a"), int_a![1]);
    assert_eq!(run("let mut a = [1]; array_append(a, 1); a"), int_a![1, 1]);
    assert_eq!(run("let mut a = [2]; array_append(a, 1); a"), int_a![2, 1]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_prepend() {
    assert_eq!(run("let mut a = []; array_prepend(a, 1); a"), int_a![1]);
    assert_eq!(run("let mut a = [1]; array_prepend(a, 1); a"), int_a![1, 1]);
    assert_eq!(run("let mut a = [2]; array_prepend(a, 1); a"), int_a![1, 2]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_len() {
    fail_compilation("let a = []; array_len(a)").expect_unbound_ty_var();
    assert_eq!(run("let a = [1]; array_len(a)"), int!(1));
    assert_eq!(run("let a = [1, 2]; array_len(a)"), int!(2));
    assert_eq!(run("let a = [[1], [1, 1]]; array_len(a)"), int!(2));
    assert_eq!(run("let a = [1, 1, 1]; array_len(a)"), int!(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
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
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_map() {
    assert_eq!(run("array_map([1], |x| x)"), int_a![1]);
    assert_eq!(run("array_map([1], |x| x + 1)"), int_a![2]);
    assert_eq!(run("array_map([1, 2, 3], |x| x + 1)"), int_a![2, 3, 4]);
    assert_eq!(
        run("array_map([1, 2, 3], |x| x >= 2)"),
        bool_a![false, true, true]
    );
    assert_eq!(
        run("array_map([(1, 2), (2, 3), (3, 4)], |v| v.0 + v.1)"),
        int_a![3, 5, 7]
    );
    use PrimitiveEffect::*;
    test_mod_for_effects(
        "fn f() { let a = [1]; array_map(a, |v| { v >= 1 }) }",
        "f",
        no_effects(),
    );
    test_mod_for_effects(
        "fn f() { let a = [1]; array_map(a, |v| { effects::read(); v >= 1 }) }",
        "f",
        effect(Read),
    );
}
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_any() {
    assert_eq!(run("array_any([], |x| x == 1)"), bool!(false));
    assert_eq!(run("array_any([1], |x| x == 1)"), bool!(true));
    assert_eq!(run("array_any([1, 2, 3], |x| x == 1)"), bool!(true));
    assert_eq!(run("array_any([1, 2, 3], |x| x >= 2)"), bool!(true));
    assert_eq!(run("array_any([1, 2, 3], |x| x >= 4)"), bool!(false));
    use PrimitiveEffect::*;
    test_mod_for_effects(
        "fn f() { let a = [1]; array_any(a, |v| { v >= 1 }) }",
        "f",
        no_effects(),
    );
    test_mod_for_effects(
        "fn f() { let a = [1]; array_any(a, |v| { effects::read(); v >= 1 }) }",
        "f",
        effect(Read),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_all() {
    assert_eq!(run("array_all([], |x| x == 1)"), bool!(true));
    assert_eq!(run("array_all([1], |x| x == 1)"), bool!(true));
    assert_eq!(run("array_all([1, 2, 3], |x| x == 1)"), bool!(false));
    assert_eq!(run("array_all([1, 2, 3], |x| x >= 1)"), bool!(true));
    assert_eq!(run("array_all([1, 2, 3], |x| x >= 2)"), bool!(false));
    use PrimitiveEffect::*;
    test_mod_for_effects(
        "fn f() { let a = [1]; array_all(a, |v| { v >= 1 }) }",
        "f",
        no_effects(),
    );
    test_mod_for_effects(
        "fn f() { let a = [1]; array_all(a, |v| { effects::read(); v >= 1 }) }",
        "f",
        effect(Read),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_concat() {
    assert_eq!(run(r#"string_concat("", "")"#), string!(""));
    assert_eq!(
        run(r#"string_concat("hello", "world")"#),
        string!("helloworld")
    );
    assert_eq!(
        run(r#"string_concat("hello", " world")"#),
        string!("hello world")
    );
    assert_eq!(
        run(r#"string_concat("hello ", "world")"#),
        string!("hello world")
    );
    assert_eq!(
        run(r#"string_concat("hello ", " world")"#),
        string!("hello  world")
    );
    assert_eq!(
        run(r#"string_concat("hello ", "world!")"#),
        string!("hello world!")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_push_str() {
    assert_eq!(
        run(r#"let mut s = ""; string_push_str(s, ""); s"#),
        string!("")
    );
    assert_eq!(
        run(r#"let mut s = ""; string_push_str(s, "hello"); s"#),
        string!("hello")
    );
    assert_eq!(
        run(r#"let mut s = "hello"; string_push_str(s, " world"); s"#),
        string!("hello world")
    );
    assert_eq!(
        run(r#"let mut s = "hello"; string_push_str(s, " world!"); s"#),
        string!("hello world!")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_replace() {
    assert_eq!(
        run(r#"string_replace("hello world", "world", "world!")"#),
        string!("hello world!")
    );
    assert_eq!(
        run(r#"string_replace("hello world", "world", "")"#),
        string!("hello ")
    );
    assert_eq!(
        run(r#"string_replace("hello world", "world", "world")"#),
        string!("hello world")
    );
    assert_eq!(
        run(r#"string_replace("hello world", "world", "world!!")"#),
        string!("hello world!!")
    );
    assert_eq!(
        run(r#"string_replace("hello world and other world are cool", "world", "home")"#),
        string!("hello home and other home are cool")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_sub_string() {
    assert_eq!(run(r#"string_sub_string("hello", 0, 0)"#), string!(""));
    assert_eq!(run(r#"string_sub_string("hello", 3, 0)"#), string!(""));
    assert_eq!(run(r#"string_sub_string("hello", 0, 5)"#), string!("hello"));
    assert_eq!(
        run(r#"string_sub_string("hello", 0, 15)"#),
        string!("hello")
    );
    assert_eq!(
        run(r#"string_sub_string("hello", -5, 5)"#),
        string!("hello")
    );
    assert_eq!(run(r#"string_sub_string("hello", 0, 4)"#), string!("hell"));
    assert_eq!(run(r#"string_sub_string("hello", 0, -1)"#), string!("hell"));
    assert_eq!(run(r#"string_sub_string("hello", 1, 4)"#), string!("ell"));
    assert_eq!(run(r#"string_sub_string("hello", 1, -1)"#), string!("ell"));
    assert_eq!(run(r#"string_sub_string("hello", -4, -2)"#), string!("el"));
}
