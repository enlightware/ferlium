use test_log::test;

use super::common::{fail_compilation, run};
use painturscript::{std::array::Array, value::Value};

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
