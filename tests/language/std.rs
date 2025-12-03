// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;

use crate::{common::variant_0, effects::test_mod as test_mod_for_effects};

use super::common::{bool, fail_compilation, float, int, run, string, variant_t1};
use ferlium::{
    effects::{PrimitiveEffect, effect, no_effects},
    std::option::{none, some},
    value::Value,
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn range_iterators() {
    assert_eq!(
        run("let r = range(0, 2); let mut it = iter(r); (next(it), next(it))"),
        tuple!(variant_t1("Some", int(0)), variant_t1("Some", int(1)))
    );
    assert_eq!(run("len(3..3)"), int(0));
    assert_eq!(run("len(3..4)"), int(1));
    assert_eq!(run("len(3..2)"), int(1));
    assert_eq!(run("is_empty(3..3)"), bool(true));
    assert_eq!(run("is_empty(3..4)"), bool(false));
    assert_eq!(run("is_empty(3..2)"), bool(false));
}

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
fn array_pop_back() {
    assert_eq!(run("let mut a: [int] = []; array_pop_back(a)"), none());
    assert_eq!(run("let mut a = [1]; array_pop_back(a); a"), int_a![]);
    assert_eq!(run("let mut a = [1]; array_pop_back(a)"), some(int(1)));
    assert_eq!(run("let mut a = [1, 2]; array_pop_back(a); a"), int_a![1]);
    assert_eq!(run("let mut a = [1, 2]; array_pop_back(a)"), some(int(2)));
    assert_eq!(
        run("let mut a = [1, 2, 3]; array_pop_back(a); a"),
        int_a![1, 2]
    );
    assert_eq!(
        run("let mut a = [1, 2, 3]; array_pop_back(a)"),
        some(int(3))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_pop_front() {
    assert_eq!(run("let mut a: [int] = []; array_pop_front(a)"), none());
    assert_eq!(run("let mut a = [1]; array_pop_front(a); a"), int_a![]);
    assert_eq!(run("let mut a = [1]; array_pop_front(a)"), some(int(1)));
    assert_eq!(run("let mut a = [1, 2]; array_pop_front(a); a"), int_a![2]);
    assert_eq!(run("let mut a = [1, 2]; array_pop_front(a)"), some(int(1)));
    assert_eq!(
        run("let mut a = [1, 2, 3]; array_pop_front(a); a"),
        int_a![2, 3]
    );
    assert_eq!(
        run("let mut a = [1, 2, 3]; array_pop_front(a)"),
        some(int(1))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_len() {
    fail_compilation("let a = []; array_len(a)").expect_unbound_ty_var();
    assert_eq!(run("let a = [1]; array_len(a)"), int(1));
    assert_eq!(run("let a = [1, 2]; array_len(a)"), int(2));
    assert_eq!(run("let a = [[1], [1, 1]]; array_len(a)"), int(2));
    assert_eq!(run("let a = [1, 1, 1]; array_len(a)"), int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_concat() {
    fail_compilation("array_concat([], [])").expect_unbound_ty_var();
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
    assert_eq!(run("array_any(([]: [int]), |x| x == 1)"), bool(false));
    assert_eq!(run("array_any([1], |x| x == 1)"), bool(true));
    assert_eq!(run("array_any([1, 2, 3], |x| x == 1)"), bool(true));
    assert_eq!(run("array_any([1, 2, 3], |x| x >= 2)"), bool(true));
    assert_eq!(run("array_any([1, 2, 3], |x| x >= 4)"), bool(false));
    use PrimitiveEffect::*;
    test_mod_for_effects(
        "fn f() { let a = [(1: int)]; array_any(a, |v| { v >= 1 }) }",
        "f",
        no_effects(),
    );
    test_mod_for_effects(
        "fn f() { let a = [(1: int)]; array_any(a, |v| { effects::read(); v >= 1 }) }",
        "f",
        effect(Read),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_all() {
    assert_eq!(run("array_all(([]: [int]), |x| x == 1)"), bool(true));
    assert_eq!(run("array_all([1], |x| x == 1)"), bool(true));
    assert_eq!(run("array_all([1, 2, 3], |x| x == 1)"), bool(false));
    assert_eq!(run("array_all([1, 2, 3], |x| x >= 1)"), bool(true));
    assert_eq!(run("array_all([1, 2, 3], |x| x >= 2)"), bool(false));
    use PrimitiveEffect::*;
    test_mod_for_effects(
        "fn f() { let a = [(1: int)]; array_all(a, |v| { v >= 1 }) }",
        "f",
        no_effects(),
    );
    test_mod_for_effects(
        "fn f() { let a = [(1: int)]; array_all(a, |v| { effects::read(); v >= 1 }) }",
        "f",
        effect(Read),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_iterators() {
    assert_eq!(
        run("let a = [1, 2, 3]; let mut it = array_iter(a); (next(it), next(it))"),
        tuple!(variant_t1("Some", int(1)), variant_t1("Some", int(2)))
    );
    assert_eq!(
        run("let a = [1.0, 2.0, 3.0]; let mut it = array_iter(a); (next(it), next(it))"),
        tuple!(
            variant_t1("Some", float(1.0)),
            variant_t1("Some", float(2.0))
        )
    );
    assert_eq!(
        run(
            r#"let a = ["hello", "world"]; let mut it = array_iter(a); (next(it), next(it), next(it))"#
        ),
        tuple!(
            variant_t1("Some", string("hello")),
            variant_t1("Some", string("world")),
            variant_0("None")
        )
    );
    assert_eq!(
        run("let a = [1, 2, 3]; let mut it = iter(a); (next(it), next(it))"),
        tuple!(variant_t1("Some", int(1)), variant_t1("Some", int(2)))
    );
    assert_eq!(
        run("let a = [1.0, 2.0, 3.0]; let mut it = iter(a); (next(it), next(it))"),
        tuple!(
            variant_t1("Some", float(1.0)),
            variant_t1("Some", float(2.0))
        )
    );
    assert_eq!(
        run(r#"let a = ["hello", "world"]; let mut it = iter(a); (next(it), next(it), next(it))"#),
        tuple!(
            variant_t1("Some", string("hello")),
            variant_t1("Some", string("world")),
            variant_0("None")
        )
    );
    assert_eq!(run("len(([]: [int]))"), int(0));
    assert_eq!(run("len([1, 2])"), int(2));
    assert_eq!(run("len([true, false, true])"), int(3));
    assert_eq!(run("is_empty(([]: [int]))"), bool(true));
    assert_eq!(run("is_empty([1, 2])"), bool(false));
    assert_eq!(run("is_empty([true, false, true])"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_casts() {
    // Identity casts
    assert_eq!(run("([1, 2, 3]: [int]) as [int]"), int_a![1, 2, 3]);
    assert_eq!(
        run("([1.0, 2.4, 3.0]: [float]) as [float]"),
        float_a![1.0, 2.4, 3.0]
    );
    // Inner type casts
    assert_eq!(
        run("([1, 2, 3]: [int]) as [float]"),
        float_a![1.0, 2.0, 3.0]
    );
    assert_eq!(run("([1.0, 2.4, 3.0]: [float]) as [int]"), int_a![1, 2, 3]);
    // In functions
    assert_eq!(
        run("fn f(v) { v as [float] } f([1.0, 2.4, 3.0])"),
        float_a![1.0, 2.4, 3.0]
    );
    assert_eq!(
        run("fn f(v) { v as [int] } f([1.0, 2.4, 3.0])"),
        int_a![1, 2, 3]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn reducing_fns() {
    assert_eq!(run("0..2 |> iter() |> any(|x| x > 1)"), bool(false));
    assert_eq!(run("0..2 |> iter() |> any(|x| x >= 1)"), bool(true));
    assert_eq!(run("[0, 1] |> iter() |> any(|x| x > 1)"), bool(false));
    assert_eq!(run("[0, 1] |> iter() |> any(|x| x >= 1)"), bool(true));
    assert_eq!(run("0..2 |> iter() |> all(|x| x > 0)"), bool(false));
    assert_eq!(run("0..2 |> iter() |> all(|x| x >= 0)"), bool(true));
    assert_eq!(run("[0, 1] |> iter() |> all(|x| x > 0)"), bool(false));
    assert_eq!(run("[0, 1] |> iter() |> all(|x| x >= 0)"), bool(true));
    assert_eq!(run("2..5 |> iter() |> count()"), int(3));
    assert_eq!(run("[2, 5] |> iter() |> count()"), int(2));
    assert_eq!(run("[2, 5] |> iter() |> iter() |> count()"), int(2));
    assert_eq!(run("2..5 |> iter() |> sum()"), int(9));
    assert_eq!(run("[2, 5] |> iter() |> sum()"), int(7));
    assert_eq!(run("[2.5, 5] |> iter() |> sum()"), float(7.5));
    assert_eq!(run("[0, 1, 3] |> iter() |> find(|x| x > 1)"), some(int(3)));
    assert_eq!(run("[0, 1, 3] |> iter() |> find(|x| x < 0)"), none());
    assert_eq!(
        run("[0, 1, 3] |> iter() |> position(|x| x > 1)"),
        some(int(2))
    );
    assert_eq!(run("[0, 1, 3] |> iter() |> position(|x| x < 0)"), none());
    assert_eq!(run("[3, 1, 2] |> iter() |> minimum()"), int(1));
    assert_eq!(run("[3.0, 1.0, 2.0] |> iter() |> minimum()"), float(1.0));
    assert_eq!(run("[3, 1, 2] |> iter() |> maximum()"), int(3));
    assert_eq!(run("[3.0, 1.0, 2.0] |> iter() |> maximum()"), float(3.0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn contains() {
    // strings
    assert_eq!(run("contains(\"hello world\", \"world\")"), bool(true));
    assert_eq!(run("contains(\"hello world\", \"world!\")"), bool(false));
    assert_eq!(run("contains(\"hello world\", \"\")"), bool(true));
    assert_eq!(run("contains(\"\", \"\")"), bool(true));
    assert_eq!(run("contains(\"\", \"a\")"), bool(false));
    // arrays
    assert_eq!(run("contains([1, 2, 3], 2)"), bool(true));
    assert_eq!(run("contains([1, 2, 3], 4)"), bool(false));
    fail_compilation("contains([], 1)")
        .into_inner()
        .into_unresolved_constraints()
        .unwrap();
    assert_eq!(run("contains([-3.0], 1.0)"), bool(false));
    assert_eq!(run("contains([-3.0, 3.0, 1.0], 1.0)"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn concat() {
    // strings
    assert_eq!(run(r#"concat("hello", "world")"#), string("helloworld"));
    assert_eq!(run(r#"concat("foo", " bar")"#), string("foo bar"));
    assert_eq!(run(r#"concat("", "")"#), string(""));
    assert_eq!(run(r#"concat("a", "")"#), string("a"));
    assert_eq!(run(r#"concat("", "b")"#), string("b"));
    // arrays
    assert_eq!(run("concat([1, 2], [3, 4])"), int_a![1, 2, 3, 4]);
    // FIXME: Broken due to limitations in type defaulting, tang related
    // to https://github.com/enlightware/ferlium/issues/59
    //assert_eq!(run("concat([], [])"), int_a![]);
    assert_eq!(run("(concat([], []): [int])"), int_a![]);
    assert_eq!(run("concat([1, 2], [])"), int_a![1, 2]);
    assert_eq!(run("concat([], [3, 4])"), int_a![3, 4]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_concat() {
    assert_eq!(run(r#"string_concat("", "")"#), string(""));
    assert_eq!(
        run(r#"string_concat("hello", "world")"#),
        string("helloworld")
    );
    assert_eq!(
        run(r#"string_concat("hello", " world")"#),
        string("hello world")
    );
    assert_eq!(
        run(r#"string_concat("hello ", "world")"#),
        string("hello world")
    );
    assert_eq!(
        run(r#"string_concat("hello ", " world")"#),
        string("hello  world")
    );
    assert_eq!(
        run(r#"string_concat("hello ", "world!")"#),
        string("hello world!")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_push_str() {
    assert_eq!(
        run(r#"let mut s = ""; string_push_str(s, ""); s"#),
        string("")
    );
    assert_eq!(
        run(r#"let mut s = ""; string_push_str(s, "hello"); s"#),
        string("hello")
    );
    assert_eq!(
        run(r#"let mut s = "hello"; string_push_str(s, " world"); s"#),
        string("hello world")
    );
    assert_eq!(
        run(r#"let mut s = "hello"; string_push_str(s, " world!"); s"#),
        string("hello world!")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_replace() {
    assert_eq!(
        run(r#"string_replace("hello world", "world", "world!")"#),
        string("hello world!")
    );
    assert_eq!(
        run(r#"string_replace("hello world", "world", "")"#),
        string("hello ")
    );
    assert_eq!(
        run(r#"string_replace("hello world", "world", "world")"#),
        string("hello world")
    );
    assert_eq!(
        run(r#"string_replace("hello world", "world", "world!!")"#),
        string("hello world!!")
    );
    assert_eq!(
        run(r#"string_replace("hello world and other world are cool", "world", "home")"#),
        string("hello home and other home are cool")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_slice() {
    assert_eq!(run(r#"string_slice("hello", 0, 0)"#), string(""));
    assert_eq!(run(r#"string_slice("hello", 3, 0)"#), string(""));
    assert_eq!(run(r#"string_slice("hello", 0, 5)"#), string("hello"));
    assert_eq!(run(r#"string_slice("hello", 0, 15)"#), string("hello"));
    assert_eq!(run(r#"string_slice("hello", -5, 5)"#), string("hello"));
    assert_eq!(run(r#"string_slice("hello", 0, 4)"#), string("hell"));
    assert_eq!(run(r#"string_slice("hello", 0, -1)"#), string("hell"));
    assert_eq!(run(r#"string_slice("hello", 1, 4)"#), string("ell"));
    assert_eq!(run(r#"string_slice("hello", 1, -1)"#), string("ell"));
    assert_eq!(run(r#"string_slice("hello", -4, -2)"#), string("el"));

    // unicode - now using grapheme-based indices (character positions)
    // "农" is 1 grapheme cluster (1 character)
    assert_eq!(run(r#"string_slice("农", 0, 1)"#), string("农"));
    assert_eq!(run(r#"string_slice("农", 0, 10)"#), string("农")); // clamps to length
    assert_eq!(run(r#"string_slice("农", 1, 2)"#), string("")); // past end
    // "a农" is 2 grapheme clusters
    assert_eq!(run(r#"string_slice("a农", 0, 1)"#), string("a"));
    assert_eq!(run(r#"string_slice("a农", 1, 2)"#), string("农"));
    assert_eq!(run(r#"string_slice("a农", 0, 2)"#), string("a农"));
    // "café" with combining accent (e + combining acute) is 4 graphemes
    assert_eq!(
        run("string_slice(\"cafe\\u{0301}\", 0, 4)"),
        string("cafe\u{0301}")
    );
    assert_eq!(
        run("string_slice(\"cafe\\u{0301}\", 3, 4)"),
        string("e\u{0301}")
    );
    // flag emoji (2 regional indicators = 1 grapheme)
    assert_eq!(run(r#"string_slice("🇫🇷", 0, 1)"#), string("🇫🇷"));
    assert_eq!(run(r#"string_slice("a🇫🇷b", 1, 2)"#), string("🇫🇷"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_len() {
    assert_eq!(run(r#"string_len("")"#), int(0));
    assert_eq!(run(r#"string_len("hello")"#), int(5));
    // unicode - grapheme-based counting
    assert_eq!(run(r#"string_len("农")"#), int(1)); // 1 grapheme, 3 bytes
    assert_eq!(run(r#"string_len("农历新年")"#), int(4)); // 4 graphemes
    assert_eq!(run("string_len(\"cafe\\u{0301}\")"), int(4)); // e + combining accent = 1 grapheme
    assert_eq!(run(r#"string_len("🇫🇷")"#), int(1)); // flag = 1 grapheme, 2 code points, 8 bytes
    assert_eq!(run(r#"string_len("a🇫🇷b")"#), int(3)); // a + flag + b = 3 graphemes
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_byte_len() {
    assert_eq!(run(r#"string_byte_len("")"#), int(0));
    assert_eq!(run(r#"string_byte_len("hello")"#), int(5));
    // unicode - byte counting
    assert_eq!(run(r#"string_byte_len("农")"#), int(3)); // 1 grapheme, 3 bytes
    assert_eq!(run(r#"string_byte_len("农历新年")"#), int(12)); // 4 graphemes, 12 bytes
    assert_eq!(run(r#"string_byte_len("🇫🇷")"#), int(8)); // flag = 1 grapheme, 8 bytes
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_iter() {
    // Basic iteration
    assert_eq!(
        run(
            r#"let s = "abc"; let mut it = string_iter(s); (string_iterator_next(it), string_iterator_next(it), string_iterator_next(it))"#
        ),
        tuple!(
            variant_t1("Some", string("a")),
            variant_t1("Some", string("b")),
            variant_t1("Some", string("c"))
        )
    );
    // Exhausted iterator
    assert_eq!(
        run(
            r#"let s = "ab"; let mut it = string_iter(s); (string_iterator_next(it), string_iterator_next(it), string_iterator_next(it))"#
        ),
        tuple!(
            variant_t1("Some", string("a")),
            variant_t1("Some", string("b")),
            variant_0("None")
        )
    );
    // Unicode - grapheme clusters
    assert_eq!(
        run(
            r#"let s = "a农b"; let mut it = string_iter(s); (string_iterator_next(it), string_iterator_next(it), string_iterator_next(it))"#
        ),
        tuple!(
            variant_t1("Some", string("a")),
            variant_t1("Some", string("农")),
            variant_t1("Some", string("b"))
        )
    );
    // Flag emoji as single grapheme
    assert_eq!(
        run(r#"let mut it = string_iter("🇫🇷"); string_iterator_next(it)"#),
        variant_t1("Some", string("🇫🇷"))
    );
    // Empty string
    assert_eq!(
        run(r#"let mut it = string_iter(""); string_iterator_next(it)"#),
        variant_0("None")
    );
    // Through Seq/SizedSeq traits
    assert_eq!(run(r#"len("")"#), int(0));
    assert_eq!(run(r#"len("hello")"#), int(5));
    assert_eq!(run(r#"len("héllo 🇫🇷, 农")"#), int(10));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_case_conversion() {
    assert_eq!(run(r#"uppercase("hello World!")"#), string("HELLO WORLD!"));
    // cspell:disable-next-line
    assert_eq!(run(r#"uppercase("tschüß")"#), string("TSCHÜSS"));
    assert_eq!(run(r#"lowercase("hello World!")"#), string("hello world!"));
    assert_eq!(run(r#"uppercase("农历新年")"#), string("农历新年"));
    assert_eq!(run(r#"lowercase("农历新年")"#), string("农历新年"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn serde_serialize() {
    // basic types
    assert_eq!(run("serialize(())"), variant_0("None"));
    assert_eq!(run("serialize(true)"), variant_t1("Bool", bool(true)));
    assert_eq!(run("serialize(1)"), variant_t1("Int", int(1)));
    assert_eq!(run("serialize(1.0)"), variant_t1("Float", float(1.0)));
    assert_eq!(
        run(r#"serialize("hello")"#),
        variant_t1("String", string("hello"))
    );
    assert_eq!(
        run("serialize([1])"),
        variant_t1("Array", array![variant_t1("Int", int(1))])
    );
    assert_eq!(
        run("serialize([1.0])"),
        variant_t1("Array", array![variant_t1("Float", float(1.0))])
    );

    // variants
    assert_eq!(
        run("serialize(None)"),
        variant_t1(
            "Object",
            array![tuple!(string("type"), variant_t1("String", string("None"))),]
        )
    );
    assert_eq!(
        run("serialize(Some(1.0))"),
        variant_t1(
            "Object",
            array![
                tuple!(string("type"), variant_t1("String", string("Some"))),
                tuple!(
                    string("data"),
                    variant_t1("Array", array![variant_t1("Float", float(1.0))])
                )
            ]
        )
    );

    // tuples
    assert_eq!(
        run("serialize((1, ))"),
        variant_t1("Array", array![variant_t1("Int", int(1))])
    );
    assert_eq!(
        run("serialize((1, 2))"),
        variant_t1(
            "Array",
            array![variant_t1("Int", int(1)), variant_t1("Int", int(2))]
        )
    );
    assert_eq!(
        run("serialize((1, 2.0, true))"),
        variant_t1(
            "Array",
            array![
                variant_t1("Int", int(1)),
                variant_t1("Float", float(2.)),
                variant_t1("Bool", bool(true))
            ]
        )
    );

    // records
    assert_eq!(
        run("serialize({a: 1, })"),
        variant_t1(
            "Object",
            array![tuple!(string("a"), variant_t1("Int", int(1)))]
        )
    );
    assert_eq!(
        run("serialize({a: 1, b: 2})"),
        variant_t1(
            "Object",
            array![
                tuple!(string("a"), variant_t1("Int", int(1))),
                tuple!(string("b"), variant_t1("Int", int(2)))
            ]
        )
    );
    assert_eq!(
        run("serialize({a: 1, b: 2.0, c: true})"),
        variant_t1(
            "Object",
            array![
                tuple!(string("a"), variant_t1("Int", int(1))),
                tuple!(string("b"), variant_t1("Float", float(2.))),
                tuple!(string("c"), variant_t1("Bool", bool(true)))
            ]
        )
    );

    // named types, by default serialize as their inner type
    assert_eq!(
        run("struct Age(float) serialize(Age(1.0))"),
        run("serialize((1.0, ))")
    );
    assert_eq!(
        run(
            "struct Person { name: string, age: float } serialize( Person { name: \"Alice\", age: 30.0 })"
        ),
        run("serialize({name: \"Alice\", age: 30.0})")
    );
    assert_eq!(
        run("enum SimpleColor { Red, Green, Blue } serialize(SimpleColor::Blue)"),
        run("serialize(Blue)")
    )
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn serde_deserialize() {
    // basic types
    assert_eq!(run("(deserialize(serialize(())) : ())"), Value::unit());
    assert_eq!(run("(deserialize(serialize(true)) : bool)"), bool(true));
    assert_eq!(run("(deserialize(serialize(1)): int)"), int(1));
    assert_eq!(run("(deserialize(serialize(1.0)): float)"), float(1.0));
    assert_eq!(
        run(r#"(deserialize(serialize("hello")): string)"#),
        string("hello")
    );
    assert_eq!(
        run("(deserialize(Array([Int(1), Int(1)])): [int])"),
        int_a![1, 1]
    );
    assert_eq!(
        run("(deserialize(Array([Int(1), Int(1)])): [float])"),
        array![float(1.0), float(1.0)]
    );

    // variants
    // TODO: once https://github.com/enlightware/ferlium/issues/75 is fixed
    // add (deserialize(serialize(None)): None)
    assert_eq!(
        run("(deserialize(serialize(None)): None | Some(int))"),
        none()
    );
    // TODO: once https://github.com/enlightware/ferlium/issues/59 is fixed, remove (int) ascription
    assert_eq!(
        run("(deserialize(serialize(Some((1: int)))): None | Some(int))"),
        some(int(1))
    );

    // tuples
    assert_eq!(
        run("(deserialize(serialize( (1, ) )): (int, ))"),
        tuple!(int(1))
    );
    assert_eq!(
        run("(deserialize(serialize( (1, 1, true) )): (int, float, bool))"),
        tuple!(int(1), float(1.0), bool(true))
    );

    // records
    assert_eq!(
        run("(deserialize(serialize( {a: 1, } )): {a: int})"),
        tuple!(int(1))
    );
    assert_eq!(
        run("(deserialize(serialize( {a: 1, } )): {a: float})"),
        tuple!(float(1.0))
    );
    assert_eq!(
        run("(deserialize(serialize( { b: true, a: 1 } )): {a: int, b: bool})"),
        tuple!(int(1), bool(true))
    );
    assert_eq!(
        run("(deserialize(serialize( { b: true, a: 1 } )): {a: int, b: bool})"),
        tuple!(int(1), bool(true))
    );

    // named types, by default de-serialize as their inner type
    assert_eq!(
        run("struct Age(float) (deserialize(serialize(Age(1.0))): Age)"),
        run("struct Age(float) (deserialize(serialize((1.0, ))): Age)")
    );
    assert_eq!(
        run(
            "struct Person { name: string, age: float } (deserialize(serialize( Person { name: \"Alice\", age: 30.0 })): Person)"
        ),
        run(
            "struct Person { name: string, age: float } (deserialize(serialize({name: \"Alice\", age: 30.0})): Person)"
        )
    );
    assert_eq!(
        run(
            "enum SimpleColor { Red, Green, Blue } (deserialize(serialize(SimpleColor::Blue)): SimpleColor)"
        ),
        run("enum SimpleColor { Red, Green, Blue } (deserialize(serialize(Blue)): SimpleColor)")
    );

    // errors
    fail_compilation(r#"deserialize(1)"#).expect_trait_impl_not_found("Num", &["Self = Variant"]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn serialize_with_type_ascription() {
    assert_eq!(
        run("fn test() -> Variant { Array([serialize(0)]) } test()"),
        variant_t1("Array", array![variant_t1("Int", int(0))])
    );
}
