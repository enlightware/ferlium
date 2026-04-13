// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;
use ustr::ustr;

use crate::effects::test_mod as test_mod_for_effects;

use crate::harness::{TestSession, bool, float, int, string, unit, variant_0, variant_t1};
use ferlium::{
    effects::{PrimitiveEffect, effect, no_effects},
    error::RuntimeErrorKind,
    std::option::{none, some},
    value::Value,
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn range_iterators() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("let r = 0..2; let mut it = iter(r); (next(it), next(it))"),
        tuple!(variant_t1("Some", int(0)), variant_t1("Some", int(1)))
    );
    assert_eq!(session.run("len(3..3)"), int(0));
    assert_eq!(session.run("len(3..4)"), int(1));
    assert_eq!(session.run("len(3..2)"), int(1));
    assert_eq!(session.run("is_empty(3..3)"), bool(true));
    assert_eq!(session.run("is_empty(3..4)"), bool(false));
    assert_eq!(session.run("is_empty(3..2)"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_append() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("let mut a = []; array_append(a, 1); a"),
        int_a![1]
    );
    assert_eq!(
        session.run("let mut a = [1]; array_append(a, 1); a"),
        int_a![1, 1]
    );
    assert_eq!(
        session.run("let mut a = [2]; array_append(a, 1); a"),
        int_a![2, 1]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_prepend() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("let mut a = []; array_prepend(a, 1); a"),
        int_a![1]
    );
    assert_eq!(
        session.run("let mut a = [1]; array_prepend(a, 1); a"),
        int_a![1, 1]
    );
    assert_eq!(
        session.run("let mut a = [2]; array_prepend(a, 1); a"),
        int_a![1, 2]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_pop_back() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("let mut a: [int] = []; array_pop_back(a)"),
        none()
    );
    assert_eq!(
        session.run("let mut a = [1]; array_pop_back(a); a"),
        int_a![]
    );
    assert_eq!(
        session.run("let mut a = [1]; array_pop_back(a)"),
        some(int(1))
    );
    assert_eq!(
        session.run("let mut a = [1, 2]; array_pop_back(a); a"),
        int_a![1]
    );
    assert_eq!(
        session.run("let mut a = [1, 2]; array_pop_back(a)"),
        some(int(2))
    );
    assert_eq!(
        session.run("let mut a = [1, 2, 3]; array_pop_back(a); a"),
        int_a![1, 2]
    );
    assert_eq!(
        session.run("let mut a = [1, 2, 3]; array_pop_back(a)"),
        some(int(3))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_pop_front() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("let mut a: [int] = []; array_pop_front(a)"),
        none()
    );
    assert_eq!(
        session.run("let mut a = [1]; array_pop_front(a); a"),
        int_a![]
    );
    assert_eq!(
        session.run("let mut a = [1]; array_pop_front(a)"),
        some(int(1))
    );
    assert_eq!(
        session.run("let mut a = [1, 2]; array_pop_front(a); a"),
        int_a![2]
    );
    assert_eq!(
        session.run("let mut a = [1, 2]; array_pop_front(a)"),
        some(int(1))
    );
    assert_eq!(
        session.run("let mut a = [1, 2, 3]; array_pop_front(a); a"),
        int_a![2, 3]
    );
    assert_eq!(
        session.run("let mut a = [1, 2, 3]; array_pop_front(a)"),
        some(int(1))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_len() {
    let mut session = TestSession::new();
    session
        .fail_compilation("let a = []; array_len(a)")
        .expect_unbound_ty_var();
    assert_eq!(session.run("let a = [1]; array_len(a)"), int(1));
    assert_eq!(session.run("let a = [1, 2]; array_len(a)"), int(2));
    assert_eq!(session.run("let a = [[1], [1, 1]]; array_len(a)"), int(2));
    assert_eq!(session.run("let a = [1, 1, 1]; array_len(a)"), int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_slice() {
    let mut session = TestSession::new();
    assert_eq!(session.run("array_slice([1, 2, 3], 0, 0)"), int_a![]);
    assert_eq!(session.run("array_slice([1, 2, 3], 1, 1)"), int_a![]);
    assert_eq!(session.run("array_slice([1, 2, 3], 0, 2)"), int_a![1, 2]);
    assert_eq!(session.run("array_slice([1, 2, 3], 1, 10)"), int_a![2, 3]);
    assert_eq!(session.run("array_slice([1, 2, 3], -2, 3)"), int_a![2, 3]);
    assert_eq!(session.run("array_slice([1, 2, 3], 0, -1)"), int_a![1, 2]);
    assert_eq!(session.run("array_slice([1, 2, 3], -2, -1)"), int_a![2]);
    assert_eq!(session.run("array_slice([1, 2, 3], 3, 5)"), int_a![]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_concat() {
    let mut session = TestSession::new();
    session
        .fail_compilation("array_concat([], [])")
        .expect_unbound_ty_var();
    assert_eq!(session.run("array_concat([1], [])"), int_a![1]);
    assert_eq!(session.run("array_concat([], [1])"), int_a![1]);
    assert_eq!(session.run("array_concat([1], [2])"), int_a![1, 2]);
    assert_eq!(session.run("array_concat([1, 2], [3])"), int_a![1, 2, 3]);
    assert_eq!(session.run("array_concat([1], [2, 3])"), int_a![1, 2, 3]);
    assert_eq!(
        session.run("array_concat([1, 2], [3, 4])"),
        int_a![1, 2, 3, 4]
    );
    assert_eq!(
        session.run("array_concat([1, 2], [3, 4, 5])"),
        int_a![1, 2, 3, 4, 5]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_map() {
    let mut session = TestSession::new();
    assert_eq!(session.run("array_map([1], |x| x)"), int_a![1]);
    assert_eq!(session.run("array_map([1], |x| x + 1)"), int_a![2]);
    assert_eq!(
        session.run("array_map([1, 2, 3], |x| x + 1)"),
        int_a![2, 3, 4]
    );
    assert_eq!(
        session.run("array_map([1, 2, 3], |x| x >= 2)"),
        bool_a![false, true, true]
    );
    assert_eq!(
        session.run("array_map([(1, 2), (2, 3), (3, 4)], |v| v.0 + v.1)"),
        int_a![3, 5, 7]
    );
    use PrimitiveEffect::*;
    test_mod_for_effects(
        &mut session,
        "fn f() { let a = [1]; array_map(a, |v| { v >= 1 }) }",
        "f",
        no_effects(),
    );
    test_mod_for_effects(
        &mut session,
        "fn f() { let a = [1]; array_map(a, |v| { effects::read(); v >= 1 }) }",
        "f",
        effect(Read),
    );
}
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_any() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("array_any(([]: [int]), |x| x == 1)"),
        bool(false)
    );
    assert_eq!(session.run("array_any([1], |x| x == 1)"), bool(true));
    assert_eq!(session.run("array_any([1, 2, 3], |x| x == 1)"), bool(true));
    assert_eq!(session.run("array_any([1, 2, 3], |x| x >= 2)"), bool(true));
    assert_eq!(session.run("array_any([1, 2, 3], |x| x >= 4)"), bool(false));
    use PrimitiveEffect::*;
    test_mod_for_effects(
        &mut session,
        "fn f() { let a = [(1: int)]; array_any(a, |v| { v >= 1 }) }",
        "f",
        no_effects(),
    );
    test_mod_for_effects(
        &mut session,
        "fn f() { let a = [(1: int)]; array_any(a, |v| { effects::read(); v >= 1 }) }",
        "f",
        effect(Read),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_all() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("array_all(([]: [int]), |x| x == 1)"),
        bool(true)
    );
    assert_eq!(session.run("array_all([1], |x| x == 1)"), bool(true));
    assert_eq!(session.run("array_all([1, 2, 3], |x| x == 1)"), bool(false));
    assert_eq!(session.run("array_all([1, 2, 3], |x| x >= 1)"), bool(true));
    assert_eq!(session.run("array_all([1, 2, 3], |x| x >= 2)"), bool(false));
    use PrimitiveEffect::*;
    test_mod_for_effects(
        &mut session,
        "fn f() { let a = [(1: int)]; array_all(a, |v| { v >= 1 }) }",
        "f",
        no_effects(),
    );
    test_mod_for_effects(
        &mut session,
        "fn f() { let a = [(1: int)]; array_all(a, |v| { effects::read(); v >= 1 }) }",
        "f",
        effect(Read),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_iterators() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("let a = [1, 2, 3]; let mut it = array_iter(a); (next(it), next(it))"),
        tuple!(variant_t1("Some", int(1)), variant_t1("Some", int(2)))
    );
    assert_eq!(
        session.run("let a = [1.0, 2.0, 3.0]; let mut it = array_iter(a); (next(it), next(it))"),
        tuple!(
            variant_t1("Some", float(1.0)),
            variant_t1("Some", float(2.0))
        )
    );
    assert_eq!(
        session.run(
            r#"let a = ["hello", "world"]; let mut it = array_iter(a); (next(it), next(it), next(it))"#
        ),
        tuple!(
            variant_t1("Some", string("hello")),
            variant_t1("Some", string("world")),
            variant_0("None")
        )
    );
    assert_eq!(
        session.run("let a = [1, 2, 3]; let mut it = iter(a); (next(it), next(it))"),
        tuple!(variant_t1("Some", int(1)), variant_t1("Some", int(2)))
    );
    assert_eq!(
        session.run("let a = [1.0, 2.0, 3.0]; let mut it = iter(a); (next(it), next(it))"),
        tuple!(
            variant_t1("Some", float(1.0)),
            variant_t1("Some", float(2.0))
        )
    );
    assert_eq!(
        session.run(
            r#"let a = ["hello", "world"]; let mut it = iter(a); (next(it), next(it), next(it))"#
        ),
        tuple!(
            variant_t1("Some", string("hello")),
            variant_t1("Some", string("world")),
            variant_0("None")
        )
    );
    assert_eq!(session.run("len(([]: [int]))"), int(0));
    assert_eq!(session.run("len([1, 2])"), int(2));
    assert_eq!(session.run("len([true, false, true])"), int(3));
    assert_eq!(session.run("is_empty(([]: [int]))"), bool(true));
    assert_eq!(session.run("is_empty([1, 2])"), bool(false));
    assert_eq!(session.run("is_empty([true, false, true])"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_casts() {
    let mut session = TestSession::new();
    // Identity casts
    assert_eq!(session.run("([1, 2, 3]: [int]) as [int]"), int_a![1, 2, 3]);
    assert_eq!(
        session.run("([1.0, 2.4, 3.0]: [float]) as [float]"),
        float_a![1.0, 2.4, 3.0]
    );
    // Inner type casts
    assert_eq!(
        session.run("([1, 2, 3]: [int]) as [float]"),
        float_a![1.0, 2.0, 3.0]
    );
    assert_eq!(
        session.run("([1.0, 2.4, 3.0]: [float]) as [int]"),
        int_a![1, 2, 3]
    );
    // In functions
    assert_eq!(
        session.run("fn f(v) { v as [float] } f([1.0, 2.4, 3.0])"),
        float_a![1.0, 2.4, 3.0]
    );
    assert_eq!(
        session.run("fn f(v) { v as [int] } f([1.0, 2.4, 3.0])"),
        int_a![1, 2, 3]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn reducing_fns() {
    let mut session = TestSession::new();
    assert_eq!(session.run("0..2 |> any(|x| x > 1)"), bool(false));
    assert_eq!(session.run("0..2 |> iter() |> any(|x| x > 1)"), bool(false));
    assert_eq!(session.run("0..2 |> any(|x| x >= 1)"), bool(true));
    assert_eq!(session.run("0..2 |> iter() |> any(|x| x >= 1)"), bool(true));
    assert_eq!(session.run("[0, 1] |> any(|x| x > 1)"), bool(false));
    assert_eq!(
        session.run("[0, 1] |> iter() |> any(|x| x > 1)"),
        bool(false)
    );
    assert_eq!(session.run("[0, 1] |> any(|x| x >= 1)"), bool(true));
    assert_eq!(
        session.run("[0, 1] |> iter() |> any(|x| x >= 1)"),
        bool(true)
    );
    assert_eq!(session.run("0..2 |> all(|x| x > 0)"), bool(false));
    assert_eq!(session.run("0..2 |> iter() |> all(|x| x > 0)"), bool(false));
    assert_eq!(session.run("0..2 |> all(|x| x >= 0)"), bool(true));
    assert_eq!(session.run("0..2 |> iter() |> all(|x| x >= 0)"), bool(true));
    assert_eq!(session.run("[0, 1] |> all(|x| x > 0)"), bool(false));
    assert_eq!(
        session.run("[0, 1] |> iter() |> all(|x| x > 0)"),
        bool(false)
    );
    assert_eq!(session.run("[0, 1] |> all(|x| x >= 0)"), bool(true));
    assert_eq!(
        session.run("[0, 1] |> iter() |> all(|x| x >= 0)"),
        bool(true)
    );
    assert_eq!(session.run("2..5 |> count()"), int(3));
    assert_eq!(session.run("2..5 |> iter() |> count()"), int(3));
    assert_eq!(session.run("[2, 5] |> count()"), int(2));
    assert_eq!(session.run("[2, 5] |> iter() |> count()"), int(2));
    assert_eq!(session.run("[2, 5] |> iter() |> iter() |> count()"), int(2));
    assert_eq!(session.run("2..5 |> sum()"), int(9));
    assert_eq!(session.run("2..5 |> iter() |> sum()"), int(9));
    assert_eq!(session.run("[2, 5] |> sum()"), int(7));
    assert_eq!(session.run("[2, 5] |> iter() |> sum()"), int(7));
    assert_eq!(session.run("[2.5, 5] |> sum()"), float(7.5));
    assert_eq!(session.run("[2.5, 5] |> iter() |> sum()"), float(7.5));
    assert_eq!(session.run("[0, 1, 3] |> find(|x| x > 1)"), some(int(3)));
    assert_eq!(
        session.run("[0, 1, 3] |> iter() |> find(|x| x > 1)"),
        some(int(3))
    );
    assert_eq!(session.run("[0, 1, 3] |> find(|x| x < 0)"), none());
    assert_eq!(
        session.run("[0, 1, 3] |> iter() |> find(|x| x < 0)"),
        none()
    );
    assert_eq!(
        session.run("[0, 1, 3] |> position(|x| x > 1)"),
        some(int(2))
    );
    assert_eq!(
        session.run("[0, 1, 3] |> iter() |> position(|x| x > 1)"),
        some(int(2))
    );
    assert_eq!(session.run("[0, 1, 3] |> position(|x| x < 0)"), none());
    assert_eq!(
        session.run("[0, 1, 3] |> iter() |> position(|x| x < 0)"),
        none()
    );
    assert_eq!(session.run("[3, 1, 2] |> minimum()"), int(1));
    assert_eq!(session.run("[3, 1, 2] |> iter() |> minimum()"), int(1));
    assert_eq!(session.run("[3.0, 1.0, 2.0] |> minimum()"), float(1.0));
    assert_eq!(
        session.run("[3.0, 1.0, 2.0] |> iter() |> minimum()"),
        float(1.0)
    );
    assert_eq!(session.run("[3, 1, 2] |> maximum()"), int(3));
    assert_eq!(session.run("[3, 1, 2] |> iter() |> maximum()"), int(3));
    assert_eq!(session.run("[3.0, 1.0, 2.0] |> maximum()"), float(3.0));
    assert_eq!(
        session.run("[3.0, 1.0, 2.0] |> iter() |> maximum()"),
        float(3.0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mapping_fns() {
    let mut session = TestSession::new();
    assert_eq!(session.run("[0, 1, 2] |> map(|x| x + 1)"), int_a![1, 2, 3]);
    assert_eq!(
        session.run(
            "let mut it = [0, 1, 2] |> iter() |> map(|x| x + 1); (next(it), next(it), next(it), next(it))"
        ),
        tuple!(some(int(1)), some(int(2)), some(int(3)), none())
    );
    assert_eq!(session.run("[0, 1, 2] |> filter(|x| x > 0)"), int_a![1, 2]);
    assert_eq!(
        session.run(
            "let mut it = [0, 1, 2] |> iter() |> filter(|x| x > 0); (next(it), next(it), next(it))"
        ),
        tuple!(some(int(1)), some(int(2)), none())
    );
    assert_eq!(
        session.run("[0, 1, 2] |> filter_map(|x| if x > 0 { Some(x * x) } else { None })"),
        int_a![1, 4]
    );
    assert_eq!(
        session.run(
            "let mut it = [0, 1, 2] |> iter() |> filter_map(|x| if x > 0 { Some(x * x) } else { None }); (next(it), next(it), next(it))"
        ),
        tuple!(some(int(1)), some(int(4)), none())
    );
    use PrimitiveEffect::*;
    test_mod_for_effects(
        &mut session,
        "fn f() { [0, 1, 2] |> map(|x| x + 1) }",
        "f",
        no_effects(),
    );
    session
        .fail_compilation("fn f() { [0, 1, 2] |> map(|x| { effects::read(); x + 1 }) }")
        .expect_invalid_effect_dependency(effect(Read), no_effects());
    session
        .fail_compilation("fn f() { [0, 1, 2] |> filter(|x| { effects::read(); x > 0 }) }")
        .expect_invalid_effect_dependency(effect(Read), no_effects());
    session
        .fail_compilation("fn f() { [0, 1, 2] |> filter_map(|x| { effects::read(); Some(x) }) }")
        .expect_invalid_effect_dependency(effect(Read), no_effects());
    session
        .fail_compilation(
            "fn f() { let ignored = [0, 1, 2] |> iter() |> map(|x| { effects::read(); x + 1 }); () }",
        )
        .expect_invalid_effect_dependency(effect(Read), no_effects());
    session
        .fail_compilation(
            "fn f() { let ignored = [0, 1, 2] |> iter() |> filter(|x| { effects::read(); x > 0 }); () }",
        )
        .expect_invalid_effect_dependency(effect(Read), no_effects());
    session
        .fail_compilation(
            "fn f() { let ignored = [0, 1, 2] |> iter() |> filter_map(|x| { effects::read(); Some(x) }); () }",
        )
        .expect_invalid_effect_dependency(effect(Read), no_effects());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn collect_fns() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("([1, 2, 3] |> collect(): [_])"),
        int_a![1, 2, 3]
    );
    assert_eq!(
        session.run("([1, 2, 3] |> iter() |> collect(): [_])"),
        int_a![1, 2, 3]
    );
    assert_eq!(
        session.run("([1, 2, 3] |> iter() |> map(|x| x as float) |> collect(): [_])"),
        float_a![1.0, 2.0, 3.0]
    );
    assert_eq!(
        session.run("let ys: [_] = [1, 2, 3] |> iter() |> map(|x| x as float) |> collect(); ys"),
        float_a![1.0, 2.0, 3.0]
    );
    assert_eq!(session.run("(0..3 |> collect(): [int])"), int_a![0, 1, 2]);
    session
        .fail_compilation("[1, 2, 3] |> iter() |> collect()")
        .expect_unbound_ty_var();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn plain_join_is_inferred_as_generic_function() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("join([\"a\", \"b\", \"c\"], \",\")"),
        string("a,b,c")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn join_accepts_iterator_input() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("join([\"a\", \"b\", \"c\"] |> iter(), \",\")"),
        string("a,b,c")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn join_uses_empty_for_empty_sequences() {
    let mut session = TestSession::new();
    assert_eq!(session.run("(join([], \",\"): string)"), string(""));
    assert_eq!(session.run("(join([], [0]): [int])"), int_a![]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn join_works_on_arrays_of_arrays() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("join([[1], [2], [3]], [0])"),
        int_a![1, 0, 2, 0, 3]
    );
    assert_eq!(session.run("(join([], [0]): [int])"), int_a![]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_split() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(r#"split(",a,,", ",")"#),
        array![string(""), string("a"), string(""), string("")]
    );
    assert_eq!(
        session.run(r#"join(split_iterator(",a,,", ","), ",")"#),
        string(",a,,")
    );
    assert_eq!(
        session.run(
            r#"let mut it = split_iterator(",a,,", ","); (next(it), next(it), next(it), next(it), next(it))"#
        ),
        tuple!(
            variant_t1("Some", string("")),
            variant_t1("Some", string("a")),
            variant_t1("Some", string("")),
            variant_t1("Some", string("")),
            variant_0("None")
        )
    );
    assert_eq!(
        session.run(r#"split("a🇫🇷b🇫🇷c", "🇫🇷")"#),
        array![string("a"), string("b"), string("c")]
    );
    assert_eq!(
        session.run(r#"split("a👩‍💻b👩‍💻c", "👩‍💻")"#),
        array![string("a"), string("b"), string("c")]
    );
    assert_eq!(session.run(r#"split("a🇫🇷b", "🇫")"#), array![string("a🇫🇷b")]);
    assert_eq!(
        session.run(r#"split("cafe\u{0301}-caf\u{00E9}", "e\u{0301}")"#),
        array![string("caf"), string("-caf"), string("")]
    );
    assert_eq!(
        session.fail_run(r#"split("abc", "")"#),
        RuntimeErrorKind::InvalidArgument(ustr("separator must not be empty"))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_split() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("split([1, 0, 0, 2, 0, 0, 3], [0, 0])"),
        array![int_a![1], int_a![2], int_a![3]]
    );
    assert_eq!(
        session.run("split([0, 1, 0, 2, 0], 0)"),
        array![int_a![], int_a![1], int_a![2], int_a![]]
    );
    assert_eq!(
        session.run(
            "let mut it = split_iterator([0, 1, 0, 2, 0], 0); (next(it), next(it), next(it), next(it), next(it))"
        ),
        tuple!(
            variant_t1("Some", int_a![]),
            variant_t1("Some", int_a![1]),
            variant_t1("Some", int_a![2]),
            variant_t1("Some", int_a![]),
            variant_0("None")
        )
    );
    assert_eq!(
        session.run("join(split_iterator([1, 0, 2, 0, 3], 0), [0])"),
        int_a![1, 0, 2, 0, 3]
    );
    assert_eq!(
        session.fail_run("split([1, 2], [])"),
        RuntimeErrorKind::InvalidArgument(ustr("separator must not be empty"))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn default() {
    let mut session = TestSession::new();
    assert_eq!(session.run("(default(): ())"), unit());
    assert_eq!(session.run("(default(): bool)"), bool(false));
    assert_eq!(session.run("(default(): int)"), int(0));
    assert_eq!(session.run("(default(): float)"), float(0.0));
    assert_eq!(session.run("(default(): string)"), string(""));
    assert_eq!(session.run("(default(): [int])"), int_a![]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn empty() {
    let mut session = TestSession::new();
    assert_eq!(session.run("(empty(): string)"), string(""));
    assert_eq!(session.run("(empty(): [int])"), int_a![]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn contains_and_contains_substring() {
    let mut session = TestSession::new();
    // strings
    assert_eq!(
        session.run("contains_substring(\"hello world\", \"world\")"),
        bool(true)
    );
    assert_eq!(
        session.run("contains_substring(\"hello world\", \"world!\")"),
        bool(false)
    );
    assert_eq!(
        session.run("contains_substring(\"hello world\", \"\")"),
        bool(true)
    );
    assert_eq!(session.run("contains_substring(\"\", \"\")"), bool(true));
    assert_eq!(session.run("contains_substring(\"\", \"a\")"), bool(false));
    // arrays
    assert_eq!(session.run("contains([1, 2, 3], 2)"), bool(true));
    assert_eq!(session.run("contains([1, 2, 3], 4)"), bool(false));
    session
        .fail_compilation("contains([], 1)")
        .into_inner()
        .into_unresolved_constraints()
        .unwrap();
    assert_eq!(session.run("contains([-3.0], 1.0)"), bool(false));
    assert_eq!(session.run("contains([-3.0, 3.0, 1.0], 1.0)"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_trim_and_prefix_suffix() {
    let mut session = TestSession::new();
    assert_eq!(session.run(r#"string_trim("")"#), string(""));
    assert_eq!(session.run(r#"string_trim("  hello  ")"#), string("hello"));
    assert_eq!(
        session.run("string_trim(\"\\n\\t hello \\u{00A0}\")"),
        string("hello")
    );
    assert_eq!(
        session.run(r#"string_trim("  café 🇫🇷  ")"#),
        string("café 🇫🇷")
    );
    assert_eq!(
        session.run(r#"string_starts_with("hello", "he")"#),
        bool(true)
    );
    assert_eq!(
        session.run(r#"string_starts_with("hello", "")"#),
        bool(true)
    );
    assert_eq!(session.run(r#"string_starts_with("", "")"#), bool(true));
    assert_eq!(session.run(r#"string_starts_with("", "a")"#), bool(false));
    assert_eq!(
        session.run(r#"string_starts_with("hello", "lo")"#),
        bool(false)
    );
    assert_eq!(
        session.run("string_starts_with(\"caf\\u{00E9}\", \"cafe\\u{0301}\")"),
        bool(true)
    );
    assert_eq!(
        session.run(r#"string_ends_with("hello", "lo")"#),
        bool(true)
    );
    assert_eq!(session.run(r#"string_ends_with("hello", "")"#), bool(true));
    assert_eq!(session.run(r#"string_ends_with("", "")"#), bool(true));
    assert_eq!(session.run(r#"string_ends_with("", "a")"#), bool(false));
    assert_eq!(
        session.run(r#"string_ends_with("hello", "he")"#),
        bool(false)
    );
    assert_eq!(
        session.run("string_ends_with(\"caf\\u{00E9}\", \"fe\\u{0301}\")"),
        bool(true)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn concat() {
    let mut session = TestSession::new();
    // strings
    assert_eq!(
        session.run(r#"concat("hello", "world")"#),
        string("helloworld")
    );
    assert_eq!(session.run(r#"concat("foo", " bar")"#), string("foo bar"));
    assert_eq!(session.run(r#"concat("", "")"#), string(""));
    assert_eq!(session.run(r#"concat("a", "")"#), string("a"));
    assert_eq!(session.run(r#"concat("", "b")"#), string("b"));
    // arrays
    assert_eq!(session.run("concat([1, 2], [3, 4])"), int_a![1, 2, 3, 4]);
    assert_eq!(session.run("concat([], [])"), int_a![]);
    assert_eq!(session.run("(concat([], []): [int])"), int_a![]);
    assert_eq!(session.run("concat([1, 2], [])"), int_a![1, 2]);
    assert_eq!(session.run("concat([], [3, 4])"), int_a![3, 4]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_concat() {
    let mut session = TestSession::new();
    assert_eq!(session.run(r#"string_concat("", "")"#), string(""));
    assert_eq!(
        session.run(r#"string_concat("hello", "world")"#),
        string("helloworld")
    );
    assert_eq!(
        session.run(r#"string_concat("hello", " world")"#),
        string("hello world")
    );
    assert_eq!(
        session.run(r#"string_concat("hello ", "world")"#),
        string("hello world")
    );
    assert_eq!(
        session.run(r#"string_concat("hello ", " world")"#),
        string("hello  world")
    );
    assert_eq!(
        session.run(r#"string_concat("hello ", "world!")"#),
        string("hello world!")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_push_str() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(r#"let mut s = ""; string_push_str(s, ""); s"#),
        string("")
    );
    assert_eq!(
        session.run(r#"let mut s = ""; string_push_str(s, "hello"); s"#),
        string("hello")
    );
    assert_eq!(
        session.run(r#"let mut s = "hello"; string_push_str(s, " world"); s"#),
        string("hello world")
    );
    assert_eq!(
        session.run(r#"let mut s = "hello"; string_push_str(s, " world!"); s"#),
        string("hello world!")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_replace() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(r#"string_replace("hello world", "world", "world!")"#),
        string("hello world!")
    );
    assert_eq!(
        session.run(r#"string_replace("hello world", "world", "")"#),
        string("hello ")
    );
    assert_eq!(
        session.run(r#"string_replace("hello world", "world", "world")"#),
        string("hello world")
    );
    assert_eq!(
        session.run(r#"string_replace("hello world", "world", "world!!")"#),
        string("hello world!!")
    );
    assert_eq!(
        session.run(r#"string_replace("hello world and other world are cool", "world", "home")"#),
        string("hello home and other home are cool")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_slice() {
    let mut session = TestSession::new();
    assert_eq!(session.run(r#"string_slice("hello", 0, 0)"#), string(""));
    assert_eq!(session.run(r#"string_slice("hello", 3, 0)"#), string(""));
    assert_eq!(
        session.run(r#"string_slice("hello", 0, 5)"#),
        string("hello")
    );
    assert_eq!(
        session.run(r#"string_slice("hello", 0, 15)"#),
        string("hello")
    );
    assert_eq!(
        session.run(r#"string_slice("hello", -5, 5)"#),
        string("hello")
    );
    assert_eq!(
        session.run(r#"string_slice("hello", 0, 4)"#),
        string("hell")
    );
    assert_eq!(
        session.run(r#"string_slice("hello", 0, -1)"#),
        string("hell")
    );
    assert_eq!(session.run(r#"string_slice("hello", 1, 4)"#), string("ell"));
    assert_eq!(
        session.run(r#"string_slice("hello", 1, -1)"#),
        string("ell")
    );
    assert_eq!(
        session.run(r#"string_slice("hello", -4, -2)"#),
        string("el")
    );

    // unicode - now using grapheme-based indices (character positions)
    // "农" is 1 grapheme cluster (1 character)
    assert_eq!(session.run(r#"string_slice("农", 0, 1)"#), string("农"));
    assert_eq!(session.run(r#"string_slice("农", 0, 10)"#), string("农")); // clamps to length
    assert_eq!(session.run(r#"string_slice("农", 1, 2)"#), string("")); // past end
    // "a农" is 2 grapheme clusters
    assert_eq!(session.run(r#"string_slice("a农", 0, 1)"#), string("a"));
    assert_eq!(session.run(r#"string_slice("a农", 1, 2)"#), string("农"));
    assert_eq!(session.run(r#"string_slice("a农", 0, 2)"#), string("a农"));
    // "café" with combining accent (e + combining acute) is 4 graphemes
    assert_eq!(
        session.run("string_slice(\"cafe\\u{0301}\", 0, 4)"),
        string("cafe\u{0301}")
    );
    assert_eq!(
        session.run("string_slice(\"cafe\\u{0301}\", 3, 4)"),
        string("e\u{0301}")
    );
    // flag emoji (2 regional indicators = 1 grapheme)
    assert_eq!(session.run(r#"string_slice("🇫🇷", 0, 1)"#), string("🇫🇷"));
    assert_eq!(session.run(r#"string_slice("a🇫🇷b", 1, 2)"#), string("🇫🇷"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_len() {
    let mut session = TestSession::new();
    assert_eq!(session.run(r#"string_len("")"#), int(0));
    assert_eq!(session.run(r#"string_len("hello")"#), int(5));
    // unicode - grapheme-based counting
    assert_eq!(session.run(r#"string_len("农")"#), int(1)); // 1 grapheme, 3 bytes
    assert_eq!(session.run(r#"string_len("农历新年")"#), int(4)); // 4 graphemes
    assert_eq!(session.run("string_len(\"cafe\\u{0301}\")"), int(4)); // e + combining accent = 1 grapheme
    assert_eq!(session.run(r#"string_len("🇫🇷")"#), int(1)); // flag = 1 grapheme, 2 code points, 8 bytes
    assert_eq!(session.run(r#"string_len("a🇫🇷b")"#), int(3)); // a + flag + b = 3 graphemes
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_byte_len() {
    let mut session = TestSession::new();
    assert_eq!(session.run(r#"string_byte_len("")"#), int(0));
    assert_eq!(session.run(r#"string_byte_len("hello")"#), int(5));
    // unicode - byte counting
    assert_eq!(session.run(r#"string_byte_len("农")"#), int(3)); // 1 grapheme, 3 bytes
    assert_eq!(session.run(r#"string_byte_len("农历新年")"#), int(12)); // 4 graphemes, 12 bytes
    assert_eq!(session.run(r#"string_byte_len("🇫🇷")"#), int(8)); // flag = 1 grapheme, 8 bytes
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_iter() {
    let mut session = TestSession::new();
    // Basic iteration
    assert_eq!(
        session.run(
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
        session.run(
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
        session.run(
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
        session.run(r#"let mut it = string_iter("🇫🇷"); string_iterator_next(it)"#),
        variant_t1("Some", string("🇫🇷"))
    );
    // Empty string
    assert_eq!(
        session.run(r#"let mut it = string_iter(""); string_iterator_next(it)"#),
        variant_0("None")
    );
    // Through Seq/SizedSeq traits
    assert_eq!(session.run(r#"len("")"#), int(0));
    assert_eq!(session.run(r#"len("hello")"#), int(5));
    assert_eq!(session.run(r#"len("héllo 🇫🇷, 农")"#), int(10));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_case_conversion() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(r#"uppercase("hello World!")"#),
        string("HELLO WORLD!")
    );
    // cspell:disable-next-line
    assert_eq!(session.run(r#"uppercase("tschüß")"#), string("TSCHÜSS"));
    assert_eq!(
        session.run(r#"lowercase("hello World!")"#),
        string("hello world!")
    );
    assert_eq!(session.run(r#"uppercase("农历新年")"#), string("农历新年"));
    assert_eq!(session.run(r#"lowercase("农历新年")"#), string("农历新年"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_normalization() {
    let mut session = TestSession::new();
    // Strings are stored in NFC form. U+0065 (e) + U+0301 (combining acute) in
    // NFD is 3 bytes; its NFC precomposed form U+00E9 (é) is 2 bytes.
    // string_byte_len distinguishes the two forms.
    assert_eq!(
        session.run("string_byte_len(\"e\\u{0301}\")"),
        int(2) // NFC: U+00E9 → 2 bytes, not NFD 3 bytes
    );
    // A string literal with a combining mark is equal to the precomposed form.
    assert_eq!(session.run("\"e\\u{0301}\" == \"\\u{00E9}\""), bool(true));
    // string_concat: combining mark at the junction is absorbed into NFC.
    // "cafe" + "\u{0301}" → NFC "caf\u{00E9}" = 5 bytes, not un-normalized 6.
    assert_eq!(
        session.run("string_byte_len(string_concat(\"cafe\", \"\\u{0301}\"))"),
        int(5)
    );
    assert_eq!(
        session.run("string_concat(\"cafe\", \"\\u{0301}\") == \"caf\\u{00E9}\""),
        bool(true)
    );
    // string_push_str: combining mark appended to a base character normalizes.
    assert_eq!(
        session.run("let mut s = \"cafe\"; string_push_str(s, \"\\u{0301}\"); string_byte_len(s)"),
        int(5)
    );
    assert_eq!(
        session
            .run("let mut s = \"cafe\"; string_push_str(s, \"\\u{0301}\"); s == \"caf\\u{00E9}\""),
        bool(true)
    );
    // string_replace: the replacement result is NFC normalized.
    // Replacing "e" with NFD "e\u{0301}" in "hello" yields NFC "h\u{00E9}llo" = 6 bytes.
    assert_eq!(
        session.run("string_byte_len(string_replace(\"hello\", \"e\", \"e\\u{0301}\"))"),
        int(6)
    );
    assert_eq!(
        session.run("string_replace(\"hello\", \"e\", \"e\\u{0301}\") == \"h\\u{00E9}llo\""),
        bool(true)
    );
    // uppercase and lowercase keep the result in NFC.
    // U+00E9 (é) uppercases to U+00C9 (É), which is 2 bytes in UTF-8.
    assert_eq!(
        session.run("string_byte_len(uppercase(\"e\\u{0301}\"))"),
        int(2)
    );
    assert_eq!(
        session.run("uppercase(\"e\\u{0301}\") == \"\\u{00C9}\""),
        bool(true)
    );
    assert_eq!(
        session.run("lowercase(\"E\\u{0301}\") == \"\\u{00E9}\""),
        bool(true)
    );
    // string_slice of an NFC string stays NFC.
    assert_eq!(
        session.run("string_byte_len(string_slice(\"caf\\u{00E9}\", 3, 4))"),
        int(2) // the é slice is still the 2-byte NFC form
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn serde_serialize() {
    let mut session = TestSession::new();
    // basic types
    assert_eq!(session.run("serialize(())"), variant_0("None"));
    assert_eq!(
        session.run("serialize(true)"),
        variant_t1("Bool", bool(true))
    );
    assert_eq!(session.run("serialize(1)"), variant_t1("Int", int(1)));
    assert_eq!(
        session.run("serialize(1.0)"),
        variant_t1("Float", float(1.0))
    );
    assert_eq!(
        session.run(r#"serialize("hello")"#),
        variant_t1("String", string("hello"))
    );
    assert_eq!(
        session.run("serialize([1])"),
        variant_t1("Array", array![variant_t1("Int", int(1))])
    );
    assert_eq!(
        session.run("serialize([1.0])"),
        variant_t1("Array", array![variant_t1("Float", float(1.0))])
    );

    // variants
    assert_eq!(
        session.run("serialize(None)"),
        variant_t1(
            "Object",
            array![tuple!(string("type"), variant_t1("String", string("None"))),]
        )
    );
    assert_eq!(
        session.run("serialize(Some(1.0))"),
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
        session.run("serialize((1, ))"),
        variant_t1("Array", array![variant_t1("Int", int(1))])
    );
    assert_eq!(
        session.run("serialize((1, 2))"),
        variant_t1(
            "Array",
            array![variant_t1("Int", int(1)), variant_t1("Int", int(2))]
        )
    );
    assert_eq!(
        session.run("serialize((1, 2.0, true))"),
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
        session.run("serialize({a: 1, })"),
        variant_t1(
            "Object",
            array![tuple!(string("a"), variant_t1("Int", int(1)))]
        )
    );
    assert_eq!(
        session.run("serialize({a: 1, b: 2})"),
        variant_t1(
            "Object",
            array![
                tuple!(string("a"), variant_t1("Int", int(1))),
                tuple!(string("b"), variant_t1("Int", int(2)))
            ]
        )
    );
    assert_eq!(
        session.run("serialize({a: 1, b: 2.0, c: true})"),
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
        session.run("struct Age(float) serialize(Age(1.0))"),
        session.run("serialize((1.0, ))")
    );
    assert_eq!(
        session.run(
            "struct Person { name: string, age: float } serialize( Person { name: \"Alice\", age: 30.0 })"
        ),
        session.run("serialize({name: \"Alice\", age: 30.0})")
    );
    assert_eq!(
        session.run("enum SimpleColor { Red, Green, Blue } serialize(SimpleColor::Blue)"),
        session.run("serialize(Blue)")
    )
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn serde_deserialize() {
    let mut session = TestSession::new();
    // basic types
    assert_eq!(
        session.run("(deserialize(serialize(())) : ())"),
        Value::unit()
    );
    assert_eq!(
        session.run("(deserialize(serialize(true)) : bool)"),
        bool(true)
    );
    assert_eq!(session.run("(deserialize(serialize(1)): int)"), int(1));
    assert_eq!(
        session.run("(deserialize(serialize(1.0)): float)"),
        float(1.0)
    );
    assert_eq!(
        session.run(r#"(deserialize(serialize("hello")): string)"#),
        string("hello")
    );
    assert_eq!(
        session.run("(deserialize(Array([Int(1), Int(1)])): [int])"),
        int_a![1, 1]
    );
    assert_eq!(
        session.run("(deserialize(Array([Int(1), Int(1)])): [float])"),
        array![float(1.0), float(1.0)]
    );

    // variants
    // TODO: once https://github.com/enlightware/ferlium/issues/75 is fixed
    // add (deserialize(serialize(None)): None)
    assert_eq!(
        session.run("(deserialize(serialize(None)): None | Some(int))"),
        none()
    );
    assert_eq!(
        session.run("(deserialize(serialize(Some(1))): None | Some(int))"),
        some(int(1))
    );
    assert_eq!(
        session.run("(deserialize(serialize(Some((1: int)))): None | Some(int))"),
        some(int(1))
    );

    // tuples
    assert_eq!(
        session.run("(deserialize(serialize( (1, ) )): (int, ))"),
        tuple!(int(1))
    );
    assert_eq!(
        session.run("(deserialize(serialize( (1, 1, true) )): (int, float, bool))"),
        tuple!(int(1), float(1.0), bool(true))
    );

    // records
    assert_eq!(
        session.run("(deserialize(serialize( {a: 1, } )): {a: int})"),
        tuple!(int(1))
    );
    assert_eq!(
        session.run("(deserialize(serialize( {a: 1, } )): {a: float})"),
        tuple!(float(1.0))
    );
    assert_eq!(
        session.run("(deserialize(serialize( { b: true, a: 1 } )): {a: int, b: bool})"),
        tuple!(int(1), bool(true))
    );
    assert_eq!(
        session.run("(deserialize(serialize( { b: true, a: 1 } )): {a: int, b: bool})"),
        tuple!(int(1), bool(true))
    );

    // named types, by default de-serialize as their inner type
    assert_eq!(
        session.run("struct Age(float) (deserialize(serialize(Age(1.0))): Age)"),
        session.run("struct Age(float) (deserialize(serialize((1.0, ))): Age)")
    );
    assert_eq!(
        session.run(
            "struct Person { name: string, age: float } (deserialize(serialize( Person { name: \"Alice\", age: 30.0 })): Person)"
        ),
        session.run(
            "struct Person { name: string, age: float } (deserialize(serialize({name: \"Alice\", age: 30.0})): Person)"
        )
    );
    assert_eq!(
        session.run(
            "enum SimpleColor { Red, Green, Blue } (deserialize(serialize(SimpleColor::Blue)): SimpleColor)"
        ),
        session.run("enum SimpleColor { Red, Green, Blue } (deserialize(serialize(Blue)): SimpleColor)")
    );

    // errors
    session
        .fail_compilation(r#"deserialize(1)"#)
        .expect_trait_impl_not_found("Num", &["Self = Variant"]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn serialize_with_type_ascription() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("fn test() -> Variant { Array([serialize(0)]) } test()"),
        variant_t1("Array", array![variant_t1("Int", int(0))])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn json_serialization_roundtrip() {
    let mut session = TestSession::new();
    // bool, low-level JSON functions
    assert_eq!(
        session.run("(deserialize(parse_json(to_json(serialize(true)))): bool)"),
        bool(true)
    );
    // bool
    assert_eq!(
        session.run("(json_decode(json_encode(true)): bool)"),
        bool(true)
    );
    // unit
    assert_eq!(
        session.run("(json_decode(json_encode(())): ())"),
        Value::unit()
    );
    // int
    assert_eq!(session.run("(json_decode(json_encode(42)): int)"), int(42));
    // float
    assert_eq!(
        session.run("(json_decode(json_encode(3.14)): float)"),
        float(3.14)
    );
    // string
    assert_eq!(
        session.run(r#"(json_decode(json_encode("hello")): string)"#),
        string("hello")
    );
    // array of ints
    assert_eq!(
        session.run("(json_decode(json_encode([1, 2, 3])): [int])"),
        int_a![1, 2, 3]
    );
    // array of floats
    assert_eq!(
        session.run("(json_decode(json_encode([1.5, 2.5, 3.5])): [float])"),
        float_a![1.5, 2.5, 3.5]
    );
    // None variant
    assert_eq!(
        session.run("(json_decode(json_encode(None)): None | Some(int))"),
        none()
    );
    // Some(int) variant
    assert_eq!(
        session.run("(json_decode(json_encode(Some((42: int)))): None | Some(int))"),
        some(int(42))
    );
    // tuple
    assert_eq!(
        session.run("(json_decode(json_encode((1, 2.0, true))): (int, float, bool))"),
        tuple!(int(1), float(2.0), bool(true))
    );
    // record
    assert_eq!(
        session.run(r#"(json_decode(json_encode({a: 1, b: true})): {a: int, b: bool})"#),
        tuple!(int(1), bool(true))
    );
    // raw JSON parsing - simple object
    assert_eq!(
        session.run(r#"(json_decode("{\"a\": 1, \"b\": true}"): {a: int, b: bool})"#),
        tuple!(int(1), bool(true))
    );
    // complex object roundtrip with nested array
    assert_eq!(
        session.run(
            r#"(
                json_decode(json_encode({name: "Alice", age: 30, is_student: false, scores: [85.5, 92.0, 78.0]})):
                {age: int, is_student: bool, name: string, scores: [float]}
            )"#
        ),
        tuple!(int(30), bool(false), string("Alice"), float_a![85.5, 92.0, 78.0])
    );
    // raw JSON parsing - complex object with nested array
    let json_str =
        r#"{"name": "Alice", "age": 30, "is_student": false, "scores": [85.5, 92.0, 78.0]}"#;
    assert_eq!(
        session.run(&format!(
            r#"(json_decode("{}"): {{age: int, is_student: bool, name: string, scores: [float]}})"#,
            json_str.replace('"', "\\\"")
        )),
        tuple!(
            int(30),
            bool(false),
            string("Alice"),
            float_a![85.5, 92.0, 78.0]
        )
    );
}
