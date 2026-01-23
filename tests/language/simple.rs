// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;

use indoc::indoc;

use crate::common::{
    get_array_property_value, set_array_property_value, variant_0, variant_t1, variant_tn,
};

use super::common::{
    TestSession, bool, float, get_property_value, int, set_property_value, string, unit,
};
use ferlium::{
    error::{DuplicatedVariantContext, MutabilityMustBeWhat, RuntimeErrorKind},
    mutability::MutType,
    std::{
        array::{Array, array_type_generic},
        math::{float_type, int_type},
    },
    r#type::{Type, tuple_type},
    value::Value,
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn whitespace() {
    let mut session = TestSession::new();
    assert_eq!(session.run(""), unit());
    assert_eq!(session.run(" "), unit());
    assert_eq!(session.run("\t"), unit());
    assert_eq!(session.run(" \t"), unit());
    assert_eq!(session.run("\t "), unit());
    assert_eq!(session.run("\t \t  \t\t\t"), unit());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn literals() {
    let mut session = TestSession::new();
    assert_eq!(session.run("42"), int(42));
    assert_eq!(session.run("from_int(42)"), int(42));
    assert_eq!(session.run("true"), bool(true));
    assert_eq!(session.run("false"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn comments() {
    let mut session = TestSession::new();
    assert_eq!(session.run("42 // comment"), int(42));
    assert_eq!(session.run("42 //comment"), int(42));
    assert_eq!(session.run("42 //comment // //"), int(42));
    assert_eq!(session.run("42 // comment\n"), int(42));
    assert_eq!(session.run("42 // comment\n // comment"), int(42));
    assert_eq!(session.run("// comment\n42"), int(42));
    assert_eq!(session.run("42 /* comment */"), int(42));
    assert_eq!(session.run("42 /**comment**/"), int(42));
    assert_eq!(session.run("/* comment */ 42"), int(42));
    assert_eq!(session.run("/*\ncomment\n*/ 42"), int(42));
    assert_eq!(session.run("/*\ncomment\n*/ 42 // comment"), int(42));
    assert_eq!(
        session.run("/*\ncomment\n*/\n/* yeah */ 42 // comment\n/* sure */\n// ///comment"),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn blocks() {
    let mut session = TestSession::new();
    assert_eq!(session.run("{}"), unit());
    assert_eq!(session.run("{ 1 }"), int(1));
    assert_eq!(session.run("{ true; 1 }"), int(1));
    assert_eq!(session.run("{ 1; true }"), bool(true));
    assert_eq!(session.run("{ {} }"), unit());
    assert_eq!(session.run("{ { 1 } }"), int(1));
    assert_eq!(session.run("{ {}; 1 }"), int(1));
    assert_eq!(session.run("{ { true }; 1 }"), int(1));
    assert_eq!(session.run("{ { 1 }; true }"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn equalities() {
    let mut session = TestSession::new();
    assert_eq!(session.run("42 == 42"), bool(true));
    assert_eq!(session.run("41 == 42"), bool(false));
    assert_eq!(session.run("42 != 42"), bool(false));
    assert_eq!(session.run("41 != 42"), bool(true));
    session
        .fail_compilation("1 == true")
        .expect_trait_impl_not_found("Num", &["Self = bool"]);
    assert_eq!(session.run("true == true"), bool(true));
    assert_eq!(session.run("true == false"), bool(false));
    assert_eq!(session.run("true != true"), bool(false));
    assert_eq!(session.run("true != false"), bool(true));
    assert_eq!(session.run("() == ()"), bool(true));
    assert_eq!(session.run("() != ()"), bool(false));
    session
        .fail_compilation("() == (1,)")
        .expect_type_mismatch("(int,)", "()");
    assert_eq!(session.run("(1,) == (1,)"), bool(true));
    assert_eq!(session.run("(1,) != (1,)"), bool(false));
    assert_eq!(session.run("(1,) == (2,)"), bool(false));
    assert_eq!(session.run("(1,) != (2,)"), bool(true));
    assert_eq!(session.run("(1,true) == (1,true)"), bool(true));
    assert_eq!(session.run("(1,true) != (1,true)"), bool(false));
    assert_eq!(session.run("(1,true) == (2,true)"), bool(false));
    assert_eq!(session.run("(1,true) != (2,true)"), bool(true));
    assert_eq!(session.run("(1,true) == (1,false)"), bool(false));
    assert_eq!(session.run("(1,true) != (1,false)"), bool(true));
    session.fail_compilation("[] == []").expect_unbound_ty_var();
    session.fail_compilation("[] != []").expect_unbound_ty_var();
    assert_eq!(session.run("[] == [1]"), bool(false));
    assert_eq!(session.run("[] != [1]"), bool(true));
    assert_eq!(session.run("[1] == [1]"), bool(true));
    assert_eq!(session.run("[1] != [1]"), bool(false));
    assert_eq!(session.run("[1] == [2]"), bool(false));
    assert_eq!(session.run("[1] != [2]"), bool(true));
    assert_eq!(session.run("let a = [1, 1]; a[0] == a[1]"), bool(true));
    assert_eq!(session.run("let a = [1, 1]; a[0] != a[1]"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn local_variables() {
    let mut session = TestSession::new();
    assert_eq!(session.run("let a = 1 ; a"), int(1));
    assert_eq!(session.run("let mut a = 1 ; a"), int(1));
    assert_eq!(session.run("let mut a = 1 ; a = 2; a"), int(2));
    assert_eq!(session.run("let a = true ; a"), bool(true));
    assert_eq!(session.run("let mut a = true ; a"), bool(true));
    assert_eq!(session.run("let mut a = true ; a = false; a"), bool(false));
    assert_eq!(
        session.run("let mut a = [1, 2]; a = [3, 4, 5]; a"),
        int_a![3, 4, 5]
    );
    assert_eq!(
        session.run("let mut a = [1, 2]; a = [3]; a == [3]"),
        bool(true)
    );
    assert_eq!(
        session.run("let mut a = (1, true); a = (2, false); a == (2, false)"),
        bool(true)
    );
    assert_eq!(session.run("let f = || 1; let a = f(); a"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn type_annotation_in_let() {
    let mut session = TestSession::new();
    assert_eq!(session.run("let a: int = 1 ; a"), int(1));
    assert_eq!(session.run("let a: float = 1 ; a"), float(1.0));
    assert_eq!(session.run("let a: [int] = [] ; a"), int_a![]);
    let fn_def = session.compile_and_get_fn_def("fn id(x) { let a: [_] = x; a }", "id");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args.len(), 1);
    let gen_array_type = array_type_generic();
    assert_eq!(fn_ty.args[0].ty, gen_array_type);
    assert_eq!(fn_ty.ret, gen_array_type);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn type_annotation_in_fn() {
    let mut session = TestSession::new();
    assert_eq!(session.run("fn id(x: int) { x } id(0)"), int(0));
    assert_eq!(session.run("fn id(x: float) { x } id(0)"), float(0.0));
    assert_eq!(session.run("fn id(x: [int]) { x } id([])"), int_a![]);
    assert_eq!(session.run("fn id(x) -> int { x } id(0)"), int(0));
    assert_eq!(session.run("fn id(x) -> float { x } id(0)"), float(0.0));
    assert_eq!(session.run("fn id(x) -> [int] { x } id([])"), int_a![]);
    let gen_array_type = array_type_generic();
    let fn_def = session.compile_and_get_fn_def("fn id(x: [_]) { x }", "id");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args[0].mut_ty, MutType::constant());
    assert_eq!(fn_ty.args[0].ty, gen_array_type);
    assert_eq!(fn_ty.ret, gen_array_type);
    let fn_def = session.compile_and_get_fn_def("fn id(x: &mut [_]) { x }", "id");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args[0].mut_ty, MutType::mutable());
    assert_eq!(fn_ty.args[0].ty, gen_array_type);
    assert_eq!(fn_ty.ret, gen_array_type);
    let fn_def = session.compile_and_get_fn_def("fn id(x) -> [_] { x }", "id");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args[0].ty, gen_array_type);
    assert_eq!(fn_ty.ret, gen_array_type);
    let fn_def = session.compile_and_get_fn_def("fn mkt(a: int, b: float) { (a, b) }", "mkt");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args[0].ty, int_type());
    assert_eq!(fn_ty.args[1].ty, float_type());
    assert_eq!(fn_ty.ret, tuple_type([int_type(), float_type()]));
    let fn_def = session.compile_and_get_fn_def("fn mkt(a, b) -> (int, float) { (a, b) }", "mkt");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args[0].ty, int_type());
    assert_eq!(fn_ty.args[1].ty, float_type());
    assert_eq!(fn_ty.ret, tuple_type([int_type(), float_type()]));
    let fn_def = session.compile_and_get_fn_def("fn ist2(v) -> (_, _) { v }", "ist2");
    let fn_ty = fn_def.ty_scheme.ty();
    let gen0 = Type::variable_id(0);
    let gen1 = Type::variable_id(1);
    let gen_tuple2 = tuple_type([gen0, gen1]);
    assert_eq!(fn_ty.args[0].ty, gen_tuple2);
    assert_eq!(fn_ty.ret, gen_tuple2);
    let fn_def = session.compile_and_get_fn_def("fn f(v: &? int) { v = 1 }", "f");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args[0].mut_ty, MutType::mutable());
    assert_eq!(fn_ty.args[0].ty, int_type());
    assert_eq!(fn_ty.ret, Type::unit());
    let fn_def = session.compile_and_get_fn_def("fn f(v: &? int) { v }", "f");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args[0].mut_ty, MutType::constant());
    assert_eq!(fn_ty.args[0].ty, int_type());
    assert_eq!(fn_ty.ret, int_type());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mutability() {
    let mut session = TestSession::new();
    assert_eq!(session.run("let mut a = 1 ; a = 2; a"), int(2));
    session
        .fail_compilation("let a = 1 ; a = 2; a")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
    assert_eq!(session.run("let mut a = (1,) ; a.0 = 2; a.0"), int(2));
    session
        .fail_compilation("let a = (1,) ; a.0 = 2; a.0")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
    assert_eq!(session.run("let mut a = [1] ; a[0] = 2; a[0]"), int(2));
    session
        .fail_compilation("let a = [1] ; a[0] = 2; a[0]")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
    assert_eq!(
        session.run("let mut a = ([1], 1) ; a.0[0] = 2; a.0[0]"),
        int(2)
    );
    session
        .fail_compilation("let a = ([1], 1) ; a.0[0] = 2; a.0[0]")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn logic_operators() {
    let mut session = TestSession::new();
    // basic usage
    assert_eq!(session.run("not true"), bool(false));
    assert_eq!(session.run("not false"), bool(true));
    assert_eq!(session.run("not not true"), bool(true));
    assert_eq!(session.run("not not false"), bool(false));
    assert_eq!(session.run("not not not true"), bool(false));
    assert_eq!(session.run("not not not false"), bool(true));
    assert_eq!(session.run("true or false"), bool(true));
    assert_eq!(session.run("true and false"), bool(false));
    assert_eq!(session.run("true or true and false"), bool(true));
    assert_eq!(session.run("(true or true) and false"), bool(false));
    // short-circuiting validation
    assert_eq!(
        session.run("let mut a = 0; let mut b = 0; if true or { a = 1; true } { b = 1 }; (a, b)"),
        int_tuple!(0, 1)
    );
    assert_eq!(
        session.run("let mut a = 0; let mut b = 0; if false or { a = 1; true } { b = 1 }; (a, b)"),
        int_tuple!(1, 1)
    );
    assert_eq!(
        session.run("let mut a = 0; let mut b = 0; if true or { a = 1; false } { b = 1 }; (a, b)"),
        int_tuple!(0, 1)
    );
    assert_eq!(
        session.run("let mut a = 0; let mut b = 0; if false or { a = 1; false } { b = 1 }; (a, b)"),
        int_tuple!(1, 0)
    );
    assert_eq!(
        session.run("let mut a = 0; let mut b = 0; if true and { a = 1; true } { b = 1 }; (a, b)"),
        int_tuple!(1, 1)
    );
    assert_eq!(
        session.run("let mut a = 0; let mut b = 0; if false and { a = 1; true } { b = 1 }; (a, b)"),
        int_tuple!(0, 0)
    );
    assert_eq!(
        session.run("let mut a = 0; let mut b = 0; if true and { a = 1; false } { b = 1 }; (a, b)"),
        int_tuple!(1, 0)
    );
    assert_eq!(
        session
            .run("let mut a = 0; let mut b = 0; if false and { a = 1; false } { b = 1 }; (a, b)"),
        int_tuple!(0, 0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn arithmetic_operators() {
    let mut session = TestSession::new();
    assert_eq!(session.run("1+2"), int(3));
    assert_eq!(session.run("  1  + 2 "), int(3));
    assert_eq!(session.run("3*2"), int(6));
    assert_eq!(session.run("1-4"), int(-3));
    assert_eq!(session.run("-1"), int(-1));
    assert_eq!(session.run("--1"), int(1));
    assert_eq!(session.run("---1"), int(-1));
    assert_eq!(session.run("1---5"), int(-4));
    assert_eq!(session.run("1+--5"), int(6));
    assert_eq!(session.run("0-2-2"), int(-4));
    assert_eq!(session.run("0-(2-2)"), int(0));
    assert_eq!(session.run("1+2*3"), int(7));
    assert_eq!(session.run("1.0+2.0"), float(3.0));
    assert_eq!(session.run("  1.0  + 2.0 "), float(3.0));
    assert_eq!(session.run("3.0*2.0"), float(6.0));
    assert_eq!(session.run("1.0-4.0"), float(-3.0));
    assert_eq!(session.run("-1.0"), float(-1.0));
    assert_eq!(session.run("--1.0"), float(1.0));
    assert_eq!(session.run("---1.0"), float(-1.0));
    assert_eq!(session.run("1.0---5.0"), float(-4.0));
    assert_eq!(session.run("1.0+--5.0"), float(6.0));
    assert_eq!(session.run("0.0-2.0-2.0"), float(-4.0));
    assert_eq!(session.run("0.0-(2.0-2.0)"), float(0.0));
    assert_eq!(session.run("1.0+2.0*3.0"), float(7.0));
    assert_eq!(session.run("7 / 2"), float(3.5));
    assert_eq!(session.run("12 / 3 / 2"), float(2.0));
    assert_eq!(session.run("12 / (3 / 2)"), float(8.0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn comparison_operators() {
    let mut session = TestSession::new();
    assert_eq!(session.run("1 < 2"), bool(true));
    assert_eq!(session.run("1 <= 2"), bool(true));
    assert_eq!(session.run("1 > 2"), bool(false));
    assert_eq!(session.run("1 >= 2"), bool(false));
    assert_eq!(session.run("1 != 2"), bool(true));
    assert_eq!(session.run("1 == 2"), bool(false));
    assert_eq!(session.run("2 < 2"), bool(false));
    assert_eq!(session.run("2 <= 2"), bool(true));
    assert_eq!(session.run("2 > 2"), bool(false));
    assert_eq!(session.run("2 >= 2"), bool(true));
    assert_eq!(session.run("2 != 2"), bool(false));
    assert_eq!(session.run("2 == 2"), bool(true));
    assert_eq!(session.run("1.5 < 2.5"), bool(true));
    assert_eq!(session.run("1.5 <= 2.5"), bool(true));
    assert_eq!(session.run("1.5 > 2.5"), bool(false));
    assert_eq!(session.run("1.5 >= 2.5"), bool(false));
    assert_eq!(session.run("1.5 != 2.5"), bool(true));
    assert_eq!(session.run("1.5 == 2.5"), bool(false));
    assert_eq!(session.run("2.5 < 2.5"), bool(false));
    assert_eq!(session.run("2.5 <= 2.5"), bool(true));
    assert_eq!(session.run("2.5 > 2.5"), bool(false));
    assert_eq!(session.run("2.5 >= 2.5"), bool(true));
    assert_eq!(session.run("2.5 != 2.5"), bool(false));
    assert_eq!(session.run("2.5 == 2.5"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn expression_grouping() {
    let mut session = TestSession::new();
    assert_eq!(session.run("(1)"), int(1));
    assert_eq!(session.run("((1))"), int(1));
    assert_eq!(session.run("(((1)))"), int(1));
    assert_eq!(session.run("(((1)))+((2))"), int(3));
    assert_eq!(session.run("1 + (2 * 3)"), int(7));
    assert_eq!(session.run("(1 + 2) * 3"), int(9));
    assert_eq!(session.run("1 + 2 * 3"), int(7));
    assert_eq!(session.run("1 * 2 + 3"), int(5));
    assert_eq!(session.run("1 * (2 + 3)"), int(5));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn if_expr() {
    let mut session = TestSession::new();
    assert_eq!(session.run("if 1 < 2 { () }"), unit());
    assert_eq!(session.run("if 1 < 2 { 1 } else { 2 }"), int(1));
    assert_eq!(session.run("if 1 <= 2 { 1 } else { 2 }"), int(1));
    assert_eq!(session.run("if 1 > 2 { 1 } else { 2 }"), int(2));
    assert_eq!(session.run("if 1 >= 2 { 1 } else { 2 }"), int(2));
    assert_eq!(session.run("if 1 != 2 { 1 } else { 2 }"), int(1));
    assert_eq!(session.run("if 1 == 2 { 1 } else { 2 }"), int(2));
    assert_eq!(session.run("if 2 < 2 { 1 } else { 2 }"), int(2));
    assert_eq!(session.run("if 2 <= 2 { 1 } else { 2 }"), int(1));
    assert_eq!(session.run("if 2 > 2 { 1 } else { 2 }"), int(2));
    assert_eq!(session.run("if 2 >= 2 { 1 } else { 2 }"), int(1));
    assert_eq!(session.run("if 2 != 2 { 1 } else { 2 }"), int(2));
    assert_eq!(session.run("if 2 == 2 { 1 } else { 2 }"), int(1));
    assert_eq!(
        session.run("if true { 1 } else if false { 2 } else { 3 }"),
        int(1)
    );
    assert_eq!(
        session.run("if false { 1 } else if true { 2 } else { 3 }"),
        int(2)
    );
    assert_eq!(
        session.run("if false { 1 } else if false { 2 } else { 3 }"),
        int(3)
    );
    assert_eq!(
        session.run("if false { 1 } else if false { 2 } else if false { 3 } else { 4 }"),
        int(4)
    );
    assert_eq!(
        session.run("let mut a = 0; if false { a = 1 } else if false { a = 2 }; a"),
        int(0)
    );
    assert_eq!(
        session.run("let mut a = 0; if true { a = 1 } else if true { a = 2 }; a"),
        int(1)
    );
    assert_eq!(
        session.run("let mut a = 0; if false { a = 1 } else if true { a = 2 }; a"),
        int(2)
    );
    session
        .fail_compilation("fn a() { if true { 1 } }")
        .expect_trait_impl_not_found("Num", &["Self = ()"]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn match_expr() {
    let mut session = TestSession::new();
    session
        .fail_compilation("match true {}")
        .into_inner()
        .into_empty_match_body()
        .unwrap();
    assert_eq!(session.run("match true { _ => 0 }"), int(0));
    assert_eq!(session.run("match true { true => 0, _ => 1 }"), int(0));
    assert_eq!(session.run("match false { true => 0, _ => 1 }"), int(1));
    assert_eq!(session.run("match true { true => 0, _ => 1, }"), int(0));
    assert_eq!(session.run("match true { false => 1, true => 0 }"), int(0));
    assert_eq!(
        session.run("match false { false => 1, true => 0, }"),
        int(1)
    );
    session
        .fail_compilation("match false { false => 1, true => 0, false => 2 }")
        .into_inner()
        .into_duplicated_literal_pattern()
        .unwrap();
    assert_eq!(
        session
            .fail_compilation("match A { A => 1, A => 2 }")
            .into_inner()
            .into_duplicated_variant()
            .unwrap()
            .3,
        DuplicatedVariantContext::Match
    );
    assert_eq!(session.run("let a = 0; match a { 0 => 1, _ => 3 }"), int(1));
    assert_eq!(
        session.run(
            "let a = -1; match a { -1 => true, 0 => false, -3 => false, 7 => false, _ => false }"
        ),
        bool(true)
    );
    session
        .fail_compilation("let a = 0; match a { 0 => 1 }")
        .into_inner()
        .into_type_values_cannot_be_enumerated()
        .unwrap();
    assert_eq!(session.run("let a = 1; match a { 0 => 1, _ => 3 }"), int(3));
    assert_eq!(
        session.run("let a = 0; match a { 0 => 1, 1 => 2, _ => 3 }"),
        int(1)
    );
    assert_eq!(
        session.run("let a = 1; match a { 0 => 1, 1 => 2, _ => 3 }"),
        int(2)
    );
    assert_eq!(
        session.run("let a = 5; match a { 0 => 1, 1 => 2, _ => 3 }"),
        int(3)
    );
    assert_eq!(session.run("match testing::some_int(0) { _ => 0 }"), int(0));
    assert_eq!(
        session.run("match testing::some_int(0) { Some(x) => 1, None => 0 }"),
        int(1)
    );
    assert_eq!(
        session.run("match testing::some_int(1) { Some(x) => x, None => 0 }"),
        int(1)
    );
    assert_eq!(
        session.run("match testing::pair(1, 2) { Pair(a, b) => a + b }"),
        int(3)
    );
    session
        .fail_compilation("match testing::some_int(0) { None => 0 }")
        .expect_type_mismatch("None | Some (int)", "None");
    session
        .fail_compilation("match testing::some_int(0) { Some(x) => 0 }")
        .expect_type_mismatch("None | Some (int)", "Some (C)");
    // TODO: add more complex literals (tuples, array) once optimisation is in place
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn match_tuples() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
            let mut a = [];
            for l in [false, true] {
                for r in [false, true] {
                    let v = match (l, r) {
                        (true, true) => 1,
                        (true, false) => 2,
                        (false, true) => 3,
                        (false, false) => 4,
                    };
                    array_append(a, v);
                }
            };
            a
        "# }),
        int_a![4, 3, 2, 1]
    );
    assert_eq!(
        session.run(indoc! { r#"
            let mut a = [];
            for l in [false, true] {
                for m in [false, true] {
                    for r in [false, true] {
                        let v = match (l, (m, r)) {
                            (true, (true, true)) => 1,
                            (true, (true, false)) => 2,
                            (true, (false, true)) => 3,
                            (true, (false, false)) => 4,
                            (false, (true, true)) => 5,
                            (false, (true, false)) => 6,
                            (false, (false, true)) => 7,
                            (false, (false, false)) => 8,
                        };
                        array_append(a, v);
                    }
                }
            };
            a
        "# }),
        int_a![8, 7, 6, 5, 4, 3, 2, 1]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn tuple_creation() {
    let mut session = TestSession::new();
    assert_eq!(session.run("()"), unit());
    assert_eq!(session.run("(1,)"), int_tuple!(1));
    assert_eq!(session.run("(1, 2)"), int_tuple!(1, 2));
    assert_eq!(session.run("(1, 2, )"), int_tuple!(1, 2));
    assert_eq!(session.run("(1, 1)"), int_tuple!(1, 1));
    assert_eq!(session.run("(3, 1, 7)"), int_tuple!(3, 1, 7));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn tuple_projection() {
    let mut session = TestSession::new();
    assert_eq!(session.run("(1,).0"), int(1));
    assert_eq!(session.run("(1,2).1"), int(2));
    assert_eq!(session.run("(1,(3, (2, 4, 5))).1.1.2"), int(5));
    assert_eq!(session.run("let a = (1,2); a.0"), int(1));
    assert_eq!(session.run("let a = (1,2); a.1"), int(2));
    assert_eq!(session.run("let f = || (1,2); f().1"), int(2));
    assert_eq!(
        session.run("let f = |x, y| (y == x.1.0); f((1,(2,1)), 2)"),
        bool(true)
    );
    assert_eq!(
        session.run("let f = |x, y| (x.1, x.1.0, y == x.1); f((1,(2,1)), (2,1)); ()"),
        unit()
    );
    assert_eq!(session.run("fn f(v) { v.1.2.3 } ()"), unit());
    assert_eq!(
        session.run("fn a(x) { x.0 } fn b(x) { x.1 } fn c(x) { (a(x), b(x)) } c((1,2))"),
        int_tuple!(1, 2)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn static_function_arity() {
    let mut session = TestSession::new();
    let text = "fn a() { 0 } fn b(x) { x + 1 } fn c(x, y) { x + y }";
    assert_eq!(session.run(&format!("{text} a()")), int(0));
    session
        .fail_compilation(&format!("{text} b()"))
        .expect_wrong_number_of_arguments(1, 0);
    session
        .fail_compilation(&format!("{text} c()"))
        .expect_wrong_number_of_arguments(2, 0);
    session
        .fail_compilation(&format!("{text} a(1)"))
        .expect_wrong_number_of_arguments(0, 1);
    assert_eq!(session.run(&format!("{text} b(1)")), int(2));
    session
        .fail_compilation(&format!("{text} c(1)"))
        .expect_wrong_number_of_arguments(2, 1);
    session
        .fail_compilation(&format!("{text} a(1, 2)"))
        .expect_wrong_number_of_arguments(0, 2);
    session
        .fail_compilation(&format!("{text} b(1, 2)"))
        .expect_wrong_number_of_arguments(1, 2);
    assert_eq!(session.run(&format!("{text} c(1, 2)")), int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn value_function_arity() {
    let mut session = TestSession::new();
    let text = "fn a() { 0 } fn b(x) { x + 1 } fn c(x, y) { x + y + 0 }";
    assert_eq!(session.run(&format!("{text} (a,).0()")), int(0));
    session
        .fail_compilation(&format!("{text} (b,).0()"))
        .expect_type_mismatch("(B) -> B", "() -> A ! e₀");
    session
        .fail_compilation(&format!("{text} (c,).0()"))
        .expect_type_mismatch("(B, B) -> B", "() -> A ! e₀");
    session
        .fail_compilation(&format!("{text} (a,).0(1)"))
        .expect_type_mismatch("() -> C", "(A) -> B ! e₀");
    assert_eq!(session.run(&format!("{text} (b,).0(1)")), int(2));
    session
        .fail_compilation(&format!("{text} (c,).0(1)"))
        .expect_type_mismatch("(C, C) -> C", "(A) -> B ! e₀");
    session
        .fail_compilation(&format!("{text} (a,).0(1, 2)"))
        .expect_type_mismatch("() -> D", "(A, B) -> C ! e₀");
    session
        .fail_compilation(&format!("{text} (b,).0(1, 2)"))
        .expect_type_mismatch("(D) -> D", "(A, B) -> C ! e₀");
    assert_eq!(session.run(&format!("{text} (c,).0(1, 2)")), int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn lambda() {
    let mut session = TestSession::new();
    assert_eq!(session.run("let f = || 1; f()"), int(1));
    assert_eq!(session.run("let f = | | 1; f()"), int(1));
    assert_eq!(session.run("let f = |x| x; f(1)"), int(1));
    assert_eq!(session.run("let f = |x,| x; f(1)"), int(1));
    assert_eq!(session.run("let f = |x, y| x + y; f(1, 2)"), int(3));
    assert_eq!(session.run("let f = |x, y,| x + y; f(1, 2)"), int(3));
    assert_eq!(session.run("let f = |x, y| x + y; f(1, f(2, 3))"), int(6));
    assert_eq!(session.run("let f = |x, y| x + y; f(f(1, 2), 3)"), int(6));
    assert_eq!(
        session.run("let f = |x, y| x + y; f(f(1, 2), f(3, 4))"),
        int(10)
    );
    assert_eq!(
        session.run("let sq = |x| x * x; let inc = |x| x + 1; sq(inc(inc(2)))"),
        int(16)
    );
    session
        .fail_compilation("let id = |x| x; id(1); id(true)")
        .expect_trait_impl_not_found("Num", &["Self = bool"]);
    session
        .fail_compilation("let d = |x, y| (x, y + 1); d(true, 1); d(1, 2)")
        .expect_trait_impl_not_found("Num", &["Self = bool"]);
    assert_eq!(session.run("(||1)()"), int(1));
    assert_eq!(session.run("(|x| x.1)((1,2))"), int(2));
    assert_eq!(
        session.run("let f = |x| x[0] = 1; let mut a = [0]; f(a); a"),
        int_a!(1)
    );
    assert_eq!(session.run("fn a() { |x| x + x } a()((1: int))"), int(2));
    assert_eq!(
        session.run("fn a() { |x| x + x } a()((1: float))"),
        float(2.0)
    );
    session
        .fail_compilation(indoc! {"
            fn swap(a, b) {
            let t = a;
            a = b;
            b = t;
        }

        let a = || {
            let mut r = [1, 2];
            swap(r[0], r[0])
        };
        a()"})
        .as_mutable_paths_overlap()
        .unwrap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn closures() {
    let mut session = TestSession::new();
    // Basic capture.
    assert_eq!(session.run("let a = 3.3; let f = || a; f()"), float(3.3));
    assert_eq!(session.run("let a = 3; let f = || a; (f(): int)"), int(3));
    assert_eq!(
        session.run("let a = 3; let f = || a; (f(): float)"),
        float(3.0)
    );
    // Capture in functions.
    assert_eq!(
        session.run("fn f() { let b = 1; |x| x + b } f()(1.0)"),
        float(2.0)
    );
    assert_eq!(
        session.run("fn f() { let b = 1; |x| x + b } (f()(1): int)"),
        int(2)
    );
    // Independence from outer mutation.
    assert_eq!(
        session.run("let mut a = 1; let f = || a; a = 2; f()"),
        int(1)
    );
    // Independence of outer from inner mutation.
    assert_eq!(
        session.run("let mut a = 1; let f = || { a = 2; a }; f(); a"),
        int(1)
    );
    // Statelessness of closures.
    assert_eq!(
        session.run("let mut a = 1; let f = || { a = a + 1; a }; f() + f()"),
        int(4)
    );
    // Deep copy of mutable structures (arrays)
    assert_eq!(
        session.run("let mut a = [1]; let f = || a[0]; a[0] = 2; f()"),
        int(1)
    );
    // Capture in nested scopes.
    assert_eq!(
        session.run("let f = || { let mut a = 1; let g = || a; a = 2; g() }; f()"),
        int(1)
    );
    assert_eq!(
        session.run("let a = 3.3; let f = || { let b = 1.2; || a + b }; f()()"),
        float(4.5)
    );
    assert_eq!(
        session.run("let a = 3; let f = || { let b = 1; || a + b }; (f()(): int)"),
        int(4)
    );
    assert_eq!(
        session.run("let a = 3; let f = || { let b: int = 1; || a + b }; f()()"),
        int(4)
    );
    assert_eq!(
        session.run("let a = \"hi\"; let f = || { let a = 3; let b: int = 1; || a + b }; f()()"),
        int(4)
    );
    // Capture in function calls.
    assert_eq!(
        session.run("fn plus0(f) { f() + 0.0 } let x = 2.0; plus0(|| x)"),
        float(2.0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment() {
    let mut session = TestSession::new();
    assert_eq!(session.run("let a = 1; a"), int(1));
    assert_eq!(session.run("let mut a = 1; a = 2"), unit());
    assert_eq!(session.run("let mut a = 1; a = 2; a"), int(2));
    assert_eq!(session.run("let mut a = 1; let b = 2; a = b; a"), int(2));
    assert_eq!(session.run("let mut a = 1; let b = 2; a = b; b"), int(2));
    assert_eq!(
        session.run("let mut a = 1; let mut b = 2; a = b; b = a; b"),
        int(2)
    );
    assert_eq!(
        session.run("let mut a = (1, 2); a.0 = 3; a"),
        int_tuple!(3, 2)
    );
    assert_eq!(
        session.run("let mut a = ((1, 2), 3); a.0.1 = 5; a.0"),
        int_tuple!(1, 5)
    );
    assert_eq!(session.run("let mut a = [1, 2]; a[0] = 3; a"), int_a![3, 2]);
    assert_eq!(
        session.run("let mut a = [[1, 2], [3, 4]]; a[0][1] = 5; a[0]"),
        int_a![1, 5]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn op_assignment() {
    let mut session = TestSession::new();
    assert_eq!(session.run("let mut a = 4; a += 1; a"), int(5));
    assert_eq!(session.run("let mut a = 4; a -= 1; a"), int(3));
    assert_eq!(session.run("let mut a = 4; a *= 2; a"), int(8));
    assert_eq!(session.run("let mut a = 4; a /= 2; a"), float(2.0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn for_loops_with_range() {
    let mut session = TestSession::new();
    assert_eq!(session.run("for i in 0..3 { () }"), unit());
    assert_eq!(
        session.run("let mut s = 0; for i in 1..4 { s = s + i }; s"),
        int(6)
    );
    assert_eq!(
        session.run("let mut s = 0; for i in -1..-4 { s = s + i }; s"),
        int(-6)
    );
    assert_eq!(
        session.run("let mut a = []; for i in 2..5 { array_append(a, i) }; a"),
        int_a![2, 3, 4]
    );
    assert_eq!(
        session.run(
            "fn s() { 2 } fn e() { 5 } let mut a = []; for i in s()..e() { array_append(a, i) }; a"
        ),
        int_a![2, 3, 4]
    );
    assert_eq!(
        session.run("let mut a = []; for i in 5..2 { array_append(a, i) }; a"),
        int_a![5, 4, 3]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn for_loops_with_inclusive_range() {
    let mut session = TestSession::new();
    assert_eq!(session.run("for i in 0..=3 { () }"), unit());
    assert_eq!(
        session.run("let mut s = 0; for i in 1..=4 { s = s + i }; s"),
        int(10)
    );
    assert_eq!(
        session.run("let mut s = 0; for i in -1..=-4 { s = s + i }; s"),
        int(-10)
    );
    assert_eq!(
        session.run("let mut a = []; for i in 2..=5 { array_append(a, i) }; a"),
        int_a![2, 3, 4, 5]
    );
    assert_eq!(
        session.run(
            "fn s() { 2 } fn e() { 5 } let mut a = []; for i in s()..=e() { array_append(a, i) }; a"
        ),
        int_a![2, 3, 4, 5]
    );
    assert_eq!(
        session.run("let mut a = []; for i in 5..=2 { array_append(a, i) }; a"),
        int_a![5, 4, 3, 2]
    );
    assert_eq!(
        session.run("let mut s = 0; for i in 1..=1 { s = s + i }; s"),
        int(1)
    );
    assert_eq!(
        session.run("let mut a = []; for i in 1..=0 { array_append(a, i) }; a"),
        int_a![1, 0]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn for_loops_with_arrays() {
    let mut session = TestSession::new();
    assert_eq!(session.run("for i in [0, 1, 2] { () }"), unit());
    assert_eq!(
        session.run("let mut s = 0; for i in [1, 2, 3] { s = s + i }; s"),
        int(6)
    );
    assert_eq!(
        session.run("let mut s = 0.5; for i in [1.5, 2.5, 3.5] { s = s + i }; s"),
        float(8.0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_functions() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(
            r#"fn my_add(x, y) {
            x + y
        }
        let x = my_add;
        x(1, 2)"#
        ),
        int(3)
    );
    assert_eq!(
        session.run(
            r#"fn my_add(x, y) {
            x + y
        }
        fn my_sub(x, y) {
            x - y
        }
        let mut x = my_add;
        x = my_sub;
        x(1, 2)"#
        ),
        int(-1)
    );
    assert_eq!(
        session.run("fn fact(i) { if i > 1 { i * ((fact,).0)(i - 1) } else { 1 } } fact(3)"),
        int(6)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn records() {
    let mut session = TestSession::new();
    assert_eq!(session.run("{a:1}.a"), int(1));
    assert_eq!(session.run("{a:1, b:2}.a"), int(1));
    assert_eq!(session.run("{a:1, b:2}.b"), int(2));
    let s = "{a:1, a:2}";
    session
        .fail_compilation(s)
        .expect_duplicate_record_field(s, "a");
    let s = "{a:1, a:true, b:2}";
    session
        .fail_compilation(s)
        .expect_duplicate_record_field(s, "a");
    assert_eq!(session.run("(|| {a:1, b:2})().a"), int(1));
    assert_eq!(session.run("(|| {a:1, b:2})().b"), int(2));
    assert_eq!(session.run("let r = || {a:1, b:2}; r().a + r().b"), int(3));
    assert_eq!(
        session.run("let r = || {a:1, a_o: true, b:2}; r().a + r().b"),
        int(3)
    );
    assert_eq!(session.run("fn s(v) { v.x + v.y } s({x:1, y:2})"), int(3));
    assert_eq!(
        session.run("fn s(v) { v.x + v.y } s({name: \"toto\", x:1, y:2})"),
        int(3)
    );
    assert_eq!(
        session.run("fn s(v) { v.x + v.y } s({name: \"toto\", x:1, z: true, y:2, noise: (1,2)})"),
        int(3)
    );
    assert_eq!(
        session.run("fn sq(x) { x * x } fn l2(v) { sq(v.x) + sq(v.y) } l2({x:1, y:2})"),
        int(5)
    );
    assert_eq!(session.run("let f = |x| x.a; f({a:1})"), int(1));
    assert_eq!(session.run("fn e(v) { v.toto } (e,).0({toto: 3})"), int(3));
    assert_eq!(
        session.run("fn e(v) { v.toto } let a = e; a({toto: 3})"),
        int(3)
    );
    assert_eq!(
        session.run("let l2 = |v| { let sq = |x| x * x; sq(v.x) + sq(v.y) }; l2({x:1, y:2})"),
        int(5)
    );
    assert_eq!(
        session.run(
            "let l = |v| { let ex = |v| v.x; let ey = |v| v.y; ex(v) + ey(v) }; l({a: true, x:1, x_n: \"hi\", y:2, y_n: false})"
        ),
        int(3)
    );
    assert_eq!(session.run("(|v| v.x + v.y)({x:1, y:2})"), int(3));
    assert_eq!(
        session.run("fn s(v) { v.x + v.y } ((s,).0)({x:1, bla: true, y:2})"),
        int(3)
    );
    assert_eq!(
        session.run("fn a(x) { x.a } fn b(x) { a(x) } b({a:3})"),
        int(3)
    );
    assert_eq!(
        session.run("fn a(x) { x.a } fn b(x) { x.b } fn c(x, y) { (a(x), b(y)) } c({a:1},{b:2})"),
        int_tuple!(1, 2)
    );
    assert_eq!(
        session.run(
            "fn sum(i, l) { if i < l.count { sum(i + 1, l) + 1 } else { 0 } } sum(0, {count: 4})"
        ),
        int(4)
    );
    assert_eq!(
        session.run("fn a(x) { x.a } fn b(x) { ((a,).0)(x) } b({a: 3})"),
        int(3)
    );
    assert_eq!(
        session.run("let f = |x, y| (x.a, x.a.b, y == x.a); f({a: {a: 3, b: 1}}, {a: 4, b: 1})"),
        Value::tuple([int_tuple!(3, 1), int(1), bool(false)])
    );
    assert_eq!(
        session.run("fn l(v) { ((|v| v.x)(v), (|v| v.y)(v)) } l({x:1, y:2})"),
        int_tuple!(1, 2)
    );
    assert_eq!(
        session.run("fn l(v) { let x = |v| v.x; let y = |v| v.y; (x(v), y(v)) } l({x:1, y:2})"),
        int_tuple!(1, 2)
    );
    assert_eq!(
        session.run("fn l(v) { (((|v| v.x),).0(v), ((|v| v.y),).0(v)) } l({x:1, y:2})"),
        int_tuple!(1, 2)
    );
    assert_eq!(
        session.run(
            "fn x() { |v| v.x } fn y() { |v| v.y } fn e(v) { (x()(v), y()(v)) } e({x:1, y:2})"
        ),
        int_tuple!(1, 2)
    );
    session.fail_compilation(
        "fn swap(a,b) { let mut temp = a; a = b; b = temp } let mut v = { x:1, y:2 }; swap(v.x, v.x)",
    )
    .expect_mutable_paths_overlap();

    // Record field abbreviation syntax tests
    // Single abbreviated field requires trailing comma to distinguish from block
    assert_eq!(session.run("let a = 1; {a,}.a"), int(1));
    // Two abbreviated fields
    assert_eq!(session.run("let a = 1; let b = 2; {a, b}.a"), int(1));
    assert_eq!(session.run("let a = 1; let b = 2; {a, b}.b"), int(2));
    // Mixed: explicit first, then abbreviated
    assert_eq!(session.run("let b = 2; {a: 1, b}.a"), int(1));
    assert_eq!(session.run("let b = 2; {a: 1, b}.b"), int(2));
    // Mixed: abbreviated first, then explicit
    assert_eq!(session.run("let a = 1; {a, b: 2}.a"), int(1));
    assert_eq!(session.run("let a = 1; {a, b: 2}.b"), int(2));
    // Trailing comma after single explicit field is optional
    assert_eq!(session.run("{a: 1}.a"), int(1));
    assert_eq!(session.run("{a: 1,}.a"), int(1));
    // Trailing comma with multiple fields
    assert_eq!(session.run("let a = 1; let b = 2; {a, b,}.a"), int(1));
    assert_eq!(session.run("{a: 1, b: 2,}.b"), int(2));
    // Abbreviated with more complex expressions
    assert_eq!(
        session.run("fn make_rec() { let x = 10; let y = 20; {x, y} } make_rec().x"),
        int(10)
    );
    assert_eq!(
        session.run("fn make_rec() { let x = 10; let y = 20; {x, y} } make_rec().y"),
        int(20)
    );
    // Using abbreviated in function arguments
    assert_eq!(
        session.run("fn s(v) { v.x + v.y } let x = 1; let y = 2; s({x, y})"),
        int(3)
    );
    // Three or more abbreviated fields
    assert_eq!(
        session.run("let a = 1; let b = 2; let c = 3; {a, b, c}.c"),
        int(3)
    );
    // Deeply nested with abbreviation
    assert_eq!(
        session.run("let inner = 5; let outer = {inner,}; outer.inner"),
        int(5)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn variants() {
    let mut session = TestSession::new();
    // tuple constructors
    assert_eq!(session.run("MyVariant"), variant_0("MyVariant"));
    assert_eq!(
        session.run("MyVariant2(1.0)"),
        variant_t1("MyVariant2", float(1.0))
    );
    assert_eq!(
        session.run("MyVariant2(1.0, 2.0)"),
        variant_tn("MyVariant2", [float(1.0), float(2.0)])
    );
    // Note: the following doesn't work due to a bug in recursive application of type defaulting substitution
    // (see https://github.com/enlightware/ferlium/issues/59)
    //assert_eq!(session.run("MyVariant2(\"hi\", 1)"), variant_tn("MyVariant2", [string("hi"), int(1)]));
    assert_eq!(
        session.run("MyVariant2(\"hi\", 1.0)"),
        variant_tn("MyVariant2", [string("hi"), float(1.0)])
    );

    // record constructors
    assert_eq!(
        session.run("MyVariant2 { a: 1.0 }"),
        variant_t1("MyVariant2", float(1.0))
    );
    assert_eq!(
        session.run("MyVariant2 { b: 2.0, a: 1.0 }"),
        variant_tn("MyVariant2", [float(1.0), float(2.0)])
    );
    // Note: the following doesn't work due to a bug in recursive application of type defaulting substitution
    // (see https://github.com/enlightware/ferlium/issues/59)
    //assert_eq!(session.run("MyVariant2(\"hi\", 1)"), variant_tn("MyVariant2", [string("hi"), int(1)]));
    assert_eq!(
        session.run("MyVariant2 { name: \"hi\", value: 1.0 }"),
        variant_tn("MyVariant2", [string("hi"), float(1.0)])
    );

    // option example
    let match_exhaustive = r#"fn s(x) { match x { None => "no", Some(x) => f"hi {x}" } }"#;
    assert_eq!(
        session.run(&format!("{match_exhaustive} s(Some(1))")),
        string("hi 1")
    );
    assert_eq!(
        session.run(&format!("{match_exhaustive} s(None)")),
        string("no")
    );
    assert_eq!(
        session.run(&format!("{match_exhaustive} fn f() {{ s(Some(1)) }} f()")),
        string("hi 1")
    );
    assert_eq!(
        session.run(&format!(
            "{match_exhaustive} fn f() {{ let a = 1; s(Some(a)) }} f()"
        )),
        string("hi 1")
    );
    assert_eq!(
        session.run(&format!("{match_exhaustive} fn f() {{ s(None) }} f()")),
        string("no")
    );
    let match_open = r#"fn s(x) { match x { None => "no", Some(x) => f"hi {x}", _ => "?" } }"#;
    assert_eq!(
        session.run(&format!("{match_open} s(Some(1))")),
        string("hi 1")
    );
    assert_eq!(session.run(&format!("{match_open} s(None)")), string("no"));
    assert_eq!(
        session.run(&format!("{match_open} fn f() {{ s(Some(1)) }} f()")),
        string("hi 1")
    );
    assert_eq!(
        session.run(&format!(
            "{match_open} fn f() {{ let a = 1; s(Some(a)) }} f()"
        )),
        string("hi 1")
    );
    assert_eq!(
        session.run(&format!("{match_open} fn f() {{ s(None) }} f()")),
        string("no")
    );

    // area example
    let match_exhaustive = r#"fn a(x) { match x { Square(r) => r * r, Rect(w, h) => w * h } }"#;
    assert_eq!(
        session.run(&format!("{match_exhaustive} a(Square(3))")),
        int(9)
    );
    assert_eq!(
        session.run(&format!("{match_exhaustive} a(Rect(3, 2))")),
        int(6)
    );
    assert_eq!(
        session.run(&format!("{match_exhaustive} let y = 2; a(Rect(3, y))")),
        int(6)
    );
    assert_eq!(
        session.run(&format!(
            "{match_exhaustive} let x = 3; let y = 2; a(Rect(x, y))"
        )),
        int(6)
    );
    let match_open = r#"fn a(x) { match x { Square(r) => r * r, Rect(w, h) => w * h, _ => 0 } }"#;
    assert_eq!(session.run(&format!("{match_open} a(Square(3))")), int(9));
    assert_eq!(session.run(&format!("{match_open} a(Rect(3, 2))")), int(6));
    assert_eq!(
        session.run(&format!("{match_open} let y = 2; a(Rect(3, y))")),
        int(6)
    );
    assert_eq!(
        session.run(&format!("{match_open} let x = 3; let y = 2; a(Rect(x, y))")),
        int(6)
    );
    assert_eq!(
        session.run(&format!("{match_open} a(Triangle(3, 3, 5))")),
        int(0)
    );
    assert_eq!(
        session.run(&format!(
            "{match_open} let x = 3; let y = 3; let z = 5; a(Triangle(x, y, z))"
        )),
        int(0)
    );

    // match with record
    let match_exhaustive_rec = r#"fn s(x) {
        match x {
            A { a } => a,
            B { a, b } => a + b
        }
    }"#;
    assert_eq!(
        session.run(&format!("{match_exhaustive_rec} s(A {{ a: 1.0 }})")),
        float(1.0)
    );
    assert_eq!(
        session.run(&format!("{match_exhaustive_rec} s(B {{ a: 2.0, b: 3.0 }})")),
        float(5.0)
    );
    let match_open_rec = r#"fn s(x) {
        match x {
            A { a } => a,
            B { a, b } => a + b,
            _ => 0.0
        }
    }"#;
    assert_eq!(
        session.run(&format!("{match_open_rec} s(A {{ a: 1.0 }})")),
        float(1.0)
    );
    assert_eq!(
        session.run(&format!("{match_open_rec} s(B {{ a: 2.0, b: 3.0 }})")),
        float(5.0)
    );
    assert_eq!(
        session.run(&format!("{match_open_rec} s(C {{ z: \"hi\" }})")),
        float(0.0)
    );

    // match mixed
    let match_exhaustive_mixed = r#"fn s(x) {
        match x {
            Quit => 0.0,
            Jump(h) => h,
            Move { y, x } => x - y,
        }
    }"#;
    assert_eq!(
        session.run(&format!("{match_exhaustive_mixed} s(Quit)")),
        float(0.0)
    );
    assert_eq!(
        session.run(&format!("{match_exhaustive_mixed} s(Jump(2.0))")),
        float(2.0)
    );
    assert_eq!(
        session.run(&format!(
            "{match_exhaustive_mixed} s(Move {{ x: 3.0, y: 1.0 }} )"
        )),
        float(2.0)
    );
    let match_open_mixed = r#"fn s(x) {
        match x {
            Quit => 0.0,
            Jump(h) => h,
            Move { y, x } => x - y,
            _ => -1.0
        }
    }"#;
    assert_eq!(
        session.run(&format!("{match_open_mixed} s(Quit)")),
        float(0.0)
    );
    assert_eq!(
        session.run(&format!("{match_open_mixed} s(Jump(2.0))")),
        float(2.0)
    );
    assert_eq!(
        session.run(&format!("{match_open_mixed} s(Move {{ x: 3.0, y: 1.0 }} )")),
        float(2.0)
    );
    assert_eq!(
        session.run(&format!("{match_open_mixed} s(Bla)")),
        float(-1.0)
    );
    assert_eq!(
        session.run(&format!("{match_open_mixed} s(Oh(1.0, true))")),
        float(-1.0)
    );
    assert_eq!(
        session.run(&format!("{match_open_mixed} s(Teleport {{ z: -4.0 }})")),
        float(-1.0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn adt() {
    let mut session = TestSession::new();
    session
        .fail_compilation("fn f(x) { (x.0, x.a) }")
        .expect_inconsistent_adt();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mutability_soundness() {
    let mut session = TestSession::new();
    session
        .fail_compilation("let f = |x| (x[0] = 1); let a = [1]; f(a)")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn borrow_checker() {
    let mut session = TestSession::new();
    let swap_fn = "fn swap(a, b) { let temp = b; b = a; a = temp }";
    assert_eq!(
        session.run(&format!(
            "{swap_fn} let mut a = [0, 1]; swap(a[0], a[1]); a"
        )),
        int_a![1, 0]
    );
    session
        .fail_compilation(&format!(
            "{swap_fn} let mut a = [0, 1]; swap(a[0], a[0]); a"
        ))
        .expect_mutable_paths_overlap();
    session
        .fail_compilation(&format!(
            "{swap_fn} let mut a = [0, 1]; let i = 0; swap(a[0], a[i]); a"
        ))
        .expect_mutable_paths_overlap();
    assert_eq!(
        session.run(&format!(
            "{swap_fn} let mut a = [0]; let mut b = [1]; swap(a[0], b[0]); a"
        )),
        int_a![1]
    );
    assert_eq!(
        session.run(&format!(
            "{swap_fn} let mut a = [0]; let mut b = [1]; swap(a[a[0]], b[0]); a"
        )),
        int_a![1]
    );
    assert_eq!(
        session.run(&format!(
            "{swap_fn} let mut a = [0]; let mut b = [1]; swap(a[a[0]], b[a[0]]); a"
        )),
        int_a![1]
    );
    assert_eq!(
        session.run(&format!(
            "{swap_fn} let mut a = ((0,1),2); swap(a.0.1, a.1); a.0"
        )),
        int_tuple!(0, 2)
    );
    assert_eq!(
        session.run(&format!(
            "{swap_fn} let mut a = ((0,1),2); swap(a.0.1, a.0.0); a.0"
        )),
        int_tuple!(1, 0)
    );
    session
        .fail_compilation(&format!(
            "{swap_fn} let mut a = ((0,1),2); swap(a.0, a.0); a.0"
        ))
        .expect_mutable_paths_overlap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn execution_errors() {
    let mut session = TestSession::new();
    use RuntimeErrorKind::*;
    assert_eq!(session.fail_run("abort()"), Aborted(None));
    assert_eq!(
        session.fail_run("panic(\"oh no\")"),
        Aborted(Some("oh no".into()))
    );
    assert_eq!(session.fail_run("1.0 / 0.0"), DivisionByZero);
    assert_eq!(
        session.fail_run("let v = || 0.0; 1.0 / v()"),
        DivisionByZero
    );
    assert_eq!(session.fail_run("idiv(1, 0)"), DivisionByZero);
    assert_eq!(
        session.fail_run("let v = || 0; idiv(1, v())"),
        DivisionByZero
    );
    assert_eq!(session.fail_run("rem(1, 0)"), RemainderByZero);
    assert_eq!(session.fail_run("mod(1, 0)"), RemainderByZero);
    assert_eq!(
        session.fail_run("let v = || 0; rem(1, v())"),
        RemainderByZero
    );
    assert_eq!(
        session.fail_run("let v = || 0; mod(1, v())"),
        RemainderByZero
    );
    assert_eq!(
        session.fail_run("[1][1]"),
        ArrayAccessOutOfBounds { index: 1, len: 1 }
    );
    assert_eq!(
        session.fail_run("let a = [1, 2]; a[3]"),
        ArrayAccessOutOfBounds { index: 3, len: 2 }
    );
    assert_eq!(
        session.fail_run("let a = [1, 2]; a[-3]"),
        ArrayAccessOutOfBounds { index: -3, len: 2 }
    );
    assert_eq!(
        session.fail_run("let mut a = [1, 2]; a[3] = 0"),
        ArrayAccessOutOfBounds { index: 3, len: 2 }
    );
    assert_eq!(
        session.fail_run("let mut a = [1, 2]; a[-3] = 0"),
        ArrayAccessOutOfBounds { index: -3, len: 2 }
    );
    assert_eq!(
        session.fail_run("let i = || 3; let a = [1, 2]; a[i()]"),
        ArrayAccessOutOfBounds { index: 3, len: 2 }
    );
    assert_eq!(
        session.fail_run("let i = || -3; let a = [1, 2]; a[i()]"),
        ArrayAccessOutOfBounds { index: -3, len: 2 }
    );
    assert_eq!(
        session.fail_run("let i = || 3; let mut a = [1, 2]; a[i()] = 0"),
        ArrayAccessOutOfBounds { index: 3, len: 2 }
    );
    assert_eq!(
        session.fail_run("let i = || -3; let mut a = [1, 2]; a[i()] = 0"),
        ArrayAccessOutOfBounds { index: -3, len: 2 }
    );
    assert_eq!(
        session.fail_run("fn rf() { rf() } rf() + 0"),
        RecursionLimitExceeded { limit: 50 }
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn never_type() {
    let mut session = TestSession::new();
    use RuntimeErrorKind::*;
    assert_eq!(session.run("if true { 2 } else { abort() }"), int(2));
    assert_eq!(
        session.fail_run("if false { 2 } else { abort() }"),
        Aborted(None)
    );
    assert_eq!(
        session.fail_run("if true { abort() } else { 2 }"),
        Aborted(None)
    );
    assert_eq!(session.run("if false { abort() } else { 2 }"), int(2));
    assert_eq!(
        session.run("log(if true { 2 } else { abort() })"),
        Value::unit()
    );
    assert_eq!(
        session.fail_run("log(if false { 2 } else { abort() })"),
        Aborted(None)
    );
    assert_eq!(
        session.fail_run("log(if true { abort() } else { 2 })"),
        Aborted(None)
    );
    assert_eq!(
        session.run("log(if false { abort() } else { 2 })"),
        Value::unit()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_creation() {
    let mut session = TestSession::new();
    session.fail_compilation("[]").expect_unbound_ty_var();
    assert_eq!(session.run("[1]"), int_a![1]);
    assert_eq!(session.run("[1,]"), int_a![1]);
    assert_eq!(session.run("[1, 2]"), int_a![1, 2]);
    assert_eq!(session.run("[1, 2,]"), int_a![1, 2]);
    assert_eq!(session.run("[1, 1]"), int_a![1, 1]);
    assert_eq!(session.run("[3, 1, 7]"), int_a![3, 1, 7]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_index() {
    let mut session = TestSession::new();
    assert_eq!(session.run("[1][0]"), int(1));
    assert_eq!(session.run("[1][-1]"), int(1));
    assert_eq!(session.run("[1, 3][0]"), int(1));
    assert_eq!(session.run("[1, 3][1]"), int(3));
    assert_eq!(session.run("[1, 3][-1]"), int(3));
    assert_eq!(session.run("[1, 3][-2]"), int(1));
    assert_eq!(session.run("[[1, 2], [3, 4]][1][0]"), int(3));
    assert_eq!(session.run("let a = [1, 3]; a[0]"), int(1));
    assert_eq!(session.run("let a = [1, 3]; a[1]"), int(3));
    assert_eq!(session.run("let i = 0; [1, 3][i]"), int(1));
    assert_eq!(session.run("let i = 1; [1, 3][i]"), int(3));
    assert_eq!(session.run("let i = -1; [1, 3][i]"), int(3));
    assert_eq!(session.run("let i = -2; [1, 3][i]"), int(1));
    assert_eq!(
        session.run("let i = 0; let j = 1; [[1, 2], [3, 4]][i][j]"),
        int(2)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_literals() {
    let mut session = TestSession::new();
    assert_eq!(session.run(r#""""#), string(""));
    assert_eq!(session.run(r#""hello world""#), string("hello world"));
    assert_eq!(
        session.run(r#""hello \"world\"""#),
        string(r#"hello "world""#)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_formatting() {
    let mut session = TestSession::new();
    assert_eq!(session.run(r#"f"hello world""#), string("hello world"));
    assert_eq!(
        session.run(r#"let a = 1; let b = true; f"hello {a} world {b}""#),
        string("hello 1 world true")
    );
    assert_eq!(
        session.run(r#"let a = [1, 2]; let b = (0, true, "hi"); f"hello {a} world {b}""#),
        string("hello [1, 2] world (0, true, hi)")
    );
    assert_eq!(
        session.run(r#"fn nbr(x) { f" #{x}" } nbr(3)"#),
        string(" #3")
    );
    let s = r#"f"hello {a} world""#;
    session
        .fail_compilation(s)
        .expect_undefined_var_in_string_formatting(s, "a");
    let s = r#"let a = 1; f"{a} is {b}""#;
    session
        .fail_compilation(s)
        .expect_undefined_var_in_string_formatting(s, "b");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn to_string() {
    let mut session = TestSession::new();
    assert_eq!(session.run("to_string(true)"), string("true"));
    assert_eq!(session.run("to_string(false)"), string("false"));
    assert_eq!(session.run("to_string(1)"), string("1"));
    assert_eq!(session.run("to_string(-17)"), string("-17"));
    assert_eq!(session.run("to_string(0.0)"), string("0"));
    assert_eq!(session.run("to_string(0.1)"), string("0.1"));
    assert_eq!(
        session.run("to_string(\"hello world\")"),
        string("hello world")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn modules() {
    let mut session = TestSession::new();
    assert_eq!(session.run("fn a(x) { x }"), unit());
    assert_eq!(session.run("fn a(x) { x } a(1)"), int(1));
    assert_eq!(session.run("fn a(x) { x + 1 } a(1)"), int(2));
    assert_eq!(
        session.run("fn d(x) { 2 * x } fn s(x) { x + 1 } d(s(s(1)))"),
        int(6)
    );
    session
        .fail_compilation("fn a() {} fn a() {}")
        .expect_name_defined_multiple_times("a");
    session
        .fail_compilation("struct a; fn a() {}")
        .expect_name_defined_multiple_times("a");
    session
        .fail_compilation("struct a(int, bool) fn a() {}")
        .expect_name_defined_multiple_times("a");
    session
        .fail_compilation("struct a { x: int } fn a() {}")
        .expect_name_defined_multiple_times("a");
    session
        .fail_compilation("enum a {} fn a() {}")
        .expect_name_defined_multiple_times("a");
    session
        .fail_compilation("enum a { True, False } fn a() {}")
        .expect_name_defined_multiple_times("a");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn deep_modules() {
    let mut session = TestSession::new();
    // Test that the same function name can exist in different modules.
    assert_eq!(
        session.run("(deep::level1::level(), deep::deeper::level2::level())"),
        int_tuple!(1, 2)
    );
    // Validate newtype equality when from same module.
    assert_eq!(
        session.run("deep::level1::Pair(1, 2) == deep::level1::Pair(1, 2)"),
        bool(true),
    );
    // Validate newtype inequality when from different modules.
    session
        .fail_compilation("deep::level1::Pair(1, 2) == deep::deeper::level2::Pair(1, 2)")
        .as_named_type_mismatch()
        .unwrap();
    // Validate first-class function passing between modules.
    assert_eq!(
        session.run("deep::deeper::level2::receiver(deep::level1::sender())"),
        float(2.5)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_functions() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("fn fact(x) { if x > 1 { x * fact(x-1) } else { 1 } } fact(5)"),
        int(120)
    );
    assert_eq!(
        session.run(
            r#"fn is_even(n) {
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

            is_even(10)"#
        ),
        bool(true)
    );
    assert_eq!(
        session.run("fn f(a) { let p = g(a); } fn g(a) { 0 }"),
        unit()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fn_pipes() {
    let mut session = TestSession::new();
    assert_eq!(session.run("1 |> add(1)"), int(2));
    assert_eq!(session.run("2 |> mul(3) |> add(1) |> div(2)"), float(3.5));
    assert_eq!(
        session.run("let mut a = 1; a = 2 |> mul(3) |> add(1) |> div(2); a"),
        float(3.5)
    );
    assert_eq!(
        session.run("[1, 2] |> array_concat([3, 4]) |> array_map(|x| x*x)"),
        int_a![1, 4, 9, 16]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn properties() {
    let mut session = TestSession::new();
    // simple value
    set_property_value(0);
    assert_eq!(session.run("@props::my_scope.my_var"), int(0));
    set_property_value(1);
    assert_eq!(session.run("@props::my_scope.my_var"), int(1));
    session.run("@props::my_scope.my_var = 2");
    assert_eq!(get_property_value(), 2);
    session.run("@props::my_scope.my_var = @props::my_scope.my_var * 2 + 3");
    assert_eq!(get_property_value(), 7);
    session.run("fn f(x) { x * 2 } @props::my_scope.my_var = f(@props::my_scope.my_var)");
    assert_eq!(get_property_value(), 14);
    session
        .fail_compilation("@props::my_scope.my_var.a")
        .into_inner()
        .into_invalid_record_field_access()
        .unwrap();
    session
        .fail_compilation("@props::my_scope.my_var.a = 2")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);

    // array value
    set_array_property_value(Array::new());
    assert_eq!(session.run("@props::my_scope.my_array"), int_a![]);
    session.run("@props::my_scope.my_array = [1, 2]");
    assert_eq!(session.run("@props::my_scope.my_array"), int_a![1, 2]);
    session.run("@props::my_scope.my_array = array_concat(@props::my_scope.my_array, [3, 4])");
    assert_eq!(session.run("@props::my_scope.my_array"), int_a![1, 2, 3, 4]);
    session.run("@props::my_scope.my_array[0] = 5");
    assert_eq!(
        Value::native(get_array_property_value()),
        int_a![5, 2, 3, 4]
    );
    session.run("@props::my_scope.my_array[3] += 1");
    assert_eq!(
        Value::native(get_array_property_value()),
        int_a![5, 2, 3, 5]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn type_ascription() {
    let mut session = TestSession::new();
    // Basic case
    assert_eq!(session.run("let x: int = 5; x"), int(5));
    assert_eq!(session.run("let x: float = 5; x"), float(5.0));
    assert_eq!(session.run("(5: int)"), int(5));
    assert_eq!(session.run("(5: float)"), float(5.0));
    // Optimisation
    let mut compile_expr = |s: &str| session.compile(s).expr.unwrap().expr;
    assert!(
        compile_expr("1").kind.as_block().unwrap()[0]
            .kind
            .is_static_apply()
    );
    assert!(
        compile_expr("(1: int)").kind.as_block().unwrap()[0]
            .kind
            .is_immediate()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn cast_as_syntax() {
    let mut session = TestSession::new();
    // Identity casts
    assert_eq!(session.run("(5: int) as int"), int(5));
    assert_eq!(session.run("(5.3: float) as float"), float(5.3));
    assert_eq!(session.run("fn f(v) { v as float } f(5.3)"), float(5.3));
    // Basic case
    assert_eq!(session.run("let x: int = 5; x as float"), float(5.0));
    assert_eq!(session.run("let x = 5.3; x as int"), int(5));
    assert_eq!(session.run("(5: int) as float"), float(5.0));
    assert_eq!(session.run("5.3 as int"), int(5));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn cast_as_precedence() {
    let mut session = TestSession::new();
    // FIXME: once bug https://github.com/enlightware/ferlium/issues/59
    // remove the int type ascription in the following tests.

    // as binds tighter than multiplication (a * b as T) = (a * (b as T))
    assert_eq!(session.run("2 * (3: int) as float"), float(6.0));
    assert_eq!(session.run("10 / (2: int) as float"), float(5.0));

    // as binds looser than unary operators (-a as T) = ((-a) as T)
    assert_eq!(session.run("-((5: int) as float)"), float(-5.0));
    assert_eq!(session.run("let x: int = -3; x as float"), float(-3.0));

    // as is left-associative (a as B as C) = ((a as B) as C)
    assert_eq!(session.run("(5: int) as float as int"), int(5));

    // as binds looser than field access and indexing
    assert_eq!(
        session.run("let a: [int] = [1, 2, 3]; a[0] as float"),
        float(1.0)
    );

    // as binds tighter than comparison
    assert_eq!(
        session.run("let x = (3: int) as float; x == 3.0"),
        bool(true)
    );
    assert_eq!(session.run("(5: int) as float < 6.0"), bool(true));

    // as binds tighter than addition
    assert_eq!(session.run("2 + (3: int) as float"), float(5.0)); // (2.0 + 3.0)
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn early_returns() {
    let mut session = TestSession::new();
    // Basic return in function
    assert_eq!(session.run("fn f() { return 42 } f()"), int(42));
    assert_eq!(session.run("fn f() { return 42; 1 } f()"), int(42));

    // Return with different types
    assert_eq!(session.run("fn f() { return true } f()"), bool(true));
    assert_eq!(
        session.run("fn f() { return (1, 2) } f()"),
        int_tuple!(1, 2)
    );
    assert_eq!(
        session.run("fn f() { return [1, 2, 3] } f()"),
        int_a![1, 2, 3]
    );

    // Return in if expression
    assert_eq!(
        session.run("fn f(x) { if x { return 1 }; 2 } f(true)"),
        int(1)
    );
    assert_eq!(
        session.run("fn f(x) { if x { return 1 }; 2 } f(false)"),
        int(2)
    );
    assert_eq!(
        session.run("fn f(x) { if x { return 1 } else { return 2 } } f(true)"),
        int(1)
    );
    assert_eq!(
        session.run("fn f(x) { if x { return 1 } else { return 2 } } f(false)"),
        int(2)
    );

    // Return in block
    assert_eq!(session.run("fn f() { { return 1 }; 2 } f()"), int(1));
    assert_eq!(session.run("fn f() { { { return 1 } }; 2 } f()"), int(1));

    // Return in loop
    assert_eq!(
        session.run("fn f() { for i in 0..10 { if i == 5 { return i } }; 99 } f()"),
        int(5)
    );
    assert_eq!(
        session.run("fn f() { for i in 0..10 { if i > 100 { return i } }; 99 } f()"),
        int(99)
    );

    // Return in match expression
    assert_eq!(
        session.run("fn f(x) { match x { true => return 1, false => 2 } } f(true)"),
        int(1)
    );
    assert_eq!(
        session.run("fn f(x) { match x { true => return 1, false => 2 } } f(false)"),
        int(2)
    );
    assert_eq!(
        session.run("fn f(x) { match x { true => 1, false => return 2 } } f(false)"),
        int(2)
    );

    // Multiple return paths
    assert_eq!(
        session.run("fn f(x) { if x < 0 { return 0 }; if x > 10 { return 10 }; x } f(-5)"),
        int(0)
    );
    assert_eq!(
        session.run("fn f(x) { if x < 0 { return 0 }; if x > 10 { return 10 }; x } f(5)"),
        int(5)
    );
    assert_eq!(
        session.run("fn f(x) { if x < 0 { return 0 }; if x > 10 { return 10 }; x } f(15)"),
        int(10)
    );

    // Return with computation
    assert_eq!(session.run("fn f(x) { return x * 2 + 1 } f(5)"), int(11));
    assert_eq!(session.run("fn f(x, y) { return x + y } f(3, 4)"), int(7));

    // Return in lambdas
    assert_eq!(session.run("let f = || { return 42 }; f()"), int(42));
    assert_eq!(
        session.run("let f = |x| { if x { return 1 }; 2 }; f(true)"),
        int(1)
    );
    assert_eq!(
        session.run("let f = |x| { if x { return 1 }; 2 }; f(false)"),
        int(2)
    );

    // Return without value (unit)
    assert_eq!(session.run("fn f() { return () } f()"), unit());
    // Note: this creates a compilation error because the compiler is not able to infer
    // that the last expression is dead.
    //assert_eq!(session.run("fn f() { return (); 1 } f()"), unit());

    // Error: return outside function
    session
        .fail_compilation("return 1")
        .expect_return_outside_function();
    session
        .fail_compilation("let x = return 1; x")
        .expect_return_outside_function();
    session
        .fail_compilation("if true { return 1 }")
        .expect_return_outside_function();
}
