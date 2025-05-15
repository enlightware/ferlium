// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;

use crate::common::variant;

use super::common::{
    bool, compile_and_get_fn_def, fail_compilation, fail_run, float, get_property_value, int, run,
    set_property_value, string, unit,
};
use ferlium::{
    error::{MutabilityMustBeWhat, RuntimeError},
    mutability::MutType,
    r#type::{tuple_type, Type},
    std::{
        array::array_type_generic,
        math::{float_type, int_type},
    },
    value::Value,
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn whitespace() {
    assert_eq!(run(""), unit());
    assert_eq!(run(" "), unit());
    assert_eq!(run("\t"), unit());
    assert_eq!(run(" \t"), unit());
    assert_eq!(run("\t "), unit());
    assert_eq!(run("\t \t  \t\t\t"), unit());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn literals() {
    assert_eq!(run("42"), int(42));
    assert_eq!(run("from_int(42)"), int(42));
    assert_eq!(run("true"), bool(true));
    assert_eq!(run("false"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn comments() {
    assert_eq!(run("42 // comment"), int(42));
    assert_eq!(run("42 //comment"), int(42));
    assert_eq!(run("42 //comment // //"), int(42));
    assert_eq!(run("42 // comment\n"), int(42));
    assert_eq!(run("42 // comment\n // comment"), int(42));
    assert_eq!(run("// comment\n42"), int(42));
    assert_eq!(run("42 /* comment */"), int(42));
    assert_eq!(run("42 /**comment**/"), int(42));
    assert_eq!(run("/* comment */ 42"), int(42));
    assert_eq!(run("/*\ncomment\n*/ 42"), int(42));
    assert_eq!(run("/*\ncomment\n*/ 42 // comment"), int(42));
    assert_eq!(
        run("/*\ncomment\n*/\n/* yeah */ 42 // comment\n/* sure */\n// ///comment"),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn blocks() {
    assert_eq!(run("{}"), unit());
    assert_eq!(run("{ 1 }"), int(1));
    assert_eq!(run("{ true; 1 }"), int(1));
    assert_eq!(run("{ 1; true }"), bool(true));
    assert_eq!(run("{ {} }"), unit());
    assert_eq!(run("{ { 1 } }"), int(1));
    assert_eq!(run("{ {}; 1 }"), int(1));
    assert_eq!(run("{ { true }; 1 }"), int(1));
    assert_eq!(run("{ { 1 }; true }"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn equalities() {
    assert_eq!(run("42 == 42"), bool(true));
    assert_eq!(run("41 == 42"), bool(false));
    assert_eq!(run("42 != 42"), bool(false));
    assert_eq!(run("41 != 42"), bool(true));
    fail_compilation("1 == true").expect_trait_impl_not_found("Num", &["bool"]);
    assert_eq!(run("true == true"), bool(true));
    assert_eq!(run("true == false"), bool(false));
    assert_eq!(run("true != true"), bool(false));
    assert_eq!(run("true != false"), bool(true));
    assert_eq!(run("() == ()"), bool(true));
    assert_eq!(run("() != ()"), bool(false));
    fail_compilation("() == (1,)").expect_type_mismatch("(int,)", "()");
    assert_eq!(run("(1,) == (1,)"), bool(true));
    assert_eq!(run("(1,) != (1,)"), bool(false));
    assert_eq!(run("(1,) == (2,)"), bool(false));
    assert_eq!(run("(1,) != (2,)"), bool(true));
    assert_eq!(run("(1,true) == (1,true)"), bool(true));
    assert_eq!(run("(1,true) != (1,true)"), bool(false));
    assert_eq!(run("(1,true) == (2,true)"), bool(false));
    assert_eq!(run("(1,true) != (2,true)"), bool(true));
    assert_eq!(run("(1,true) == (1,false)"), bool(false));
    assert_eq!(run("(1,true) != (1,false)"), bool(true));
    fail_compilation("[] == []").expect_unbound_ty_var();
    fail_compilation("[] != []").expect_unbound_ty_var();
    assert_eq!(run("[] == [1]"), bool(false));
    assert_eq!(run("[] != [1]"), bool(true));
    assert_eq!(run("[1] == [1]"), bool(true));
    assert_eq!(run("[1] != [1]"), bool(false));
    assert_eq!(run("[1] == [2]"), bool(false));
    assert_eq!(run("[1] != [2]"), bool(true));
    assert_eq!(run("let a = [1, 1]; a[0] == a[1]"), bool(true));
    assert_eq!(run("let a = [1, 1]; a[0] != a[1]"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn local_variables() {
    assert_eq!(run("let a = 1 ; a"), int(1));
    assert_eq!(run("let mut a = 1 ; a"), int(1));
    assert_eq!(run("let mut a = 1 ; a = 2; a"), int(2));
    assert_eq!(run("let a = true ; a"), bool(true));
    assert_eq!(run("let mut a = true ; a"), bool(true));
    assert_eq!(run("let mut a = true ; a = false; a"), bool(false));
    assert_eq!(run("let mut a = [1, 2]; a = [3, 4, 5]; a"), int_a![3, 4, 5]);
    assert_eq!(run("let mut a = [1, 2]; a = [3]; a == [3]"), bool(true));
    assert_eq!(
        run("let mut a = (1, true); a = (2, false); a == (2, false)"),
        bool(true)
    );
    assert_eq!(run("let f = || 1; let a = f(); a"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn type_annotation_in_let() {
    assert_eq!(run("let a: int = 1 ; a"), int(1));
    assert_eq!(run("let a: float = 1 ; a"), float(1.0));
    assert_eq!(run("let a: [int] = [] ; a"), int_a![]);
    let fn_def = compile_and_get_fn_def("fn id(x) { let a: [_] = x; a }", "id");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args.len(), 1);
    let gen_array_type = array_type_generic();
    assert_eq!(fn_ty.args[0].ty, gen_array_type);
    assert_eq!(fn_ty.ret, gen_array_type);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn type_annotation_in_fn() {
    assert_eq!(run("fn id(x: int) { x } id(0)"), int(0));
    assert_eq!(run("fn id(x: float) { x } id(0)"), float(0.0));
    assert_eq!(run("fn id(x: [int]) { x } id([])"), int_a![]);
    assert_eq!(run("fn id(x) -> int { x } id(0)"), int(0));
    assert_eq!(run("fn id(x) -> float { x } id(0)"), float(0.0));
    assert_eq!(run("fn id(x) -> [int] { x } id([])"), int_a![]);
    let gen_array_type = array_type_generic();
    let fn_def = compile_and_get_fn_def("fn id(x: [_]) { x }", "id");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args[0].mut_ty, MutType::constant());
    assert_eq!(fn_ty.args[0].ty, gen_array_type);
    assert_eq!(fn_ty.ret, gen_array_type);
    let fn_def = compile_and_get_fn_def("fn id(x: &mut [_]) { x }", "id");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args[0].mut_ty, MutType::mutable());
    assert_eq!(fn_ty.args[0].ty, gen_array_type);
    assert_eq!(fn_ty.ret, gen_array_type);
    let fn_def = compile_and_get_fn_def("fn id(x) -> [_] { x }", "id");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args[0].ty, gen_array_type);
    assert_eq!(fn_ty.ret, gen_array_type);
    let fn_def = compile_and_get_fn_def("fn mkt(a: int, b: float) { (a, b) }", "mkt");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args[0].ty, int_type());
    assert_eq!(fn_ty.args[1].ty, float_type());
    assert_eq!(fn_ty.ret, tuple_type([int_type(), float_type()]));
    let fn_def = compile_and_get_fn_def("fn mkt(a, b) -> (int, float) { (a, b) }", "mkt");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args[0].ty, int_type());
    assert_eq!(fn_ty.args[1].ty, float_type());
    assert_eq!(fn_ty.ret, tuple_type([int_type(), float_type()]));
    let fn_def = compile_and_get_fn_def("fn ist2(v) -> (_, _) { v }", "ist2");
    let fn_ty = fn_def.ty_scheme.ty();
    let gen0 = Type::variable_id(0);
    let gen1 = Type::variable_id(1);
    let gen_tuple2 = tuple_type([gen0, gen1]);
    assert_eq!(fn_ty.args[0].ty, gen_tuple2);
    assert_eq!(fn_ty.ret, gen_tuple2);
    let fn_def = compile_and_get_fn_def("fn f(v: &? int) { v = 1 }", "f");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args[0].mut_ty, MutType::mutable());
    assert_eq!(fn_ty.args[0].ty, int_type());
    assert_eq!(fn_ty.ret, Type::unit());
    let fn_def = compile_and_get_fn_def("fn f(v: &? int) { v }", "f");
    let fn_ty = fn_def.ty_scheme.ty();
    assert_eq!(fn_ty.args[0].mut_ty, MutType::constant());
    assert_eq!(fn_ty.args[0].ty, int_type());
    assert_eq!(fn_ty.ret, int_type());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mutability() {
    assert_eq!(run("let mut a = 1 ; a = 2; a"), int(2));
    fail_compilation("let a = 1 ; a = 2; a")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
    assert_eq!(run("let mut a = (1,) ; a.0 = 2; a.0"), int(2));
    fail_compilation("let a = (1,) ; a.0 = 2; a.0")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
    assert_eq!(run("let mut a = [1] ; a[0] = 2; a[0]"), int(2));
    fail_compilation("let a = [1] ; a[0] = 2; a[0]")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
    assert_eq!(run("let mut a = ([1], 1) ; a.0[0] = 2; a.0[0]"), int(2));
    fail_compilation("let a = ([1], 1) ; a.0[0] = 2; a.0[0]")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn logic_operators() {
    assert_eq!(run("not true"), bool(false));
    assert_eq!(run("not false"), bool(true));
    assert_eq!(run("not not true"), bool(true));
    assert_eq!(run("not not false"), bool(false));
    assert_eq!(run("not not not true"), bool(false));
    assert_eq!(run("not not not false"), bool(true));
    assert_eq!(run("true or false"), bool(true));
    assert_eq!(run("true and false"), bool(false));
    assert_eq!(run("true or true and false"), bool(true));
    assert_eq!(run("(true or true) and false"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn arithmetic_operators() {
    assert_eq!(run("1+2"), int(3));
    assert_eq!(run("  1  + 2 "), int(3));
    assert_eq!(run("3*2"), int(6));
    assert_eq!(run("1-4"), int(-3));
    assert_eq!(run("-1"), int(-1));
    assert_eq!(run("--1"), int(1));
    assert_eq!(run("---1"), int(-1));
    assert_eq!(run("1---5"), int(-4));
    assert_eq!(run("1+--5"), int(6));
    assert_eq!(run("0-2-2"), int(-4));
    assert_eq!(run("0-(2-2)"), int(0));
    assert_eq!(run("1+2*3"), int(7));
    assert_eq!(run("1.0+2.0"), float(3.0));
    assert_eq!(run("  1.0  + 2.0 "), float(3.0));
    assert_eq!(run("3.0*2.0"), float(6.0));
    assert_eq!(run("1.0-4.0"), float(-3.0));
    assert_eq!(run("-1.0"), float(-1.0));
    assert_eq!(run("--1.0"), float(1.0));
    assert_eq!(run("---1.0"), float(-1.0));
    assert_eq!(run("1.0---5.0"), float(-4.0));
    assert_eq!(run("1.0+--5.0"), float(6.0));
    assert_eq!(run("0.0-2.0-2.0"), float(-4.0));
    assert_eq!(run("0.0-(2.0-2.0)"), float(0.0));
    assert_eq!(run("1.0+2.0*3.0"), float(7.0));
    assert_eq!(run("7 / 2"), float(3.5));
    assert_eq!(run("12 / 3 / 2"), float(2.0));
    assert_eq!(run("12 / (3 / 2)"), float(8.0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn comparison_operators() {
    assert_eq!(run("1 < 2"), bool(true));
    assert_eq!(run("1 <= 2"), bool(true));
    assert_eq!(run("1 > 2"), bool(false));
    assert_eq!(run("1 >= 2"), bool(false));
    assert_eq!(run("1 != 2"), bool(true));
    assert_eq!(run("1 == 2"), bool(false));
    assert_eq!(run("2 < 2"), bool(false));
    assert_eq!(run("2 <= 2"), bool(true));
    assert_eq!(run("2 > 2"), bool(false));
    assert_eq!(run("2 >= 2"), bool(true));
    assert_eq!(run("2 != 2"), bool(false));
    assert_eq!(run("2 == 2"), bool(true));
    assert_eq!(run("1.5 < 2.5"), bool(true));
    assert_eq!(run("1.5 <= 2.5"), bool(true));
    assert_eq!(run("1.5 > 2.5"), bool(false));
    assert_eq!(run("1.5 >= 2.5"), bool(false));
    assert_eq!(run("1.5 != 2.5"), bool(true));
    assert_eq!(run("1.5 == 2.5"), bool(false));
    assert_eq!(run("2.5 < 2.5"), bool(false));
    assert_eq!(run("2.5 <= 2.5"), bool(true));
    assert_eq!(run("2.5 > 2.5"), bool(false));
    assert_eq!(run("2.5 >= 2.5"), bool(true));
    assert_eq!(run("2.5 != 2.5"), bool(false));
    assert_eq!(run("2.5 == 2.5"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn expression_grouping() {
    assert_eq!(run("(1)"), int(1));
    assert_eq!(run("((1))"), int(1));
    assert_eq!(run("(((1)))"), int(1));
    assert_eq!(run("(((1)))+((2))"), int(3));
    assert_eq!(run("1 + (2 * 3)"), int(7));
    assert_eq!(run("(1 + 2) * 3"), int(9));
    assert_eq!(run("1 + 2 * 3"), int(7));
    assert_eq!(run("1 * 2 + 3"), int(5));
    assert_eq!(run("1 * (2 + 3)"), int(5));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn if_expr() {
    assert_eq!(run("if 1 < 2 { () }"), unit());
    assert_eq!(run("if 1 < 2 { 1 } else { 2 }"), int(1));
    assert_eq!(run("if 1 <= 2 { 1 } else { 2 }"), int(1));
    assert_eq!(run("if 1 > 2 { 1 } else { 2 }"), int(2));
    assert_eq!(run("if 1 >= 2 { 1 } else { 2 }"), int(2));
    assert_eq!(run("if 1 != 2 { 1 } else { 2 }"), int(1));
    assert_eq!(run("if 1 == 2 { 1 } else { 2 }"), int(2));
    assert_eq!(run("if 2 < 2 { 1 } else { 2 }"), int(2));
    assert_eq!(run("if 2 <= 2 { 1 } else { 2 }"), int(1));
    assert_eq!(run("if 2 > 2 { 1 } else { 2 }"), int(2));
    assert_eq!(run("if 2 >= 2 { 1 } else { 2 }"), int(1));
    assert_eq!(run("if 2 != 2 { 1 } else { 2 }"), int(2));
    assert_eq!(run("if 2 == 2 { 1 } else { 2 }"), int(1));
    assert_eq!(run("if true { 1 } else if false { 2 } else { 3 }"), int(1));
    assert_eq!(run("if false { 1 } else if true { 2 } else { 3 }"), int(2));
    assert_eq!(run("if false { 1 } else if false { 2 } else { 3 }"), int(3));
    assert_eq!(
        run("if false { 1 } else if false { 2 } else if false { 3 } else { 4 }"),
        int(4)
    );
    assert_eq!(
        run("let mut a = 0; if false { a = 1 } else if false { a = 2 }; a"),
        int(0)
    );
    assert_eq!(
        run("let mut a = 0; if true { a = 1 } else if true { a = 2 }; a"),
        int(1)
    );
    assert_eq!(
        run("let mut a = 0; if false { a = 1 } else if true { a = 2 }; a"),
        int(2)
    );
    fail_compilation("fn a() { if true { 1 } }").expect_trait_impl_not_found("Num", &["()"]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn match_expr() {
    fail_compilation("match true {}")
        .into_inner()
        .into_empty_match_body()
        .unwrap();
    assert_eq!(run("match true { _ => 0 }"), int(0));
    assert_eq!(run("match true { true => 0, _ => 1 }"), int(0));
    assert_eq!(run("match false { true => 0, _ => 1 }"), int(1));
    assert_eq!(run("match true { true => 0, _ => 1, }"), int(0));
    assert_eq!(run("match true { false => 1, true => 0 }"), int(0));
    assert_eq!(run("match false { false => 1, true => 0, }"), int(1));
    fail_compilation("match false { false => 1, true => 0, false => 2 }")
        .into_inner()
        .into_duplicated_literal_pattern()
        .unwrap();
    assert_eq!(run("let a = 0; match a { 0 => 1, _ => 3 }"), int(1));
    assert_eq!(
        run("let a = -1; match a { -1 => true, 0 => false, -3 => false, 7 => false, _ => false }"),
        bool(true)
    );
    fail_compilation("let a = 0; match a { 0 => 1 }")
        .into_inner()
        .into_type_values_cannot_be_enumerated()
        .unwrap();
    assert_eq!(run("let a = 1; match a { 0 => 1, _ => 3 }"), int(3));
    assert_eq!(run("let a = 0; match a { 0 => 1, 1 => 2, _ => 3 }"), int(1));
    assert_eq!(run("let a = 1; match a { 0 => 1, 1 => 2, _ => 3 }"), int(2));
    assert_eq!(run("let a = 5; match a { 0 => 1, 1 => 2, _ => 3 }"), int(3));
    assert_eq!(run("match testing::some_int(0) { _ => 0 }"), int(0));
    assert_eq!(
        run("match testing::some_int(0) { Some(x) => 1, None => 0 }"),
        int(1)
    );
    fail_compilation("match testing::some_int(0) { None => 0 }")
        .expect_type_mismatch("None | Some (int)", "None");
    fail_compilation("match testing::some_int(0) { Some(x) => 0 }")
        .expect_type_mismatch("None | Some (int)", "Some (B)");
    // TODO: add more complex literals (tuples, array) once optimisation is in place
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn match_tuples() {
    assert_eq!(
        run(r#"
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
        "#),
        int_a![4, 3, 2, 1]
    );
    assert_eq!(
        run(r#"
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
        "#),
        int_a![8, 7, 6, 5, 4, 3, 2, 1]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn tuple_creation() {
    assert_eq!(run("()"), unit());
    assert_eq!(run("(1,)"), int_tuple!(1));
    assert_eq!(run("(1, 2)"), int_tuple!(1, 2));
    assert_eq!(run("(1, 2, )"), int_tuple!(1, 2));
    assert_eq!(run("(1, 1)"), int_tuple!(1, 1));
    assert_eq!(run("(3, 1, 7)"), int_tuple!(3, 1, 7));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn tuple_projection() {
    assert_eq!(run("(1,).0"), int(1));
    assert_eq!(run("(1,2).1"), int(2));
    assert_eq!(run("(1,(3, (2, 4, 5))).1.1.2"), int(5));
    assert_eq!(run("let a = (1,2); a.0"), int(1));
    assert_eq!(run("let a = (1,2); a.1"), int(2));
    assert_eq!(run("let f = || (1,2); f().1"), int(2));
    assert_eq!(
        run("let f = |x, y| (y == x.1.0); f((1,(2,1)), 2)"),
        bool(true)
    );
    assert_eq!(
        run("let f = |x, y| (x.1, x.1.0, y == x.1); f((1,(2,1)), (2,1)); ()"),
        unit()
    );
    assert_eq!(run("fn f(v) { v.1.2.3 } ()"), unit());
    assert_eq!(
        run("fn a(x) { x.0 } fn b(x) { x.1 } fn c(x) { (a(x), b(x)) } c((1,2))"),
        int_tuple!(1, 2)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn static_function_arity() {
    let text = "fn a() { 0 } fn b(x) { x + 1 } fn c(x, y) { x + y }";
    assert_eq!(run(&format!("{text} a()")), int(0));
    fail_compilation(&format!("{text} b()")).expect_wrong_number_of_arguments(1, 0);
    fail_compilation(&format!("{text} c()")).expect_wrong_number_of_arguments(2, 0);
    fail_compilation(&format!("{text} a(1)")).expect_wrong_number_of_arguments(0, 1);
    assert_eq!(run(&format!("{text} b(1)")), int(2));
    fail_compilation(&format!("{text} c(1)")).expect_wrong_number_of_arguments(2, 1);
    fail_compilation(&format!("{text} a(1, 2)")).expect_wrong_number_of_arguments(0, 2);
    fail_compilation(&format!("{text} b(1, 2)")).expect_wrong_number_of_arguments(1, 2);
    assert_eq!(run(&format!("{text} c(1, 2)")), int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn value_function_arity() {
    let text = "fn a() { 0 } fn b(x) { x + 1 } fn c(x, y) { x + y + 0 }";
    assert_eq!(run(&format!("{text} (a,).0()")), int(0));
    fail_compilation(&format!("{text} (b,).0()")).expect_type_mismatch("(B) -> B", "() -> A ! e₀");
    fail_compilation(&format!("{text} (c,).0()"))
        .expect_type_mismatch("(B, B) -> B", "() -> A ! e₀");
    fail_compilation(&format!("{text} (a,).0(1)")).expect_type_mismatch("() -> C", "(A) -> B ! e₀");
    assert_eq!(run(&format!("{text} (b,).0(1)")), int(2));
    fail_compilation(&format!("{text} (c,).0(1)"))
        .expect_type_mismatch("(C, C) -> C", "(A) -> B ! e₀");
    fail_compilation(&format!("{text} (a,).0(1, 2)"))
        .expect_type_mismatch("() -> D", "(A, B) -> C ! e₀");
    fail_compilation(&format!("{text} (b,).0(1, 2)"))
        .expect_type_mismatch("(D) -> D", "(A, B) -> C ! e₀");
    assert_eq!(run(&format!("{text} (c,).0(1, 2)")), int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn lambda() {
    assert_eq!(run("let f = || 1; f()"), int(1));
    assert_eq!(run("let f = | | 1; f()"), int(1));
    assert_eq!(run("let f = |x| x; f(1)"), int(1));
    assert_eq!(run("let f = |x,| x; f(1)"), int(1));
    assert_eq!(run("let f = |x, y| x + y; f(1, 2)"), int(3));
    assert_eq!(run("let f = |x, y,| x + y; f(1, 2)"), int(3));
    assert_eq!(run("let f = |x, y| x + y; f(1, f(2, 3))"), int(6));
    assert_eq!(run("let f = |x, y| x + y; f(f(1, 2), 3)"), int(6));
    assert_eq!(run("let f = |x, y| x + y; f(f(1, 2), f(3, 4))"), int(10));
    assert_eq!(
        run("let sq = |x| x * x; let inc = |x| x + 1; sq(inc(inc(2)))"),
        int(16)
    );
    fail_compilation("let id = |x| x; id(1); id(true)")
        .expect_trait_impl_not_found("Num", &["bool"]);
    fail_compilation("let d = |x, y| (x, y + 1); d(true, 1); d(1, 2)")
        .expect_trait_impl_not_found("Num", &["bool"]);
    assert_eq!(run("(||1)()"), int(1));
    assert_eq!(run("(|x| x.1)((1,2))"), int(2));
    assert_eq!(
        run("let f = |x| x[0] = 1; let mut a = [0]; f(a); a"),
        int_a!(1)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment() {
    assert_eq!(run("let a = 1; a"), int(1));
    assert_eq!(run("let mut a = 1; a = 2"), unit());
    assert_eq!(run("let mut a = 1; a = 2; a"), int(2));
    assert_eq!(run("let mut a = 1; let b = 2; a = b; a"), int(2));
    assert_eq!(run("let mut a = 1; let b = 2; a = b; b"), int(2));
    assert_eq!(run("let mut a = 1; let mut b = 2; a = b; b = a; b"), int(2));
    assert_eq!(run("let mut a = (1, 2); a.0 = 3; a"), int_tuple!(3, 2));
    assert_eq!(
        run("let mut a = ((1, 2), 3); a.0.1 = 5; a.0"),
        int_tuple!(1, 5)
    );
    assert_eq!(run("let mut a = [1, 2]; a[0] = 3; a"), int_a![3, 2]);
    assert_eq!(
        run("let mut a = [[1, 2], [3, 4]]; a[0][1] = 5; a[0]"),
        int_a![1, 5]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn op_assignment() {
    assert_eq!(run("let mut a = 4; a += 1; a"), int(5));
    assert_eq!(run("let mut a = 4; a -= 1; a"), int(3));
    assert_eq!(run("let mut a = 4; a *= 2; a"), int(8));
    assert_eq!(run("let mut a = 4; a /= 2; a"), float(2.0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn for_loops_with_range() {
    assert_eq!(run("for i in 0..3 { () }"), unit());
    assert_eq!(run("let mut s = 0; for i in 1..4 { s = s + i }; s"), int(6));
    assert_eq!(
        run("let mut s = 0; for i in -1..-4 { s = s + i }; s"),
        int(-6)
    );
    assert_eq!(
        run("let mut a = []; for i in 2..5 { array_append(a, i) }; a"),
        int_a![2, 3, 4]
    );
    assert_eq!(
        run(
            "fn s() { 2 } fn e() { 5 } let mut a = []; for i in s()..e() { array_append(a, i) }; a"
        ),
        int_a![2, 3, 4]
    );
    assert_eq!(
        run("let mut a = []; for i in 5..2 { array_append(a, i) }; a"),
        int_a![5, 4, 3]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn for_loops_with_arrays() {
    assert_eq!(run("for i in [0, 1, 2] { () }"), unit());
    assert_eq!(
        run("let mut s = 0; for i in [1, 2, 3] { s = s + i }; s"),
        int(6)
    );
    assert_eq!(
        run("let mut s = 0.5; for i in [1.5, 2.5, 3.5] { s = s + i }; s"),
        float(8.0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_functions() {
    assert_eq!(
        run(r#"fn my_add(x, y) {
            x + y
        }
        let x = my_add;
        x(1, 2)"#),
        int(3)
    );
    assert_eq!(
        run(r#"fn my_add(x, y) {
            x + y
        }
        fn my_sub(x, y) {
            x - y
        }
        let mut x = my_add;
        x = my_sub;
        x(1, 2)"#),
        int(-1)
    );
    assert_eq!(
        run("fn fact(i) { if i > 1 { i * ((fact,).0)(i - 1) } else { 1 } } fact(3)"),
        int(6)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn records() {
    assert_eq!(run("{a:1}.a"), int(1));
    assert_eq!(run("{a:1, b:2}.a"), int(1));
    assert_eq!(run("{a:1, b:2}.b"), int(2));
    let s = "{a:1, a:2}";
    fail_compilation(s).expect_duplicate_record_field(s, "a");
    let s = "{a:1, a:true, b:2}";
    fail_compilation(s).expect_duplicate_record_field(s, "a");
    assert_eq!(run("(|| {a:1, b:2})().a"), int(1));
    assert_eq!(run("(|| {a:1, b:2})().b"), int(2));
    assert_eq!(run("let r = || {a:1, b:2}; r().a + r().b"), int(3));
    assert_eq!(
        run("let r = || {a:1, a_o: true, b:2}; r().a + r().b"),
        int(3)
    );
    assert_eq!(run("fn s(v) { v.x + v.y } s({x:1, y:2})"), int(3));
    assert_eq!(
        run("fn s(v) { v.x + v.y } s({name: \"toto\", x:1, y:2})"),
        int(3)
    );
    assert_eq!(
        run("fn s(v) { v.x + v.y } s({name: \"toto\", x:1, z: true, y:2, noise: (1,2)})"),
        int(3)
    );
    assert_eq!(
        run("fn sq(x) { x * x } fn l2(v) { sq(v.x) + sq(v.y) } l2({x:1, y:2})"),
        int(5)
    );
    assert_eq!(run("let f = |x| x.a; f({a:1})"), int(1));
    assert_eq!(run("fn e(v) { v.toto } (e,).0({toto: 3})"), int(3));
    assert_eq!(run("fn e(v) { v.toto } let a = e; a({toto: 3})"), int(3));
    assert_eq!(
        run("let l2 = |v| { let sq = |x| x * x; sq(v.x) + sq(v.y) }; l2({x:1, y:2})"),
        int(5)
    );
    assert_eq!(
        run("let l = |v| { let ex = |v| v.x; let ey = |v| v.y; ex(v) + ey(v) }; l({a: true, x:1, x_n: \"hi\", y:2, y_n: false})"),
        int(3)
    );
    assert_eq!(run("(|v| v.x + v.y)({x:1, y:2})"), int(3));
    assert_eq!(
        run("fn s(v) { v.x + v.y } ((s,).0)({x:1, bla: true, y:2})"),
        int(3)
    );
    assert_eq!(run("fn a(x) { x.a } fn b(x) { a(x) } b({a:3})"), int(3));
    assert_eq!(
        run("fn a(x) { x.a } fn b(x) { x.b } fn c(x, y) { (a(x), b(y)) } c({a:1},{b:2})"),
        int_tuple!(1, 2)
    );
    assert_eq!(
        run("fn sum(i, l) { if i < l.count { sum(i + 1, l) + 1 } else { 0 } } sum(0, {count: 4})"),
        int(4)
    );
    assert_eq!(
        run("fn a(x) { x.a } fn b(x) { ((a,).0)(x) } b({a: 3})"),
        int(3)
    );
    assert_eq!(
        run("let f = |x, y| (x.a, x.a.b, y == x.a); f({a: {a: 3, b: 1}}, {a: 4, b: 1})"),
        Value::tuple(vec![int_tuple!(3, 1), int(1), bool(false)])
    );
    assert_eq!(
        run("fn l(v) { ((|v| v.x)(v), (|v| v.y)(v)) } l({x:1, y:2})"),
        int_tuple!(1, 2)
    );
    assert_eq!(
        run("fn l(v) { let x = |v| v.x; let y = |v| v.y; (x(v), y(v)) } l({x:1, y:2})"),
        int_tuple!(1, 2)
    );
    assert_eq!(
        run("fn l(v) { (((|v| v.x),).0(v), ((|v| v.y),).0(v)) } l({x:1, y:2})"),
        int_tuple!(1, 2)
    );
    assert_eq!(
        run("fn x() { |v| v.x } fn y() { |v| v.y } fn e(v) { (x()(v), y()(v)) } e({x:1, y:2})"),
        int_tuple!(1, 2)
    );
    fail_compilation(
        "fn swap(a,b) { let mut temp = a; a = b; b = temp } let mut v = { x:1, y:2 }; swap(v.x, v.x)",
    )
    .expect_mutable_paths_overlap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn variants() {
    // simple example
    assert_eq!(run("MyVariant"), variant("MyVariant", Value::unit()));
    assert_eq!(run("MyVariant2(1.1)"), variant("MyVariant2", float(1.1)));
    // TODO: add more variant constructor tests
    // option example
    let match_exhaustive = r#"fn s(x) { match x { None => "no", Some(x) => f"hi {x}" } }"#;
    assert_eq!(
        run(&format!("{match_exhaustive} s(Some(1))")),
        string("hi 1")
    );
    assert_eq!(run(&format!("{match_exhaustive} s(None)")), string("no"));
    assert_eq!(
        run(&format!("{match_exhaustive} fn f() {{ s(Some(1)) }} f()")),
        string("hi 1")
    );
    assert_eq!(
        run(&format!(
            "{match_exhaustive} fn f() {{ let a = 1; s(Some(a)) }} f()"
        )),
        string("hi 1")
    );
    assert_eq!(
        run(&format!("{match_exhaustive} fn f() {{ s(None) }} f()")),
        string("no")
    );
    let match_open = r#"fn s(x) { match x { None => "no", Some(x) => f"hi {x}", _ => "?" } }"#;
    assert_eq!(run(&format!("{match_open} s(Some(1))")), string("hi 1"));
    assert_eq!(run(&format!("{match_open} s(None)")), string("no"));
    assert_eq!(
        run(&format!("{match_open} fn f() {{ s(Some(1)) }} f()")),
        string("hi 1")
    );
    assert_eq!(
        run(&format!(
            "{match_open} fn f() {{ let a = 1; s(Some(a)) }} f()"
        )),
        string("hi 1")
    );
    assert_eq!(
        run(&format!("{match_open} fn f() {{ s(None) }} f()")),
        string("no")
    );
    // area example
    let match_exhaustive = r#"fn a(x) { match x { Square(r) => r * r, Rect(w, h) => w * h } }"#;
    assert_eq!(run(&format!("{match_exhaustive} a(Square(3))")), int(9));
    assert_eq!(run(&format!("{match_exhaustive} a(Rect(3, 2))")), int(6));
    assert_eq!(
        run(&format!("{match_exhaustive} let y = 2; a(Rect(3, y))")),
        int(6)
    );
    assert_eq!(
        run(&format!(
            "{match_exhaustive} let x = 3; let y = 2; a(Rect(x, y))"
        )),
        int(6)
    );
    let match_open = r#"fn a(x) { match x { Square(r) => r * r, Rect(w, h) => w * h, _ => 0 } }"#;
    assert_eq!(run(&format!("{match_open} a(Square(3))")), int(9));
    assert_eq!(run(&format!("{match_open} a(Rect(3, 2))")), int(6));
    assert_eq!(
        run(&format!("{match_open} let y = 2; a(Rect(3, y))")),
        int(6)
    );
    assert_eq!(
        run(&format!("{match_open} let x = 3; let y = 2; a(Rect(x, y))")),
        int(6)
    );
    assert_eq!(run(&format!("{match_open} a(Triangle(3, 3, 5))")), int(0));
    assert_eq!(
        run(&format!(
            "{match_open} let x = 3; let y = 3; let z = 5; a(Triangle(x, y, z))"
        )),
        int(0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn adt() {
    fail_compilation("fn f(x) { (x.0, x.a) }").expect_inconsistent_adt();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mutability_soundness() {
    fail_compilation("let f = |x| (x[0] = 1); let a = [1]; f(a)")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn borrow_checker() {
    let swap_fn = "fn swap(a, b) { let temp = b; b = a; a = temp }";
    assert_eq!(
        run(&format!(
            "{swap_fn} let mut a = [0, 1]; swap(a[0], a[1]); a"
        )),
        int_a![1, 0]
    );
    fail_compilation(&format!(
        "{swap_fn} let mut a = [0, 1]; swap(a[0], a[0]); a"
    ))
    .expect_mutable_paths_overlap();
    fail_compilation(&format!(
        "{swap_fn} let mut a = [0, 1]; let i = 0; swap(a[0], a[i]); a"
    ))
    .expect_mutable_paths_overlap();
    assert_eq!(
        run(&format!(
            "{swap_fn} let mut a = [0]; let mut b = [1]; swap(a[0], b[0]); a"
        )),
        int_a![1]
    );
    assert_eq!(
        run(&format!(
            "{swap_fn} let mut a = [0]; let mut b = [1]; swap(a[a[0]], b[0]); a"
        )),
        int_a![1]
    );
    assert_eq!(
        run(&format!(
            "{swap_fn} let mut a = [0]; let mut b = [1]; swap(a[a[0]], b[a[0]]); a"
        )),
        int_a![1]
    );
    assert_eq!(
        run(&format!(
            "{swap_fn} let mut a = ((0,1),2); swap(a.0.1, a.1); a.0"
        )),
        int_tuple!(0, 2)
    );
    assert_eq!(
        run(&format!(
            "{swap_fn} let mut a = ((0,1),2); swap(a.0.1, a.0.0); a.0"
        )),
        int_tuple!(1, 0)
    );
    fail_compilation(&format!(
        "{swap_fn} let mut a = ((0,1),2); swap(a.0, a.0); a.0"
    ))
    .expect_mutable_paths_overlap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn execution_errors() {
    use RuntimeError::*;
    assert_eq!(fail_run("abort()"), Aborted(None));
    assert_eq!(fail_run("panic(\"oh no\")"), Aborted(Some("oh no".into())));
    assert_eq!(fail_run("1.0 / 0.0"), DivisionByZero);
    assert_eq!(fail_run("let v = || 0.0; 1.0 / v()"), DivisionByZero);
    assert_eq!(fail_run("idiv(1, 0)"), DivisionByZero);
    assert_eq!(fail_run("let v = || 0; idiv(1, v())"), DivisionByZero);
    assert_eq!(fail_run("rem(1, 0)"), RemainderByZero);
    assert_eq!(fail_run("mod(1, 0)"), RemainderByZero);
    assert_eq!(fail_run("let v = || 0; rem(1, v())"), RemainderByZero);
    assert_eq!(fail_run("let v = || 0; mod(1, v())"), RemainderByZero);
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
        fail_run("let mut a = [1, 2]; a[3] = 0"),
        ArrayAccessOutOfBounds { index: 3, len: 2 }
    );
    assert_eq!(
        fail_run("let mut a = [1, 2]; a[-3] = 0"),
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
        fail_run("let i = || 3; let mut a = [1, 2]; a[i()] = 0"),
        ArrayAccessOutOfBounds { index: 3, len: 2 }
    );
    assert_eq!(
        fail_run("let i = || -3; let mut a = [1, 2]; a[i()] = 0"),
        ArrayAccessOutOfBounds { index: -3, len: 2 }
    );
    assert_eq!(
        fail_run("fn rf() { rf() } rf() + 0"),
        RecursionLimitExceeded { limit: 100 }
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn never_type() {
    use RuntimeError::*;
    assert_eq!(run("if true { 2 } else { abort() }"), int(2));
    assert_eq!(fail_run("if false { 2 } else { abort() }"), Aborted(None));
    assert_eq!(fail_run("if true { abort() } else { 2 }"), Aborted(None));
    assert_eq!(run("if false { abort() } else { 2 }"), int(2));
    assert_eq!(run("log(if true { 2 } else { abort() })"), Value::unit());
    assert_eq!(
        fail_run("log(if false { 2 } else { abort() })"),
        Aborted(None)
    );
    assert_eq!(
        fail_run("log(if true { abort() } else { 2 })"),
        Aborted(None)
    );
    assert_eq!(run("log(if false { abort() } else { 2 })"), Value::unit());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_creation() {
    fail_compilation("[]").expect_unbound_ty_var();
    assert_eq!(run("[1]"), int_a![1]);
    assert_eq!(run("[1,]"), int_a![1]);
    assert_eq!(run("[1, 2]"), int_a![1, 2]);
    assert_eq!(run("[1, 2,]"), int_a![1, 2]);
    assert_eq!(run("[1, 1]"), int_a![1, 1]);
    assert_eq!(run("[3, 1, 7]"), int_a![3, 1, 7]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_index() {
    assert_eq!(run("[1][0]"), int(1));
    assert_eq!(run("[1][-1]"), int(1));
    assert_eq!(run("[1, 3][0]"), int(1));
    assert_eq!(run("[1, 3][1]"), int(3));
    assert_eq!(run("[1, 3][-1]"), int(3));
    assert_eq!(run("[1, 3][-2]"), int(1));
    assert_eq!(run("[[1, 2], [3, 4]][1][0]"), int(3));
    assert_eq!(run("let a = [1, 3]; a[0]"), int(1));
    assert_eq!(run("let a = [1, 3]; a[1]"), int(3));
    assert_eq!(run("let i = 0; [1, 3][i]"), int(1));
    assert_eq!(run("let i = 1; [1, 3][i]"), int(3));
    assert_eq!(run("let i = -1; [1, 3][i]"), int(3));
    assert_eq!(run("let i = -2; [1, 3][i]"), int(1));
    assert_eq!(run("let i = 0; let j = 1; [[1, 2], [3, 4]][i][j]"), int(2));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_literals() {
    assert_eq!(run(r#""""#), string(""));
    assert_eq!(run(r#""hello world""#), string("hello world"));
    assert_eq!(run(r#""hello \"world\"""#), string(r#"hello "world""#));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn string_formatting() {
    assert_eq!(run(r#"f"hello world""#), string("hello world"));
    assert_eq!(
        run(r#"let a = 1; let b = true; f"hello {a} world {b}""#),
        string("hello 1 world true")
    );
    assert_eq!(
        run(r#"let a = [1, 2]; let b = (0, true, "hi"); f"hello {a} world {b}""#),
        string("hello [1, 2] world (0, true, hi)")
    );
    assert_eq!(run(r#"fn nbr(x) { f" #{x}" } nbr(3)"#), string(" #3"));
    let s = r#"f"hello {a} world""#;
    fail_compilation(s).expect_undefined_var_in_string_formatting(s, "a");
    let s = r#"let a = 1; f"{a} is {b}""#;
    fail_compilation(s).expect_undefined_var_in_string_formatting(s, "b");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn to_string() {
    assert_eq!(run("to_string(true)"), string("true"));
    assert_eq!(run("to_string(false)"), string("false"));
    assert_eq!(run("to_string(1)"), string("1"));
    assert_eq!(run("to_string(-17)"), string("-17"));
    assert_eq!(run("to_string(0.0)"), string("0"));
    assert_eq!(run("to_string(0.1)"), string("0.1"));
    assert_eq!(run("to_string(\"hello world\")"), string("hello world"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn modules() {
    assert_eq!(run("fn a(x) { x }"), unit());
    assert_eq!(run("fn a(x) { x } a(1)"), int(1));
    assert_eq!(run("fn a(x) { x + 1 } a(1)"), int(2));
    assert_eq!(
        run("fn d(x) { 2 * x } fn s(x) { x + 1 } d(s(s(1)))"),
        int(6)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_functions() {
    assert_eq!(
        run("fn fact(x) { if x > 1 { x * fact(x-1) } else { 1 } } fact(5)"),
        int(120)
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
        bool(true)
    );
    assert_eq!(run("fn f(a) { let p = g(a); } fn g(a) { 0 }"), unit());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fn_pipes() {
    assert_eq!(run("1 |> add(1)"), int(2));
    assert_eq!(run("2 |> mul(3) |> add(1) |> div(2)"), float(3.5));
    assert_eq!(
        run("let mut a = 1; a = 2 |> mul(3) |> add(1) |> div(2); a"),
        float(3.5)
    );
    assert_eq!(
        run("[1, 2] |> array_concat([3, 4]) |> array_map(|x| x*x)"),
        int_a![1, 4, 9, 16]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn properties() {
    set_property_value(0);
    assert_eq!(run("@props::my_scope.my_var"), int(0));
    set_property_value(1);
    assert_eq!(run("@props::my_scope.my_var"), int(1));
    run("@props::my_scope.my_var = 2");
    assert_eq!(get_property_value(), 2);
    run("@props::my_scope.my_var = @props::my_scope.my_var * 2 + 3");
    assert_eq!(get_property_value(), 7);
    run("fn f(x) { x * 2 } @props::my_scope.my_var = f(@props::my_scope.my_var)");
    assert_eq!(get_property_value(), 14);
    fail_compilation("@props::my_scope.my_var.a")
        .into_inner()
        .into_invalid_record_field_access()
        .unwrap();
    fail_compilation("@props::my_scope.my_var.a = 2")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
}
