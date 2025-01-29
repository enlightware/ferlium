// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;

use super::common::{fail_compilation, run, unit};
use painturscript::{error::MutabilityMustBeWhat, value::Value};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
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
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
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
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn exprs_in_match() {
    assert_eq!(
        run("match 0 { 0 => { let a = 1; a }, _ => { let a = 2; 2 } }"),
        int!(1)
    );
    assert_eq!(
        run("match 5 { 0 => { let a = 1; a }, _ => { let a = 2; 2 } }"),
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
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn stuff_in_single_if() {
    assert_eq!(run("let mut a = 0; if true { a = a + 1}; a"), int!(1));
    assert_eq!(
        run("let mut a = [1]; if true { a[-1] = a[0] + 1 }; a"),
        int_a![2]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_and_let_polymorphism() {
    assert_eq!(
        run("let f = || []; let mut a = f(); array_append(a, 1); a[0]"),
        int!(1)
    );
    fail_compilation("let f = || []; let a = f(); ()").expect_unbound_ty_var();
    fail_compilation("let f = || []; let mut a = f(); ()").expect_unbound_ty_var();
    fail_compilation("let f = || []; let a = f(); array_append(a, 1); a[0]")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
    assert_eq!(
        run("let f = || []; let mut a = f(); array_append(a, 1); a[0]"),
        int!(1)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_and_lambda() {
    assert_eq!(
        run("let mut a = [1,2]; (|x| array_append(x, 3))(a); a"),
        int_a![1, 2, 3]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_access_in_module_functions() {
    assert_eq!(run("fn p(a) { let x = a[0]; }"), unit());
    assert_eq!(run("fn p(a) { let x = a[0]; x }"), unit());
    assert_eq!(run("fn p(a, i) { let x = a[i]; 0 }"), unit());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_mutable_references() {
    assert_eq!(
        run("fn set_1(a) { a = 1 } fn call_set_1(a) { set_1(a) } let mut a = 0; call_set_1(a); a"),
        int!(1)
    );
    assert_eq!(
        run("fn set_1(a) { a = 1 } fn call_set_1(a) { a = 2; set_1(a) } let mut a = 0; call_set_1(a); a"),
        int!(1)
    );
}
