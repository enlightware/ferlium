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

use crate::common::float;

use super::common::{bool, fail_compilation, int, run, unit};
use ferlium::{error::MutabilityMustBeWhat, value::Value};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn logic_and_comparison() {
    assert_eq!(run("1 < 2 and 2 < 3"), bool(true));
    assert_eq!(run("1 < 2 and 2 > 3"), bool(false));
    assert_eq!(run("1 < 2 or 2 > 3"), bool(true));
    assert_eq!(run("1 > 2 or 2 > 3"), bool(false));
    assert_eq!(run("1 < 2 and 2 < 3 and 3 < 4"), bool(true));
    assert_eq!(run("1 < 2 and 2 < 3 and 3 > 4"), bool(false));
    assert_eq!(run("1 < 2 or 2 > 3 or 3 < 4"), bool(true));
    assert_eq!(run("1 > 2 or 2 > 3 or 3 < 4"), bool(true));
    assert_eq!(run("1 > 2 or 2 > 3 or 3 > 4"), bool(false));
    assert_eq!(run("1 < 2 and 2 < 3 or 3 < 4"), bool(true));
    assert_eq!(run("1 < 2 and 2 > 3 or 3 < 4"), bool(true));
    assert_eq!(run("1 < 2 and 2 > 3 or 3 > 4"), bool(false));
    assert_eq!(run("1 > 2 and 2 < 3 or 3 < 4"), bool(true));
    assert_eq!(run("1 > 2 and 2 < 3 or 3 > 4"), bool(false));
    assert_eq!(run("1 > 2 and 2 > 3 or 3 < 4"), bool(true));
    assert_eq!(run("1 > 2 and 2 > 3 or 3 > 4"), bool(false));
    assert_eq!(run("1 < 2 or 2 < 3 and 3 < 4"), bool(true));
    assert_eq!(run("1 < 2 or 2 < 3 and 3 > 4"), bool(true));
    assert_eq!(run("1 < 2 or 2 > 3 and 3 < 4"), bool(true));
    assert_eq!(run("1 < 2 or 2 > 3 and 3 > 4"), bool(true));
    assert_eq!(run("1 > 2 or 2 < 3 and 3 < 4"), bool(true));
    assert_eq!(run("1 > 2 or 2 < 3 and 3 > 4"), bool(false));
    assert_eq!(run("1 > 2 or 2 > 3 and 3 < 4"), bool(false));
    assert_eq!(run("1 > 2 or 2 > 3 and 3 > 4"), bool(false));
    assert_eq!(run("(1 < 2 or 2 < 3) and 3 < 4"), bool(true));
    assert_eq!(run("(1 < 2 or 2 < 3) and 3 > 4"), bool(false));
    assert_eq!(run("(1 < 2 or 2 > 3) and 3 < 4"), bool(true));
    assert_eq!(run("(1 < 2 or 2 > 3) and 3 > 4"), bool(false));
    assert_eq!(run("(1 > 2 or 2 < 3) and 3 < 4"), bool(true));
    assert_eq!(run("(1 > 2 or 2 < 3) and 3 > 4"), bool(false));
    assert_eq!(run("(1 > 2 or 2 > 3) and 3 < 4"), bool(false));
    assert_eq!(run("(1 > 2 or 2 > 3) and 3 > 4"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn lambdas_in_containers() {
    assert_eq!(run("(|| 1,).0()"), int(1));
    assert_eq!(run("[|| 1][0]()"), int(1));
    assert_eq!(run("let i = 0; [|| 1][i]()"), int(1));
    assert_eq!(run("let i = 0; [|| 1][i + 0]()"), int(1));
    assert_eq!(
        run("let f = ([|i| i + 1, |x| x*x], 3); let i = 1; f.0[0](f.0[i](f.1))"),
        int(10)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn exprs_in_match() {
    assert_eq!(
        run("match 0 { 0 => { let a = 1; a }, _ => { let a = 2; 2 } }"),
        int(1)
    );
    assert_eq!(
        run("match 5 { 0 => { let a = 1; a }, _ => { let a = 2; 2 } }"),
        int(2)
    );
    assert_eq!(
        run("match 0 { 0 => |x| x * 2, _ => |x| x * x } (3)"),
        int(6)
    );
    assert_eq!(
        run("match 1 { 0 => |x| x * 2, _ => |x| x * x } (3)"),
        int(9)
    );
    assert_eq!(run("match 0 { 0 => (1,2), _ => (2,3) }"), int_tuple!(1, 2));
    assert_eq!(run("match 1 { 0 => (1,2), _ => (2,3) }"), int_tuple!(2, 3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn record_wildcards_in_match() {
    assert_eq!(
        run("match (Some { x: 1, y: 2, z: 3 }) { Some { x, .. } => x + 10 }"),
        int(11)
    );
    assert_eq!(
        run("match (Some { a: 5, b: 6, c: 7, d: 8 }) { Some { b, d, .. } => b * d }"),
        int(48)
    );
    assert_eq!(
        run(indoc! { "
            enum Action {
                Move { x: float, y: float }
            }
            match (Action::Move { x: 5, y: 6 }) {
                Move { x, .. } => x
            }
        "}),
        float(5.0)
    );
    // errors
    fail_compilation("match (Some { x: 1, y: 2, z: 3 }) { Some { .., x } => x + 10 }")
        .into_inner()
        .as_record_wildcard_pattern_not_at_end()
        .unwrap();
    fail_compilation("match (Some { x: 1, y: 2, z: 3 }) { Some { .., x, .. } => x + 10 }")
        .into_inner()
        .as_record_wildcard_pattern_not_at_end()
        .unwrap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn tuple_wildcards_in_match_is_unsupported() {
    fail_compilation("match Some(1, 2, 3) { Some(x, .., z) => x + z }")
        .into_inner()
        .as_unsupported()
        .unwrap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn stuff_in_single_if() {
    assert_eq!(run("let mut a = 0; if true { a = a + 1}; a"), int(1));
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
        int(1)
    );
    fail_compilation("let f = || []; let a = f(); ()").expect_unbound_ty_var();
    fail_compilation("let f = || []; let mut a = f(); ()").expect_unbound_ty_var();
    fail_compilation("let f = || []; let a = f(); array_append(a, 1); a[0]")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
    assert_eq!(
        run("let f = || []; let mut a = f(); array_append(a, 1); a[0]"),
        int(1)
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
        int(1)
    );
    assert_eq!(
        run(
            "fn set_1(a) { a = 1 } fn call_set_1(a) { a = 2; set_1(a) } let mut a = 0; call_set_1(a); a"
        ),
        int(1)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fn_pipes_and_if_expr() {
    assert_eq!(run("2 |> (if true { |x| x } else { |x| -x }) ()"), int(2));
    assert_eq!(run("2 |> (if false { |x| x } else { |x| -x }) ()"), int(-2));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn minimalist_variants_and_trait_constraints() {
    assert_eq!(
        run(indoc! { r#"
            fn count_somes(a) {
                let mut sum = 0;
                for option in a {
                    match option {
                        Some(a) => sum = sum + 1,
                        None => ()
                    }
                };
                sum
            }

            count_somes([None, Some(true), None, None, Some(false)])
        "# }),
        int(2)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn double_loop() {
    assert_eq!(
        run(indoc! { r#"
            fn sums() {
                let mut sum = 0;
                for i in 1..3 {
                    for j in 1..4 {
                        sum = sum + i * j;
                    }
                };
                sum
            }

            sums()
        "# }),
        int(18)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn early_returns_in_unexpected_places() {
    // Test evaluation order: function application should evaluate function before arguments
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                (if true { return 42 } else { |x| x })(1)
            }
            f()
        "# }),
        int(42)
    );

    // Test evaluation order: arguments evaluated left-to-right, return in first arg
    assert_eq!(
        run(indoc! { r#"
            fn add(a, b) { a + b }
            fn f() {
                add({ return 100 }, { panic("should not reach") })
            }
            f()
        "# }),
        int(100)
    );

    // Test return in nested blocks with environment cleanup
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                let a = 1;
                {
                    let b = 2;
                    {
                        let c = 3;
                        return a + b + c;
                        let d = 4;
                    };
                    let e = 5;
                };
                let f = 6;
                99
            }
            f()
        "# }),
        int(6)
    );

    // Test return in array literal construction
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                [1, 2, { return 42 }, 4][0]
            }
            f()
        "# }),
        int(42)
    );

    // Test return in tuple construction
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                (1, { return 42 }, 3).0
            }
            f()
        "# }),
        int(42)
    );

    // Test return in record construction
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                { x: 1, y: { return 42 }, z: 3 }.x
            }
            f()
        "# }),
        int(42)
    );

    // Test return in variant construction
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                Some({ return 42 }); 1
            }
            f()
        "# }),
        int(42)
    );

    // Test return in match with early exit in condition
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                match { return 42 } {
                    0 => 1,
                    _ => 2
                }
            }
            f()
        "# }),
        int(42)
    );

    // Test return in closure capture
    // TODO: use once closures are implemented
    // assert_eq!(
    //     run(indoc! { r#"
    //         fn f() {
    //             let x = { return 42 };
    //             || x
    //         }
    //         f()
    //     "# }),
    //     int(42)
    // );

    // Test multiple returns in sequence (first one wins)
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                return 1;
                return 2;
                return 3;
                99
            }
            f()
        "# }),
        int(1)
    );

    // Test return doesn't leak from nested function
    assert_eq!(
        run(indoc! { r#"
            fn outer() {
                let inner = || { return 42 };
                let result = inner();
                result + 1
            }
            outer()
        "# }),
        int(43)
    );

    // Test return in deeply nested loops
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                for i in 0..5 {
                    for j in 0..5 {
                        for k in 0..5 {
                            if i == 2 and j == 3 and k == 4 {
                                return i * 100 + j * 10 + k
                            }
                        }
                    }
                };
                999
            }
            f()
        "# }),
        int(234)
    );

    // Test return in loop with side effects before return
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                let mut sum = 0;
                for i in 0..10 {
                    sum = sum + i;
                    if i == 5 {
                        return sum
                    }
                };
                999
            }
            f()
        "# }),
        int(15) // 0+1+2+3+4+5 = 15
    );

    // Test that return type checking works with complex expressions
    assert_eq!(
        run(indoc! { r#"
            fn f() -> (int, bool) {
                if true {
                    return (1, true)
                };
                (2, false)
            }
            f()
        "# }),
        Value::tuple([int(1), bool(true)])
    );

    // Test return in array index evaluation
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                let arr = [10, 20, 30];
                arr[{ return 42 }]
            }
            f()
        "# }),
        int(42)
    );

    // Test return in lambda used in higher-order function
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                let arr = [1, 2, 3];
                array_map(arr, |x| { if x == 2 { return 42 } else { x } })
            }
            f()
        "# }),
        int_a!(1, 42, 3)
    );

    // Test return in field access on tuple
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                let t = (1, 2, 3);
                ({ return 42 }, t.1).1
            }
            f()
        "# }),
        int(42)
    );

    // Test return with arithmetic operations
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                let x = 5;
                return x * 2 + 3;
                99
            }
            f()
        "# }),
        int(13)
    );

    // Test return inside match arm with computation
    assert_eq!(
        run(indoc! { r#"
            fn f(x) {
                match x {
                    0 => 1,
                    1 => { return 10 + 5 },
                    _ => 2
                }
            }
            f(1)
        "# }),
        int(15)
    );

    // Test return array indexing
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                let a = [1, 2, 3];
                (if true { return 42 } else { a })[0]
            }
            f()
        "# }),
        int(42)
    );
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                let a = [1, 2, 3];
                a[(if true { return 42 } else { 0 })]
            }
            f()
        "# }),
        int(42)
    );
    assert_eq!(
        run(indoc! { r#"
            fn f() {
                let a = [1, 2, 3];
                a[(if false { return 42 } else { 0 })]
            }
            f()
        "# }),
        int(1)
    );
}
