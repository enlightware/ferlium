// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;

use indoc::indoc;

use crate::harness::{TestSession, bool, float, int, unit};
use ferlium::{
    error::MutabilityMustBeWhat, std::core_traits_names::NUM_TRAIT_NAME,
    type_scheme::PubTypeConstraint, value::Value,
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn logic_and_comparison() {
    let mut session = TestSession::new();
    assert_eq!(session.run("1 < 2 and 2 < 3"), bool(true));
    assert_eq!(session.run("1 < 2 and 2 > 3"), bool(false));
    assert_eq!(session.run("1 < 2 or 2 > 3"), bool(true));
    assert_eq!(session.run("1 > 2 or 2 > 3"), bool(false));
    assert_eq!(session.run("1 < 2 and 2 < 3 and 3 < 4"), bool(true));
    assert_eq!(session.run("1 < 2 and 2 < 3 and 3 > 4"), bool(false));
    assert_eq!(session.run("1 < 2 or 2 > 3 or 3 < 4"), bool(true));
    assert_eq!(session.run("1 > 2 or 2 > 3 or 3 < 4"), bool(true));
    assert_eq!(session.run("1 > 2 or 2 > 3 or 3 > 4"), bool(false));
    assert_eq!(session.run("1 < 2 and 2 < 3 or 3 < 4"), bool(true));
    assert_eq!(session.run("1 < 2 and 2 > 3 or 3 < 4"), bool(true));
    assert_eq!(session.run("1 < 2 and 2 > 3 or 3 > 4"), bool(false));
    assert_eq!(session.run("1 > 2 and 2 < 3 or 3 < 4"), bool(true));
    assert_eq!(session.run("1 > 2 and 2 < 3 or 3 > 4"), bool(false));
    assert_eq!(session.run("1 > 2 and 2 > 3 or 3 < 4"), bool(true));
    assert_eq!(session.run("1 > 2 and 2 > 3 or 3 > 4"), bool(false));
    assert_eq!(session.run("1 < 2 or 2 < 3 and 3 < 4"), bool(true));
    assert_eq!(session.run("1 < 2 or 2 < 3 and 3 > 4"), bool(true));
    assert_eq!(session.run("1 < 2 or 2 > 3 and 3 < 4"), bool(true));
    assert_eq!(session.run("1 < 2 or 2 > 3 and 3 > 4"), bool(true));
    assert_eq!(session.run("1 > 2 or 2 < 3 and 3 < 4"), bool(true));
    assert_eq!(session.run("1 > 2 or 2 < 3 and 3 > 4"), bool(false));
    assert_eq!(session.run("1 > 2 or 2 > 3 and 3 < 4"), bool(false));
    assert_eq!(session.run("1 > 2 or 2 > 3 and 3 > 4"), bool(false));
    assert_eq!(session.run("(1 < 2 or 2 < 3) and 3 < 4"), bool(true));
    assert_eq!(session.run("(1 < 2 or 2 < 3) and 3 > 4"), bool(false));
    assert_eq!(session.run("(1 < 2 or 2 > 3) and 3 < 4"), bool(true));
    assert_eq!(session.run("(1 < 2 or 2 > 3) and 3 > 4"), bool(false));
    assert_eq!(session.run("(1 > 2 or 2 < 3) and 3 < 4"), bool(true));
    assert_eq!(session.run("(1 > 2 or 2 < 3) and 3 > 4"), bool(false));
    assert_eq!(session.run("(1 > 2 or 2 > 3) and 3 < 4"), bool(false));
    assert_eq!(session.run("(1 > 2 or 2 > 3) and 3 > 4"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn lambdas_in_containers() {
    let mut session = TestSession::new();
    assert_eq!(session.run("(|| 1,).0()"), int(1));
    assert_eq!(session.run("[|| 1][0]()"), int(1));
    assert_eq!(session.run("let i = 0; [|| 1][i]()"), int(1));
    assert_eq!(session.run("let i = 0; [|| 1][i + 0]()"), int(1));
    assert_eq!(
        session.run("let f = ([|i| i + 1, |x| x*x], 3); let i = 1; f.0[0](f.0[i](f.1))"),
        int(10)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn exprs_in_match() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("match 0 { 0 => { let a = 1; a }, _ => { let a = 2; 2 } }"),
        int(1)
    );
    assert_eq!(
        session.run("match 5 { 0 => { let a = 1; a }, _ => { let a = 2; 2 } }"),
        int(2)
    );
    assert_eq!(
        session.run("match 0 { 0 => |x| x * 2, _ => |x| x * x } (3)"),
        int(6)
    );
    assert_eq!(
        session.run("match 1 { 0 => |x| x * 2, _ => |x| x * x } (3)"),
        int(9)
    );
    assert_eq!(
        session.run("match 0 { 0 => (1,2), _ => (2,3) }"),
        int_tuple!(1, 2)
    );
    assert_eq!(
        session.run("match 1 { 0 => (1,2), _ => (2,3) }"),
        int_tuple!(2, 3)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn record_wildcards_in_match() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("match (Some { x: 1, y: 2, z: 3 }) { Some { x, .. } => x + 10 }"),
        int(11)
    );
    assert_eq!(
        session.run("match (Some { a: 5, b: 6, c: 7, d: 8 }) { Some { b, d, .. } => b * d }"),
        int(48)
    );
    assert_eq!(
        session.run(indoc! { "
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
    session
        .fail_compilation("match (Some { x: 1, y: 2, z: 3 }) { Some { .., x } => x + 10 }")
        .into_inner()
        .as_record_wildcard_pattern_not_at_end()
        .unwrap();
    session
        .fail_compilation("match (Some { x: 1, y: 2, z: 3 }) { Some { .., x, .. } => x + 10 }")
        .into_inner()
        .as_record_wildcard_pattern_not_at_end()
        .unwrap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn tuple_wildcards_in_match_is_unsupported() {
    let mut session = TestSession::new();
    session
        .fail_compilation("match Some(1, 2, 3) { Some(x, .., z) => x + z }")
        .into_inner()
        .as_unsupported()
        .unwrap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn stuff_in_single_if() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("let mut a = 0; if true { a = a + 1}; a"),
        int(1)
    );
    assert_eq!(
        session.run("let mut a = [1]; if true { a[-1] = a[0] + 1 }; a"),
        int_a![2]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_and_let_polymorphism() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("let f = || []; let mut a = f(); array_append(a, 1); a[0]"),
        int(1)
    );
    session
        .fail_compilation("let f = || []; let a = f(); ()")
        .expect_unbound_ty_var();
    session
        .fail_compilation("let f = || []; let mut a = f(); ()")
        .expect_unbound_ty_var();
    session
        .fail_compilation("let f = || []; let a = f(); array_append(a, 1); a[0]")
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
    assert_eq!(
        session.run("let f = || []; let mut a = f(); array_append(a, 1); a[0]"),
        int(1)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_and_lambda() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("let mut a = [1,2]; (|x| array_append(x, 3))(a); a"),
        int_a![1, 2, 3]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_access_in_module_functions() {
    let mut session = TestSession::new();
    assert_eq!(session.run("fn p(a) { let x = a[0]; }"), unit());
    assert_eq!(session.run("fn p(a) { let x = a[0]; x }"), unit());
    assert_eq!(session.run("fn p(a, i) { let x = a[i]; 0 }"), unit());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn explicit_generic_module_functions() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
            fn keep<T>(value: T) -> T {
                let identity = |candidate| {
                    let typed: T = candidate;
                    typed
                };
                identity(value)
            }

            let left = keep(1);
            let right = keep(true);
            if right { left } else { 0 }
        "# }),
        int(1)
    );

    let keep = session.compile_and_get_fn_def(
        indoc! { r#"
            fn keep<T>(value: T) -> T {
                let identity = |candidate| {
                    let typed: T = candidate;
                    typed
                };
                identity(value)
            }
        "# },
        "keep",
    );
    assert_eq!(keep.ty_scheme.ty_quantifiers.len(), 1);
    assert!(keep.ty_scheme.constraints.is_empty());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn function_where_clauses_are_enforced() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
            fn keep_ord<T>(value: T) -> T
            where
                T: Ord
            {
                value
            }

            keep_ord(1) + keep_ord(2)
        "# }),
        int(3)
    );

    let keep_ord = session.compile_and_get_fn_def(
        indoc! { r#"
            fn keep_ord<T>(value: T) -> T
            where
                T: Ord
            {
                value
            }
        "# },
        "keep_ord",
    );
    assert_eq!(keep_ord.ty_scheme.ty_quantifiers.len(), 1);
    assert_eq!(keep_ord.ty_scheme.constraints.len(), 1);

    session.fail_compilation(indoc! { r#"
        fn keep_ord<T>(value: T) -> T
        where
            T: Ord
        {
            value
        }

        keep_ord(|x| x)
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_impl_methods_with_local_generics_or_where_clauses_are_unsupported() {
    let mut session = TestSession::new();

    assert_eq!(
        session
            .fail_compilation(indoc! { r#"
                struct Wrapper(int)

                impl Cast for <From = int, To = Wrapper> {
                    fn cast<T>(self) -> Wrapper {
                        Wrapper(self)
                    }
                }
            "# })
            .into_inner()
            .into_unsupported()
            .unwrap()
            .1,
        "Explicit generic parameters on trait impl methods are not supported yet: method `cast` in impl of trait `Cast`"
    );

    assert_eq!(
        session
            .fail_compilation(indoc! { r#"
                struct Wrapper<T>(T)

                impl<T> Cast for <From = T, To = Wrapper<T>> {
                    fn cast(self) -> Wrapper<T>
                    where
                        T: Ord
                    {
                        Wrapper(self)
                    }
                }
            "# })
            .into_inner()
            .into_unsupported()
            .unwrap()
            .1,
        "Method-local where clauses on trait impl methods are not supported yet: method `cast` in impl of trait `Cast`"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_mutable_references() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(
            "fn set_1(a) { a = 1 } fn call_set_1(a) { set_1(a) } let mut a = 0; call_set_1(a); a"
        ),
        int(1)
    );
    assert_eq!(
        session.run(
            "fn set_1(a) { a = 1 } fn call_set_1(a) { a = 2; set_1(a) } let mut a = 0; call_set_1(a); a"
        ),
        int(1)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fn_pipes_and_if_expr() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run("2 |> (if true { |x| x } else { |x| -x }) ()"),
        int(2)
    );
    assert_eq!(
        session.run("2 |> (if false { |x| x } else { |x| -x }) ()"),
        int(-2)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn minimalist_variants_and_trait_constraints() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
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
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
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
    let mut session = TestSession::new();
    // Test evaluation order: function application should evaluate function before arguments
    assert_eq!(
        session.run(indoc! { r#"
            fn f() {
                (if true { return 42 } else { |x| x })(1)
            }
            f()
        "# }),
        int(42)
    );

    // Test evaluation order: arguments evaluated left-to-right, return in first arg
    assert_eq!(
        session.run(indoc! { r#"
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
        session.run(indoc! { r#"
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
        session.run(indoc! { r#"
            fn f() {
                [1, 2, { return 42 }, 4][0]
            }
            f()
        "# }),
        int(42)
    );

    // Test return in tuple construction
    assert_eq!(
        session.run(indoc! { r#"
            fn f() {
                (1, { return 42 }, 3).0
            }
            f()
        "# }),
        int(42)
    );

    // Test return in record construction
    assert_eq!(
        session.run(indoc! { r#"
            fn f() {
                { x: 1, y: { return 42 }, z: 3 }.x
            }
            f()
        "# }),
        int(42)
    );

    // Test return in variant construction
    assert_eq!(
        session.run(indoc! { r#"
            fn f() {
                Some({ return 42 }); 1
            }
            f()
        "# }),
        int(42)
    );

    // Test return in match with early exit in condition
    assert_eq!(
        session.run(indoc! { r#"
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
    // FIXME: issue https://github.com/enlightware/ferlium/issues/121
    // assert_eq!(
    //     session.run(indoc! { r#"
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
        session.run(indoc! { r#"
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
        session.run(indoc! { r#"
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
        session.run(indoc! { r#"
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
        session.run(indoc! { r#"
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
        session.run(indoc! { r#"
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
        session.run(indoc! { r#"
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
        session.run(indoc! { r#"
            fn f() {
                let arr = [1, 2, 3];
                map(arr, |x| { if x == 2 { return 42 } else { x } })
            }
            f()
        "# }),
        int_a!(1, 42, 3)
    );

    // Test return in field access on tuple
    assert_eq!(
        session.run(indoc! { r#"
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
        session.run(indoc! { r#"
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
        session.run(indoc! { r#"
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
        session.run(indoc! { r#"
            fn f() {
                let a = [1, 2, 3];
                (if true { return 42 } else { a })[0]
            }
            f()
        "# }),
        int(42)
    );
    assert_eq!(
        session.run(indoc! { r#"
            fn f() {
                let a = [1, 2, 3];
                a[(if true { return 42 } else { 0 })]
            }
            f()
        "# }),
        int(42)
    );
    assert_eq!(
        session.run(indoc! { r#"
            fn f() {
                let a = [1, 2, 3];
                a[(if false { return 42 } else { 0 })]
            }
            f()
        "# }),
        int(1)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn circular_imports_functions() {
    let mut session = TestSession::new();
    session.try_compile_module("A", "fn f() {}").unwrap();
    session
        .try_compile_module("B", "fn g() { A::f() }")
        .unwrap();
    session
        .try_compile_module("A", "fn f() { B::g() }")
        .unwrap_err()
        .as_circular_import_dependency()
        .unwrap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn oop_style_dispatch_via_first_class_fns_in_records() {
    let mut session = TestSession::new();

    // A "shape" object is an anonymous record whose fields are first-class
    // functions acting as methods.  Different concrete shapes share the same
    // interface (same field names) but carry different closure implementations.

    // Basic dispatch: call `.area` directly on a locally-bound object.
    assert_eq!(
        session.run(indoc! { r#"
            let circle = { area: || 3, describe: || 1 };
            circle.area()
        "# }),
        int(3)
    );

    // Closures capture their own data, giving each "instance" its own state.
    assert_eq!(
        session.run(indoc! { r#"
            let r = 5;
            let circle = { area: || r * r };
            let w = 4;
            let h = 3;
            let rect = { area: || w * h };
            circle.area() + rect.area()
        "# }),
        int(37)
    );

    // A named helper function that accepts any record with an `.area` field
    // and calls it — the structural-typing equivalent of an interface.
    // Each call dispatches to a different closure implementation at runtime.
    assert_eq!(
        session.run(indoc! { r#"
            fn total_area(shape) { shape.area() }
            let r = 7;
            let circle = { area: || r * r };
            let w = 4;
            let h = 3;
            let rect   = { area: || w * h };
            total_area(circle) + total_area(rect)
        "# }),
        int(61)
    );

    // Accumulating areas from an array of heterogeneous "objects" by
    // indexing each element — each slot carries its own closure, so
    // every `.area()` call dispatches to a different implementation.
    // Note: the `-> int` anotation works around a limitation of Num defaulting propagation.
    assert_eq!(
        session.run(indoc! { r#"
            fn sum_areas(shapes) -> int {
                let mut total = 0;
                for shape in shapes {
                    total = total + shape.area()
                };
                total
            }
            let r = 3;
            let circle = { area: || r * r };
            let w = 4;
            let h = 2;
            let rect   = { area: || w * h };
            let s = 5;
            let square = { area: || s * s };
            let shapes = [circle, rect, square];
            sum_areas(shapes)
        "# }),
        int(42)
    );

    // "Inheritance-like" extension: build a richer object by reusing a method
    // from a base object and adding a new one.  Both methods work correctly.
    assert_eq!(
        session.run(indoc! { r#"
            let side = 4;
            let base     = { area: || side * side };
            let extended = { area: base.area, perimeter: || side * 4 };
            extended.area() + extended.perimeter()
        "# }),
        int(32)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn calling_fn_field_on_named_fn_record_parameter() {
    let mut session = TestSession::new();

    // Simplest case: a named function with one record parameter whose sole
    // field is a nullary closure, called at a concrete call site.
    assert_eq!(
        session.run(indoc! { r#"
            fn invoke(obj) { obj.f() }
            invoke({ f: || 42 })
        "# }),
        int(42)
    );

    // The function can be called multiple times with records that carry
    // different closure implementations.
    assert_eq!(
        session.run(indoc! { r#"
            fn invoke(obj) { obj.f() }
            invoke({ f: || 1 }) + invoke({ f: || 2 })
        "# }),
        int(3)
    );

    // Works for closures that capture variables from their enclosing scope.
    assert_eq!(
        session.run(indoc! { r#"
            fn invoke(obj) { obj.f() }
            let x = 10;
            invoke({ f: || x * x })
        "# }),
        int(100)
    );

    // Works for closures that take arguments.
    assert_eq!(
        session.run(indoc! { r#"
            fn apply(obj, n) { obj.transform(n) }
            apply({ transform: |x| x + 1 }, 5)
        "# }),
        int(6)
    );

    // Works when the record carries additional non-function fields alongside
    // the function field (structural / row-polymorphic access).
    assert_eq!(
        session.run(indoc! { r#"
            fn get_label(obj) { obj.label() }
            get_label({ value: 99, label: || 7 })
        "# }),
        int(7)
    );
}

fn assert_f_defaults_num_after_dead_suffix(session: &mut TestSession, src: &str) {
    let runnable_src = format!("{src}\n\nf()");
    assert_eq!(
        session.run(&runnable_src),
        int(42),
        "runtime regression for:\n{src}"
    );

    let fn_def = session.compile_and_get_fn_def(src, "f");
    let num_trait = session.std_trait(NUM_TRAIT_NAME);
    assert_eq!(
        fn_def.ty_scheme.ty_quantifiers.len(),
        1,
        "type regression for:\n{src}"
    );
    assert_eq!(
        fn_def.ty_scheme.constraints.len(),
        1,
        "type regression for:\n{src}"
    );
    match &fn_def.ty_scheme.constraints[0] {
        PubTypeConstraint::HaveTrait {
            trait_ref,
            input_tys,
            output_tys,
            ..
        } => {
            assert_eq!(*trait_ref, num_trait, "type regression for:\n{src}");
            assert_eq!(
                input_tys.as_slice(),
                &[fn_def.ty_scheme.ty().ret],
                "type regression for:\n{src}",
            );
            assert!(output_tys.is_empty(), "type regression for:\n{src}");
        }
        other => panic!("expected Num constraint on the return type for:\n{src}\n got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unreachable_block_suffix_does_not_constrain_return_type() {
    let mut session = TestSession::new();
    let src = indoc! { r#"
        fn f() {
            let x = { return 42 };
            || x
        }

        f()
    "# };
    assert_eq!(session.run(src), int(42));

    let fn_def = session.compile_and_get_fn_def(
        indoc! { r#"
            fn f() {
                let x = { return 42 };
                || x
            }
        "# },
        "f",
    );
    let num_trait = session.std_trait(NUM_TRAIT_NAME);
    let module_env = session.std_module_env();
    assert_eq!(
        fn_def.ty_scheme.display_rust_style(&module_env).to_string(),
        "() -> A where A: Num"
    );
    assert_eq!(fn_def.ty_scheme.ty_quantifiers.len(), 1);
    assert_eq!(fn_def.ty_scheme.constraints.len(), 1);
    match &fn_def.ty_scheme.constraints[0] {
        PubTypeConstraint::HaveTrait {
            trait_ref,
            input_tys,
            output_tys,
            ..
        } => {
            assert_eq!(*trait_ref, num_trait);
            assert_eq!(input_tys.as_slice(), &[fn_def.ty_scheme.ty().ret]);
            assert!(output_tys.is_empty());
        }
        other => panic!("expected Num constraint on the return type, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unreachable_suffixes_in_other_expressions_do_not_constrain_return_type() {
    let mut session = TestSession::new();

    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let x = ({ return 42 }, || 0);
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let x = [{ return 42 }, || 0];
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let x = { x: { return 42 }, y: || 0 };
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn add(a, b) { a + b }

            fn f() {
                let x = add({ return 42 }, || 0);
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let x = { return 42 } + (|| 0);
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let g = |a, b| a + b;
                let x = g({ return 42 }, || 0);
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let x = ({ return 42; |a| a })(|| 0);
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let x = ({ return 42; (0, 1) }).0;
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let x = ({ return 42; { value: 0 } }).value;
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let x = ({ return 42; [0] })[|| 0];
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let x = [0][{ return 42 }];
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            struct Pair(int, int)

            fn f() {
                let x = Pair({ return 42 }, || 0);
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let x = Foo({ return 42 }, || 0);
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let x = match { return 42 } {
                    0 => 0,
                    _ => || 0,
                };
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let x = match 0 {
                    0 => { return 42 },
                    _ => { return 7 },
                };
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let mut a = [0];
                let x = a[0] = { return 42 };
                || x
            }
        "# },
    );
    assert_f_defaults_num_after_dead_suffix(
        &mut session,
        indoc! { r#"
            fn f() {
                let mut a = [0];
                let x = ({ return 42; a[0] }) = 0;
                || x
            }
        "# },
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn circular_imports_type_defs() {
    let mut session = TestSession::new();
    session.try_compile_module("A", "struct S;").unwrap();
    session.try_compile_module("B", "struct T(A::S)").unwrap();
    session
        .try_compile_module("A", "struct S(B::T)")
        .unwrap_err()
        .as_circular_import_dependency()
        .unwrap();
}
