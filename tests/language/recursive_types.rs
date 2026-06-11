// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Inference of recursive structural types without annotations.

use indoc::indoc;

use crate::harness::{TestSession, bool, int, variant_0, variant_t1};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn match_infers_recursive_variant() {
    let mut session = TestSession::new();

    assert_val_eq!(
        session.run(indoc! { r#"
            fn size(t) {
                match t {
                    Leaf(x) => 1,
                    Node(l, r) => size(l) + size(r),
                }
            }
            size(Node(Node(Leaf(1), Leaf(2)), Leaf(3)))
        "# }),
        int(3)
    );

    // A default arm leaves the variant open; the call site closes it.
    assert_val_eq!(
        session.run(indoc! { r#"
            fn size(t) {
                match t {
                    Node(l, r) => size(l) + size(r),
                    _ => 1,
                }
            }
            size(Node(Leaf(1), Leaf(2)))
        "# }),
        int(2)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn inferred_recursive_type_is_generic_over_payloads() {
    let mut session = TestSession::new();

    assert_val_eq!(
        session.run(indoc! { r#"
            fn size(t) {
                match t {
                    Leaf(x) => 1,
                    Node(l, r) => size(l) + size(r),
                }
            }
            size(Node(Leaf(1), Leaf(2))) + size(Leaf("hello"))
        "# }),
        int(3)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn inferred_recursive_type_unifies_with_declared_alias() {
    let mut session = TestSession::new();

    assert_val_eq!(
        session.run(indoc! { r#"
            type Tree<T> = Leaf(T) | Node(Tree<T>, Tree<T>);

            fn size(t) {
                match t {
                    Leaf(x) => 1,
                    Node(l, r) => size(l) + size(r),
                }
            }
            let t: Tree<int> = Node(Leaf(1), Node(Leaf(2), Leaf(3)));
            size(t)
        "# }),
        int(3)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn constructors_infer_recursive_variant() {
    let mut session = TestSession::new();

    assert_val_eq!(
        session.run(indoc! { r#"
            fn build(n) {
                if n == 0 { Nil } else { Cons(n, build(n - 1)) }
            }
            fn sum(l) {
                match l {
                    Nil => 0,
                    Cons(h, t) => h + sum(t),
                }
            }
            sum(build(3))
        "# }),
        int(6)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mutually_recursive_functions_infer_recursive_variant() {
    let mut session = TestSession::new();

    assert_val_eq!(
        session.run(indoc! { r#"
            fn is_even_len(l) {
                match l {
                    Nil => true,
                    Cons(h, t) => is_odd_len(t),
                }
            }
            fn is_odd_len(l) {
                match l {
                    Nil => false,
                    Cons(h, t) => is_even_len(t),
                }
            }
            is_even_len(Cons(1, Cons(2, Nil)))
        "# }),
        bool(true)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mutually_recursive_structures_infer_recursive_variants() {
    let mut session = TestSession::new();

    // The equation for `b` alone has no terminating payload; it terminates
    // through the variants of `a`, like declared `type A = Done | Next(B);
    // type B = Back(A);` does.
    assert_val_eq!(
        session.run(indoc! { r#"
            fn count_a(a) {
                match a {
                    ADone => 0,
                    ANext(b) => count_b(b),
                }
            }
            fn count_b(b) {
                match b {
                    BBack(a) => 1 + count_a(a),
                }
            }
            count_a(ANext(BBack(ANext(BBack(ADone)))))
        "# }),
        int(2)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_functions_can_consume_and_rebuild_structures() {
    let mut session = TestSession::new();

    // The match drives the input type and the constructors drive the output
    // type; both resolve to the same recursive variant.
    assert_val_eq!(
        session.run(indoc! { r#"
            fn add_one(l) {
                match l {
                    Nil => Nil,
                    Cons(h, t) => Cons(h + 1, add_one(t)),
                }
            }
            fn sum(l) {
                match l {
                    Nil => 0,
                    Cons(h, t) => h + sum(t),
                }
            }
            sum(add_one(Cons(1, Cons(2, Nil))))
        "# }),
        int(5)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn constructors_infer_mutually_recursive_variants() {
    let mut session = TestSession::new();

    // No match ever touches the values: the mutual cycle is closed by
    // variant defaulting alone, one equation at a time.
    assert_val_eq!(
        session.run(indoc! { r#"
            fn build_a(n) {
                if n == 0 { ADone } else { ANext(build_b(n)) }
            }
            fn build_b(n) {
                BBack(build_a(n - 1))
            }
            build_a(2)
        "# }),
        variant_t1(
            "ANext",
            variant_t1(
                "BBack",
                variant_t1("ANext", variant_t1("BBack", variant_0("ADone")))
            )
        )
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn nominal_enum_values_flow_into_unannotated_functions() {
    let mut session = TestSession::new();

    // The unqualified match patterns resolve to the nominal type through the
    // `Repr` constraint once the call provides a `Tree` value.
    assert_val_eq!(
        session.run(indoc! { r#"
            enum Tree {
                Leaf(int),
                Node(Tree, Tree),
            }

            fn build(n) {
                if n == 0 { Tree::Leaf(1) } else { Tree::Node(build(n - 1), build(n - 1)) }
            }
            fn size(t) {
                match t {
                    Leaf(x) => 1,
                    Node(l, r) => size(l) + size(r),
                }
            }
            size(build(2))
        "# }),
        int(4)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn inferred_recursion_threads_through_nominal_structs() {
    let mut session = TestSession::new();

    // The cycle passes through the parameter of a nominal generic struct:
    // the equation is R = Nil | Cons (P<R>), guarded by the Cons payload.
    assert_val_eq!(
        session.run(indoc! { r#"
            struct P<T> {
                value: int,
                next: T,
            }
            fn build(n) {
                if n == 0 { Nil } else { Cons(P { value: n, next: build(n - 1) }) }
            }
            fn sum(l) {
                match l {
                    Nil => 0,
                    Cons(p) => p.value + sum(p.next),
                }
            }
            sum(build(3))
        "# }),
        int(6)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn inferred_recursion_crosses_declared_recursive_worlds() {
    let mut session = TestSession::new();

    // A rose tree: the inferred equation R = TLeaf | TNode (List<R>) closes
    // through the recursive world of the declared generic alias.
    assert_val_eq!(
        session.run(indoc! { r#"
            type List<T> = Nil | Cons(T, List<T>);

            fn tree(n) {
                if n == 0 { TLeaf } else { TNode(Cons(tree(n - 1), Cons(tree(n - 1), Nil))) }
            }
            fn count(t) {
                match t {
                    TLeaf => 1,
                    TNode(children) => count_list(children),
                }
            }
            fn count_list(l) {
                match l {
                    Nil => 0,
                    Cons(h, t) => count(h) + count_list(t),
                }
            }
            count(tree(2))
        "# }),
        int(4)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn inferred_mutual_recursion_unifies_with_declared_aliases() {
    let mut session = TestSession::new();

    assert_val_eq!(
        session.run(indoc! { r#"
            type A = Done | Next(B);
            type B = Back(A);

            fn count_a(a) {
                match a {
                    Done => 0,
                    Next(b) => count_b(b),
                }
            }
            fn count_b(b) {
                match b {
                    Back(a) => 1 + count_a(a),
                }
            }
            let v: A = Next(Back(Next(Back(Done))));
            count_a(v)
        "# }),
        int(2)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn inferred_recursive_types_cross_module_boundaries() {
    let mut session = TestSession::new();

    // A producer and a consumer of an inferred structural recursive type,
    // exported from a module and used from outside it.
    session
        .try_compile_module(
            "lists",
            indoc! { r#"
                pub fn build(n) {
                    if n == 0 { Nil } else { Cons(n, build(n - 1)) }
                }
                pub fn sum(l) {
                    match l {
                        Nil => 0,
                        Cons(h, t) => h + sum(t),
                    }
                }
            "# },
        )
        .expect("module with inferred recursive types should compile");

    assert_val_eq!(session.run("lists::sum(lists::build(3))"), int(6));
    assert_val_eq!(session.run("lists::sum(Cons(1, Cons(2, Nil)))"), int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unguarded_recursive_equations_are_rejected() {
    let mut session = TestSession::new();

    // Recursion through a function type is not guarded by a variant; the
    // application constrains `x` directly, so the equation closes and is
    // rejected within the function itself.
    session
        .fail_compilation(indoc! { r#"
            fn f(x) { x(x) }
            f(1)
        "# })
        .expect_infinite_type_ty_var_cycle();

    // Recursion through a named type's parameter nests forever: named shapes
    // are not unfolded, so the parameter does not guard the cycle, mirroring
    // the rule for declared recursive types.
    session
        .fail_compilation(indoc! { r#"
            enum BoxT<T> {
                B(T),
            }
            fn f(x) {
                f(BoxT::B(x))
            }
            f(1)
        "# })
        .expect_infinite_type_ty_var_cycle();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_equations_without_terminating_variant_are_rejected() {
    let mut session = TestSession::new();

    // A match constrains its scrutinee only through the deferred `Repr`
    // constraint (the scrutinee could also be a named type whose shape
    // matches), so a variant cycle does not close within the function: the
    // definition alone compiles, carrying an unsatisfiable `Repr` constraint.
    assert_val_eq!(
        session.run(indoc! { r#"
            fn depth(t) {
                match t {
                    Wrap(u) => 1 + depth(u),
                }
            }
            0
        "# }),
        int(0)
    );

    // The cycle closes at the first call that makes the argument concrete,
    // where the missing terminating variant is rejected.
    session
        .fail_compilation(indoc! { r#"
            fn depth(t) {
                match t {
                    Wrap(u) => 1 + depth(u),
                }
            }
            depth(Wrap(1))
        "# })
        .expect_infinite_type_ty_var_sum_cycle_without_terminating_variant();

    // The same holds for a mutual constructor-only group with no terminating
    // variant in any of its members.
    session
        .fail_compilation(indoc! { r#"
            fn build_a(n) {
                ANext(build_b(n))
            }
            fn build_b(n) {
                BBack(build_a(n - 1))
            }
            build_a(2)
        "# })
        .expect_infinite_type_ty_var_sum_cycle_without_terminating_variant();
}
