// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Inference and comparison of recursive structural types.

use ferlium::types::effects::{PrimitiveEffect, effect, no_effects};

use indoc::indoc;

use crate::harness::{TestSession, bool, int, variant_0, variant_t1};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_comparison_widens_callback_effects() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            type Pure = () -> int;
            type Fallible = () -> int ! fallible;
            type List<T> = Nil | Cons(T, List<T>);
            fn coerce(xs: List<Pure>) -> List<Fallible> { xs }
            fn first(xs: List<Fallible>) -> int {
                match xs { Nil => 0, Cons(f, tail) => f() }
            }
            first(coerce(Cons(|| 42, Nil)))
        "# }),
        int(42)
    );
}

/// Widening the effect of a callback keeps a value's bytes, so a variant that holds the recursive
/// type in a payload must keep that payload behind a pointer, as the recursive type does.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn widening_a_callback_effect_keeps_the_layout_of_a_recursive_variant() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            type V = End | Next(V) | Other(() -> int ! ());
            #[inline(never)]
            fn initial(n: int) -> V {
                if n > 0 {
                    Next(initial(n - 1))
                } else {
                    End
                }
            }
            #[inline(never)]
            fn widen(x: V) -> End | Next(V) | Other(() -> int ! fallible) { x }
            #[inline(never)]
            fn depth(x: V) -> int {
                match x { End => 0, Next(t) => 1 + depth(t), Other(callback) => 7 }
            }
            #[inline(never)]
            fn f(n: int) -> int {
                match widen(initial(n)) { End => 0, Next(t) => 1 + depth(t), Other(callback) => 7 }
            }
            f(black_box(3))
        "# }),
        int(3)
    );
}

/// Types that differ only within callables, at any depth, have the same layout.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn types_differing_only_within_callables_have_the_same_layout() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            type V = End | Next(V) | Other(() -> int);
            type Top = End | Next(V) | Other(() -> int ! fallible);
            type Deep = End | Next(End | Next(V) | Other(() -> int ! fallible)) | Other(() -> int);
            fn widen_deep(x: V) -> Deep { x }
            (Value::<Top>::SIZE - Value::<V>::SIZE, Value::<Deep>::SIZE - Value::<V>::SIZE)
        "# }),
        tuple!(int(0), int(0))
    );
}

/// The type of a generic construction may be the recursive type itself once instantiated, whose
/// payload is behind a pointer.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_construction_of_an_instance_of_a_recursive_type() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            type V = End | Next(V);
            fn mk(n: int) -> V {
                if n > 0 {
                    Next(mk(n - 1))
                } else {
                    End
                }
            }
            fn next<A>(x: A) -> End | Next(A) { Next(x) }
            fn depth(v: V) -> int {
                match v {
                    End => 0,
                    Next(w) => 1 + depth(w),
                }
            }
            depth(next(mk(black_box(2))))
        "# }),
        int(3)
    );
}

/// A payload stored inline in generic code may be behind a pointer once instantiated: `List`
/// holds an `Option<List>`.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_construction_of_a_payload_that_becomes_recursive() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            type List = Nil | Cons(int, Option<List>);
            fn mkl(n: int) -> List {
                if n > 0 {
                    Cons(n, Some(mkl(n - 1)))
                } else {
                    Nil
                }
            }
            fn sum(l: List) -> int {
                match l {
                    Nil => 0,
                    Cons(n, t) => match t {
                        Some(r) => n + sum(r),
                        None => n,
                    },
                }
            }
            fn wrap<T>(x: T) -> Option<T> { Some(x) }
            sum(Cons(10, wrap(mkl(black_box(3)))))
        "# }),
        int(16)
    );
}

/// The storage of a closed payload may depend on another payload: `Next` is behind a pointer
/// only once `Other` holds an `int`.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_construction_of_a_closed_payload_whose_variant_becomes_recursive() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            type V = End | Next(V) | Other(int);
            fn mk<T>(v: V, x: T, which: bool) -> End | Next(V) | Other(T) {
                if which {
                    Next(v)
                } else {
                    Other(x)
                }
            }
            fn depth(v: V) -> int {
                match v {
                    End => 0,
                    Next(w) => 1 + depth(w),
                    Other(n) => n,
                }
            }
            let v: V = Next(End);
            let n = black_box(0);
            (depth(mk(v, n + 5, n == 0)), depth(mk(v, n + 5, n != 0)))
        "# }),
        tuple!(int(2), int(5))
    );
}

/// Generic code computes the layout of a variant as the instance does.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_layout_of_a_variant_that_becomes_recursive() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            type List = Nil | Cons(int, Option<List>);
            fn layout<T>(x: T) -> (int, int) { (Value::<Option<T>>::SIZE, Value::<Option<T>>::ALIGN) }
            fn structural<T>(x: T) -> int { Value::<(bool, None | Some(T))>::SIZE }
            let l: List = Nil;
            let (size, align) = layout(l);
            (
                size - Value::<Option<List>>::SIZE,
                align - Value::<Option<List>>::ALIGN,
                structural(l) - Value::<(bool, None | Some(List))>::SIZE,
            )
        "# }),
        tuple!(int(0), int(0), int(0))
    );
}

/// Generic code that keeps, copies and captures a variant of an open type uses the layout and
/// storage of the instance.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_code_handles_a_variant_that_becomes_recursive() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            type List = Nil | Cons(int, Option<List>);
            fn mkl(n: int) -> List {
                if n > 0 {
                    Cons(n, Some(mkl(n - 1)))
                } else {
                    Nil
                }
            }
            fn sum(l: List) -> int {
                match l {
                    Nil => 0,
                    Cons(n, t) => match t {
                        Some(r) => n + sum(r),
                        None => n,
                    },
                }
            }
            #[inline(never)]
            fn copies<T>(x: T) -> [Option<T>] {
                let o = Some(x);
                [o, o]
            }
            #[inline(never)]
            fn captures<T>(x: T) -> () -> Option<T> {
                let o = Some(x);
                || o
            }
            fn sum_option(o: Option<List>) -> int {
                match o {
                    Some(l) => sum(l),
                    None => 0,
                }
            }
            let l = mkl(black_box(3));
            let a = copies(l);
            sum_option(a[0]) + sum_option(a[1]) + sum_option(captures(l)())
        "# }),
        int(18)
    );
}

/// A closure capturing a variant of an open type lays its capture out as the instance does,
/// also when the variant's layout is built here from its cases.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_closure_captures_a_variant_that_becomes_recursive() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            enum Opt<T> { No, Yes(T) }
            type List = Nil | Cons(int, Opt<List>);
            fn mkl(n: int) -> List {
                if n > 0 {
                    Cons(n, Opt::Yes(mkl(n - 1)))
                } else {
                    Nil
                }
            }
            fn sum(l: List) -> int {
                match l {
                    Nil => 0,
                    Cons(n, t) => match t {
                        Yes(r) => n + sum(r),
                        No => n,
                    },
                }
            }
            #[inline(never)]
            fn captures<T>(x: T, y: T) -> () -> (Opt<T>, None | Some(T)) {
                let o = Opt::Yes(x);
                let p = Some(y);
                || (o, p)
            }
            let (o, p) = captures(mkl(black_box(3)), mkl(black_box(2)))();
            let first = match o {
                Yes(l) => sum(l),
                No => 0,
            };
            let second = match p {
                Some(l) => sum(l),
                None => 0,
            };
            first + second
        "# }),
        int(9)
    );
}

/// The dictionary of a variant needs the storage of the cases of a payload stored behind a
/// pointer too: its layout stops at the pointer, but its `clone` copies the payload.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_clone_reaches_cases_behind_an_indirect_payload() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            enum Tree<T> { Leaf(T), Node(A(Tree<T>) | B(T)) }
            fn both<T>(x: Tree<T>) -> (Tree<T>, Tree<T>) { (x, x) }
            let (x, y) = both(Tree::Node(B(3)));
            match y {
                Leaf(n) => n,
                Node(k) => match k {
                    A(unused) => 0,
                    B(n) => n,
                },
            }
        "# }),
        int(3)
    );
}

/// A written `Value` impl requires the storages that its generated layout getters read, even
/// when none of its methods reads them.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn written_value_impl_supplies_the_storage_its_layout_reads() {
    let mut session = TestSession::new();
    session.allow_unsafe();
    assert_val_eq!(
        session.run(indoc! { r#"
            enum V<T> { No, Yes(T) }
            impl<T> Value for V<T> where T: Value {
                fn eq(x: V<T>, y: V<T>) -> bool { true }
                fn to_string(x: V<T>) -> string { "V" }
                fn hash(x: V<T>, state: &mut hasher) {}
                fn clone(x: V<T>) -> V<T> { V::No }
                fn drop(x: &mut V<T>) {}
            }
            type L = Nil | Cons(V<L>);
            fn size<T>(x: T) -> int { Value::<V<T>>::SIZE }
            let l: L = Nil;
            (
                Value::<V<int>>::SIZE - Value::<No | Yes(int)>::SIZE,
                size(l) - Value::<V<L>>::SIZE,
            )
        "# }),
        tuple!(int(0), int(0))
    );
}

/// Cases whose payloads differ only in effects share their storage evidence, whichever of them
/// is built.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_construction_of_a_case_whose_payload_differs_only_in_effects() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            enum V<T> { A(() -> int ! ()), B(() -> int ! fallible), C(T) }
            #[inline(never)]
            fn make_b<T>(x: T, f: () -> int ! fallible) -> V<T> { V::B(f) }
            let v = make_b(black_box(1), || 3);
            match v {
                A(f) => f(),
                B(f) => f(),
                C(x) => x,
            }
        "# }),
        int(3)
    );
}

/// A generated layout getter chooses between layouts computed beforehand, so its paths through
/// the choices of nested open cases do not multiply. Found by fuzzing: verifying this getter took
/// minutes in a debug build when each choice computed its own layout.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn layout_getters_of_nested_open_cases_stay_small() {
    let mut session = TestSession::new();
    session
        .try_compile("enum A<a> {None(None([a]) | Ok, None | Some), Ok(Err(a, a) | Some, a), Some}")
        .expect("the enum compiles");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_comparison_checks_payload_after_cycle() {
    let mut session = TestSession::new();
    session
        .try_compile(indoc! { r#"
            type List<T> = Nil | Cons(List<T>, T);
            fn bad(xs: List<int>) -> List<bool> { xs }
        "# })
        .expect_err("closing the recursive edge must still check the following payload")
        .expect_type_mismatch("int", "bool");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_comparison_checks_effects_after_cycle() {
    let mut session = TestSession::new();
    session
        .try_compile(indoc! { r#"
            type Pure = () -> int;
            type Fallible = () -> int ! fallible;
            type List<T> = Nil | Cons(List<T>, T);
            fn bad(xs: List<Fallible>) -> List<Pure> { xs }
        "# })
        .expect_err("closing the recursive edge must not hide callback effects")
        .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_comparison_preserves_direction() {
    let mut session = TestSession::new();
    session
        .try_compile(indoc! { r#"
            type Pure = () -> int;
            type Fallible = () -> int ! fallible;
            type Recursive<T> = Done | Next((Recursive<T>) -> T);
            fn bad(x: Recursive<Pure>) -> Recursive<Fallible> { x }
        "# })
        .expect_err("a contravariant recursive edge must check the reverse relation")
        .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_comparison_preserves_named_invariance() {
    let mut session = TestSession::new();
    session
        .try_compile(indoc! { r#"
            type Pure = () -> int;
            type Fallible = () -> int ! fallible;
            struct Box<T>(T)
            type Recursive<T> = Done | Next(Recursive<T>, T);
            fn bad(x: Box<Recursive<Pure>>) -> Box<Recursive<Fallible>> { x }
        "# })
        .expect_err("recursive comparisons inside named arguments must preserve exact effects")
        .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_alias_preserves_named_argument_invariance() {
    let mut session = TestSession::new();
    session
        .try_compile(indoc! { r#"
            type Pure = () -> int;
            type Fallible = () -> int ! fallible;
            struct Box<T>(T)
            type Recursive<T> = Done | Next(Box<Recursive<T>>, T);
            fn bad(x: Recursive<Pure>) -> Recursive<Fallible> { x }
        "# })
        .expect_err("the Box argument must retain the recursive variant and its callback effects")
        .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_alias_values_through_named_type() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            struct Box<T>(T)
            type Recursive<T> = Done | Next(Box<Recursive<T>>, T);
            fn sum(xs: Recursive<int>) -> int {
                match xs { Done => 0, Next(tail, n) => n + sum(tail.0) }
            }
            sum(Next(Box(Next(Box(Done), 20)), 22))
        "# }),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_alias_values_through_array() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            type Tree = Leaf(int) | Branch([Tree]);
            fn sum(tree: Tree) -> int {
                match tree {
                    Leaf(n) => n,
                    Branch(children) => {
                        let mut total = 0;
                        for child in children { total += sum(child) };
                        total
                    },
                }
            }
            sum(Branch([Leaf(20), Branch([Leaf(22)])]))
        "# }),
        int(42)
    );
}

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
fn match_infers_recursive_variant_with_an_effect_generic() {
    // The payload of `Leaf` is named by no signature, only by what the function requires of
    // `t`: it is a type of the function all the same.
    assert_val_eq!(
        TestSession::new().run(indoc! { r#"
            fn size<! E>(t, g: () -> int ! E) -> int {
                match t {
                    Leaf(x) => g(),
                    Node(l, r) => size(l, g) + size(r, g),
                }
            }
            size(Node(Leaf(1), Leaf(2)), || 1) + size(Leaf("hello"), || 1)
        "# }),
        int(3)
    );
    assert_val_eq!(
        TestSession::new().run(indoc! { r#"
            fn is_even_len<! E>(l, g: () -> bool ! E) {
                match l {
                    Nil => g(),
                    Cons(h, t) => is_odd_len(t, g),
                }
            }
            fn is_odd_len(l, g) {
                match l {
                    Nil => false,
                    Cons(h, t) => is_even_len(t, g),
                }
            }
            is_even_len(Cons(1, Cons(2, Nil)), || true)
        "# }),
        bool(true)
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
fn constructors_infer_mutually_recursive_variants_with_an_effect_generic() {
    // The functions are inferred one by one against the signatures of the group: the type
    // that they build together is still one type, not a copy at each call.
    let mut session = TestSession::new();

    assert_val_eq!(
        session.run(indoc! { r#"
            fn build_a<! E>(n, g: () -> int ! E) {
                if n == 0 {
                    g();
                    ADone
                } else {
                    ANext(build_b(n, g))
                }
            }
            fn build_b(n, g) {
                BBack(build_a(n - 1, g))
            }
            build_a(2, || 1)
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

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_alias_equivalent_sharing_finds_trait_impl() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            type List<T> = Nil | Cons(T, List<T>);
            type Pair<T> = (T, T);
            type Repeated = Done | Next((List<Repeated>, List<Repeated>));
            type Shared = Done | Next(Pair<List<Shared>>);
            struct Wrapped<T>(T)
            trait Marker<Self> { fn tag(x: Self) -> int; }
            impl Marker for Wrapped<Repeated> { fn tag(x: Wrapped<Repeated>) -> int { 42 } }
            fn read(x: Wrapped<Shared>) -> int { Marker::tag(x) }
            read(Wrapped(Next((Cons(Done, Nil), Nil))))
        "# }),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_function_over_a_recursive_alias_is_specialized() {
    // Matching the parameter against the argument type leads back to the same two types.
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            type List<T> = Nil | Cons(T, List<T>);
            fn f<T>(x: List<T>) { x }
            f(Cons(1, Nil));
            1
        "# }),
        int(1)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_type_that_is_an_alias_of_itself_is_shown_once() {
    // `t` is `Option<t>`, and showing it used to recurse without end.
    TestSession::new()
        .fail_compilation("fn f<t>(x: t) { let r: Some(t) | None = x; x + 0; }")
        .expect_trait_impl_not_found("Num", &["Self = Option<Self>"]);
}
