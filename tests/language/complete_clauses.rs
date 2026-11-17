// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Complete `where` clauses: a written clause states the requirements that callers supply, with
//! those that they imply; the definition solves every other one itself, or is refused.

use test_log::test;

use ferlium::compiler::error::{CompilationErrorImpl, InvalidTraitConstraintKind};
use indoc::indoc;

use crate::harness::{TestSession, bool, expected_tuple, float, int, signature, string};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

/// A requirement that only the module's impls answer, built from a written one.
const RENDER: &str = indoc! { r#"
    pub struct Bag<T>(T)
    pub trait Display<Self> { fn display(x: Self) -> string; }
    impl Display for int { fn display(x: int) -> string { "i" } }
    pub trait Render<Self> { fn render(x: Self) -> string; }
    impl<T> Render for Bag<T> where T: Display, T: Value {
        fn render(x: Bag<T>) -> string { display(x.0) }
    }
"# };

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_complete_clause_solves_what_it_does_not_write() {
    let src = format!(
        "{RENDER}fn show<T>(x: Bag<T>) -> string where T: Display, T: Value {{ render(x) }}\n"
    );
    assert_val_eq!(
        TestSession::new().run(&format!("{src}show(Bag(1))")),
        string("i")
    );
    // The contract is what is written: the definition built `Bag<T>: Render` itself.
    assert_eq!(
        signature(&mut TestSession::new(), &src, "show"),
        "fn show<T>(x: Bag<T>) -> string where T: Display + Value"
    );
    // Partial, the same body leaves the requirement to its callers.
    let partial = format!(
        "{RENDER}fn show<T>(x: Bag<T>) -> string where T: Display, T: Value, .. {{ render(x) }}\n"
    );
    assert_eq!(
        signature(&mut TestSession::new(), &partial, "show"),
        "fn show<T>(x: Bag<T>) -> string where T: Display + Value, Bag<T>: Render"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_complete_clause_refuses_a_requirement_for_its_callers() {
    // `Bag<T>: Render` needs `T: Display`, which the clause does not write.
    TestSession::new()
        .fail_compilation(&format!(
            "{RENDER}fn show<T>(x: Bag<T>) -> string where T: Value {{ render(x) }}"
        ))
        .expect_undeclared_requirement("T: Display", false);
    // Writing it is enough.
    assert_val_eq!(
        TestSession::new().run(&format!(
            "{RENDER}fn show<T>(x: Bag<T>) -> string where T: Value, Bag<T>: Render {{ render(x) }}
            show(Bag(1))"
        )),
        string("i")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_complete_clause_accepts_what_it_implies_and_publishes_what_it_writes() {
    let src = indoc! { r#"
        fn twice<T>(x: T) -> T where T: Real { x + x }
        fn same<T>(x: T) -> T where T: Real, T: Value { x }
    "# };
    assert_val_eq!(
        TestSession::new().run(&format!("{src}(twice(1.5), same(2.5))")),
        expected_tuple([3.0, 2.5].map(crate::harness::float))
    );
    // `Real: Div: Num`: the body that adds reads `Num` from the dictionary of `Real`.
    assert_eq!(
        signature(&mut TestSession::new(), src, "twice"),
        "fn twice<T>(x: T) -> T where T: Real"
    );
    assert_eq!(
        signature(&mut TestSession::new(), src, "same"),
        "fn same<T>(x: T) -> T where T: Real + Value"
    );
    // A parent that leaves an output to the implementations has no slot: it is published when
    // the body uses it, as the dictionary of the written requirement does not hold it.
    let src = indoc! { r#"
        trait Act<Self |-> ! E> { fn act(x: Self) -> int ! E; }
        trait Named<Self>: Act<Self> {}
        impl Act for <Self = int |-> ! E = ()> { fn act(x: int) -> int { x } }
        impl Named for int {}
        fn run<T>(x: T) -> int where T: Named { act(x) }
    "# };
    assert!(signature(&mut TestSession::new(), src, "run").contains("Act"));
    assert_val_eq!(TestSession::new().run(&format!("{src}run(7)")), int(7));
}

/// `Container` implies `Source` at the same item; `W` reaches `Source` through an impl.
const CONTAINER: &str = indoc! { r#"
    trait Source<Self |-> Item> { fn source(x: Self) -> Item; }
    trait Container<Self |-> Item> where Self: Source<Item = Item> {}
    struct S(int)
    impl Source for <Self = S |-> Item = int> { fn source(x: S) -> int { x.0 } }
    impl Container for <Self = S |-> Item = int> {}
    struct W<T>(T)
    trait Get<Self |-> Item> { fn get(x: Self) -> Item; }
    impl<T, A> Get for <Self = W<T> |-> Item = A> where T: Source<Item = A>, T: Value {
        fn get(x: W<T>) -> A { source(x.0) }
    }
"# };

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_requirement_found_by_reduction_has_the_outputs_of_the_implied_one() {
    let clause = "where T: Container<Item = int>, T: Value";
    assert_val_eq!(
        TestSession::new().run(&format!(
            "{CONTAINER}fn f<T>(x: T) -> int {clause} {{ get(W(x)) }}\nf(S(3))"
        )),
        int(3)
    );
    TestSession::new()
        .fail_compilation(&format!(
            "{CONTAINER}fn f<T>(x: T) -> bool {clause} {{ get(W(x)) }}"
        ))
        .expect_type_mismatch("int", "bool");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_written_requirement_has_the_outputs_of_the_implied_one() {
    assert_val_eq!(
        TestSession::new().run(&format!(
            "{CONTAINER}fn f<T>(x: T) -> string where T: Container<Item = int>, T: Source<Item = _> {{
                to_string(source(x))
            }}
            f(S(5))"
        )),
        string("5")
    );
    TestSession::new()
        .fail_compilation(&format!(
            "{CONTAINER}fn f<T>(x: T) -> bool where T: Container<Item = int>, T: Source<Item = bool> {{
                source(x)
            }}"
        ))
        .expect_type_mismatch("int", "bool");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_sequence_implies_the_requirements_of_its_iterator() {
    assert_val_eq!(
        TestSession::new().run(indoc! { r#"
            fn count<S, A, I>(s: S) -> int where S: Seq<Item = A, Iter = I>, S: Value, I: Value, A: Value {
                let mut n = 0;
                for x in s {
                    n = n + 1
                };
                n
            }
            count([1, 2, 3])
        "# }),
        int(3)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn where_nothing_publishes_only_structural_requirements() {
    let src = "fn field<T>(x: T) -> int where nothing { x.a }\n";
    assert_val_eq!(
        TestSession::new().run(&format!("{src}field({{ a: 4 }})")),
        int(4)
    );
    assert!(
        signature(&mut TestSession::new(), src, "field").contains("where T: { a: int"),
        "the field requirement is published"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn nothing_is_still_a_type_name_in_a_requirement() {
    assert_val_eq!(
        TestSession::new().run(indoc! { r#"
            struct nothing(int)
            trait Show<Self> { fn show(x: Self) -> int; }
            impl Show for nothing { fn show(x: nothing) -> int { x.0 } }
            fn f<T>(x: T) -> int where nothing: Show { show(nothing(3)) }
            f(1)
        "# }),
        int(3)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_requirement_on_an_unnamed_type_asks_for_a_name() {
    // The type of the field has no name, so its `Num` cannot be written.
    TestSession::new()
        .fail_compilation("fn field<T>(x: T) where nothing { x.a + x.a }")
        .expect_undeclared_requirement("B: Num", true);
    // A generic ascribing a value of the body names it.
    assert_val_eq!(
        TestSession::new().run(indoc! { r#"
            fn field<T, B>(x: T) -> B where B: Num {
                let y: B = x.a;
                y + y
            }
            field({ a: 2 })
        "# }),
        int(4)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn the_value_of_a_type_variable_is_implicit_and_published_if_used() {
    let src = indoc! { r#"
        fn id<T>(x: T) -> T where nothing { x }
        fn len_of<A>(a: [A]) -> int where nothing { len(a) }
        fn field<T>(x: T) where nothing { x.a }
        fn ascribed<T, B>(x: T) -> int where nothing { let y: B = x.a; 1 }
        fn count<T>(n: int, x: T) -> int where nothing {
            if n == 0 {
                0
            } else {
                count(n - 1, x)
            }
        }
        fn kept<T>(x: T) -> int where T: Value { 0 }
    "# };
    assert_val_eq!(
        TestSession::new().run(&format!(
            "{src}(id(1), len_of([1, 2]), field({{ a: 3 }}), ascribed({{ a: true }}), count(2, 1), kept(1))"
        )),
        expected_tuple([int(1), int(2), int(3), int(1), int(0), int(0)])
    );
    for (name, published) in [
        ("id", "fn id<T>(x: T) -> T where T: Value"),
        ("len_of", "fn len_of<A>(a: [A]) -> int"),
        ("count", "fn count<T>(n: int, x: T) -> int"),
        // A written `Value` is published even if unused.
        ("kept", "fn kept<T>(x: T) -> int where T: Value"),
    ] {
        assert_eq!(
            signature(&mut TestSession::new(), src, name).trim_end(),
            published
        );
    }
    for name in ["field", "ascribed"] {
        assert!(
            signature(&mut TestSession::new(), src, name).contains("B: Value"),
            "{name} publishes the `Value` of the field's type"
        );
    }
    // A `Value` that a recursive sibling uses is published by its caller too.
    let src = indoc! { r#"
        fn even<T>(n: int, x: T) -> [T] where nothing {
            if n == 0 {
                []
            } else {
                odd(n - 1, x)
            }
        }
        fn odd<T>(n: int, x: T) -> [T] where nothing {
            if n == 0 {
                [x]
            } else {
                even(n - 1, x)
            }
        }
    "# };
    assert_val_eq!(
        TestSession::new().run(&format!("{src}even(3, 7)[0]")),
        int(7)
    );
    for name in ["even", "odd"] {
        assert_eq!(
            signature(&mut TestSession::new(), src, name).trim_end(),
            format!("fn {name}<T>(n: int, x: T) -> [T] where T: Value")
        );
    }
    // A variable that reaches neither the signature nor a requirement stays ambiguous.
    TestSession::new()
        .fail_compilation("fn f<T>(x: T) -> bool where nothing { let a = []; a == a }")
        .expect_unbound_ty_var();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_inferred_output_has_an_implicit_value() {
    let src = format!(
        "{CONTAINER}fn f<T>(x: T) -> string where T: Source<Item = _> {{ to_string(source(x)) }}\n"
    );
    assert_val_eq!(
        TestSession::new().run(&format!("{src}f(S(5))")),
        string("5")
    );
    assert_eq!(
        signature(&mut TestSession::new(), &src, "f"),
        "fn f<T, B>(x: T) -> string where T: Source <Item = B>, B: Value"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_partial_clause_keeps_inferring() {
    for (clause, requirements) in [
        ("where T: Value, ..", "T: Num + Value"),
        ("where ..", "T: Num"),
    ] {
        let src = format!("fn twice<T>(x: T) -> T {clause} {{ x + x }}\n");
        assert_val_eq!(TestSession::new().run(&format!("{src}twice(2)")), int(4));
        assert_eq!(
            signature(&mut TestSession::new(), &src, "twice"),
            format!("fn twice<T>(x: T) -> T where {requirements}")
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_complete_clause_does_not_narrow_an_independent_generic() {
    // Only `int` has a `Shape`: selecting it would narrow `T`.
    TestSession::new()
        .fail_compilation(indoc! { r#"
            trait Shape<Self> { fn sides(x: Self) -> int; }
            impl Shape for int { fn sides(x: int) -> int { 4 } }
            fn total<T>(x: T) -> int where T: Value { sides(x) }
        "# })
        .expect_undeclared_requirement("T: Shape", false);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_function_of_the_module_may_write_a_private_requirement() {
    assert_val_eq!(
        TestSession::new().run(indoc! { r#"
            trait Hidden<Self> { fn hidden(x: Self) -> int; }
            impl Hidden for int { fn hidden(x: int) -> int { x + 1 } }
            struct W<T>(T)
            trait Use<Self> { fn use_it(x: Self) -> int; }
            impl<T> Use for W<T> where T: Hidden, T: Value { fn use_it(x: W<T>) -> int { hidden(x.0) } }
            fn through<T>(x: T) -> int where T: Hidden, T: Value { use_it(W(x)) }
            through(2)
        "# }),
        int(3)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_complete_impl_solves_what_it_does_not_write() {
    let src = format!(
        "{RENDER}pub trait Describe<Self> {{ fn describe(x: Self) -> string; }}
        pub struct Box<T>(Bag<T>)
        impl<T> Describe for Box<T> where T: Display, T: Value {{
            fn describe(x: Box<T>) -> string {{ render(x.0) }}
        }}\n"
    );
    assert_val_eq!(
        TestSession::new().run(&format!("{src}describe(Box(Bag(1)))")),
        string("i")
    );
    TestSession::new()
        .fail_compilation(&format!(
            "{RENDER}pub trait Describe<Self> {{ fn describe(x: Self) -> string; }}
            pub struct Box<T>(Bag<T>)
            impl<T> Describe for Box<T> where T: Value {{
                fn describe(x: Box<T>) -> string {{ render(x.0) }}
            }}"
        ))
        .expect_undeclared_requirement("T: Display", false);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_complete_function_of_a_group_gives_its_siblings_its_contract() {
    // `f` solves `Bag<T>: Render`; `g`, which needs it too, publishes it, in either order.
    let f = "fn f<T>(x: Bag<T>, n: int) -> string where T: Display, T: Value {
        if n == 0 { render(x) } else { g(x, n - 1) }
    }\n";
    let g = "fn g(x, n) {
        if n == 0 { render(x) } else { f(x, n - 1) }
    }\n";
    for src in [format!("{RENDER}{f}{g}"), format!("{RENDER}{g}{f}")] {
        assert_val_eq!(
            TestSession::new().run(&format!("{src}(f(Bag(1), 1), g(Bag(1), 1))")),
            expected_tuple([string("i"), string("i")])
        );
        assert_eq!(
            signature(&mut TestSession::new(), &src, "f"),
            "fn f<T>(x: Bag<T>, n: int) -> string where T: Display + Value"
        );
        assert_eq!(
            signature(&mut TestSession::new(), &src, "g"),
            "fn g<A>(x: Bag<A>, n: int) -> string where A: Display + Value, Bag<A>: Render"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_structural_requirement_of_a_complete_function_reaches_its_group() {
    let src = indoc! { r#"
        fn f<T>(x: T, n: int) -> int where nothing {
            if n == 0 { x.a } else { g(x, n - 1) }
        }
        fn g(x, n) {
            if n == 0 { 0 } else { f(x, n - 1) }
        }
    "# };
    assert_val_eq!(
        TestSession::new().run(&format!("{src}(g({{ a: 4 }}, 1), g({{ a: 4 }}, 2))")),
        expected_tuple([int(4), int(0)])
    );
    assert!(
        signature(&mut TestSession::new(), src, "g").contains("where A: { a: int"),
        "the field requirement of `f` is one of `g`"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_sibling_cannot_widen_a_complete_contract() {
    // `g` needs `Num` of what `f` passes it, which `f` does not write.
    TestSession::new()
        .fail_compilation(indoc! { r#"
            fn f<T>(x: T, n: int) -> T where T: Value {
                if n == 0 { x } else { g(x, n - 1) }
            }
            fn g(x, n) {
                if n == 0 { x + x } else { f(x, n - 1) }
            }
        "# })
        .expect_undeclared_requirement("T: Num", false);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_hole_in_an_output_is_inferred() {
    let src = indoc! { r#"
        fn first<S, I>(s: S) -> int where S: Seq<Item = _, Iter = I>, S: Value, I: Value {
            let mut it = iter(s);
            match next(it) { Some(x) => x, None => 0 }
        }
    "# };
    assert_val_eq!(TestSession::new().run(&format!("{src}first([5])")), int(5));
    assert!(
        signature(&mut TestSession::new(), src, "first").contains("S: Seq <Item = int,"),
        "the published requirement shows the inferred item"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_omitted_output_suggests_a_hole_where_one_is_allowed() {
    let error =
        TestSession::new().fail_compilation("fn f<S>(s: S) -> int where S: Seq<Iter = _> { 0 }");
    assert!(
        matches!(
            &*error,
            CompilationErrorImpl::InvalidTraitConstraint {
                kind: InvalidTraitConstraintKind::MissingOutputBindings {
                    holes_allowed: true,
                    ..
                },
                ..
            }
        ),
        "{error:?}"
    );
    let error = TestSession::new()
        .fail_compilation("struct W<S> where S: Seq<Item = int, Iter = _> (S)\n1");
    assert!(
        matches!(
            &*error,
            CompilationErrorImpl::InvalidTraitConstraint {
                kind: InvalidTraitConstraintKind::HoleNotAllowed,
                ..
            }
        ),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_written_ground_requirement_is_checked_and_not_published() {
    let src = "fn f() -> int where int: Num { 1 }\n";
    assert_val_eq!(TestSession::new().run(&format!("{src}f()")), int(1));
    assert_eq!(
        signature(&mut TestSession::new(), src, "f"),
        "fn f() -> int"
    );
    TestSession::new()
        .fail_compilation("fn g() -> int where string: Num { 1 }")
        .expect_trait_impl_not_found("Num", &["Self = string"]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_literal_beside_a_generic_value_defaults_under_a_complete_clause() {
    // The `Value` of the tuple, or of the struct, holds whenever those of its elements do, so it
    // does not tie the literal's type to `T`: that type defaults, and `T` stays generic.
    let src = indoc! { r#"
        struct W<A, B>(A, B)
        fn first<T>(x: T) -> T where nothing { let p = (x, 1); p.0 }
        fn wrapped<T>(x: T) -> T where nothing { let p = W(x, 1.5); p.0 }
        fn second<T>(x: T) -> int where nothing { let p = (x, 1); p.1 + 2 }
        fn sum<T>(x: T) -> T where T: Num { let p = (x, 1); x + p.0 }
    "# };
    assert_eq!(
        signature(&mut TestSession::new(), src, "first"),
        "fn first<T>(x: T) -> T where T: Value"
    );
    assert_eq!(
        signature(&mut TestSession::new(), src, "sum"),
        "fn sum<T>(x: T) -> T where T: Num + Value"
    );
    assert_val_eq!(
        TestSession::new().run(&format!(
            "{src}(first(true), wrapped(\"a\"), second(true), sum(2.5))"
        )),
        expected_tuple([bool(true), string("a"), int(3), float(5.0)])
    );
}
