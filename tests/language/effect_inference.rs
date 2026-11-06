// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Soundness and precision of inferred effects: callback effects reaching their callers through
//! trait outputs, joins, declared effect variables and generalization.

use test_log::test;

use indoc::indoc;
use ustr::ustr;

use crate::harness::{TestSession, int, string};
use ferlium::{
    compiler::error::{CompilationErrorImpl, ImplEffectRestriction, SourceFailureKind},
    format::FormatWith,
    types::effects::*,
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

/// Renders the published signature of function `name` of the module compiled from `src`.
fn signature(session: &mut TestSession, src: &str, name: &str) -> String {
    let module_id = session.compile(src).module_id;
    let compiler_session = session.session();
    let module = compiler_session.expect_fresh_module(module_id);
    let rendered = module.format_with(&compiler_session.modules()).to_string();
    let with_generics = format!("fn {name}<");
    let without_generics = format!("fn {name}(");
    let line = rendered
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with(&with_generics) || line.starts_with(&without_generics))
        .unwrap_or_else(|| panic!("no function {name} in module:\n{rendered}"));
    match line.rfind(" (#") {
        Some(index) => line[..index].to_string(),
        None => line.to_string(),
    }
}

fn fn_effects(session: &mut TestSession, src: &str, name: &str) -> EffType {
    let module = session.compile_and_get_module(src);
    module
        .get_function(ustr(name))
        .unwrap()
        .definition
        .ty_scheme
        .ty()
        .effects
        .clone()
}

const COMPOSE: &str = "fn compose(f, g) { |x| g(f(x)) }\n";

// Callback failures through iterator adaptors

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn eager_filter_callback_failure_propagates() {
    let mut session = TestSession::new();
    assert_eq!(
        session.fail_run("fn f(d) { [1, 2] |> filter(|x| idiv(x, d) > 0) }\nf(0)"),
        SourceFailureKind::DivisionByZero
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn eager_filter_callback_failure_propagates_through_generic_caller() {
    let mut session = TestSession::new();
    assert_eq!(
        session.fail_run("fn g(p) { [1, 2] |> filter(p) }\ng(|x| idiv(x, 0) > 0)"),
        SourceFailureKind::DivisionByZero
    );
    assert_eq!(
        session.fail_run(indoc! { r#"
            fn k(p) {
                let a: [int] = [1, 2];
                a |> filter(p)
            }
            k(|x| idiv(x, 0) > 0)
        "# }),
        SourceFailureKind::DivisionByZero
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn pure_and_fallible_uses_of_one_dictionary_input_stay_apart() {
    let mut session = TestSession::new();
    for src in [
        "fn a() { [1, 2] |> map(|x| x) }\nfn b(d) { [1, 2] |> map(|x| idiv(x, d)) }\n(a(), b(0))",
        "fn b(d) { [1, 2] |> map(|x| idiv(x, d)) }\nfn a() { [1, 2] |> map(|x| x) }\n(b(0), a())",
    ] {
        assert_eq!(session.fail_run(src), SourceFailureKind::DivisionByZero);
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn open_dictionaries_keep_their_callers_effects() {
    let mut session = TestSession::new();
    for src in [
        "fn g(a: [int], f) { a |> map(f) }\ng([1, 2], |x| idiv(x, 0))",
        "fn g(a: [int], f) { iter(a) |> map(f) |> count() }\ng([1, 2], |x| idiv(x, 0))",
        "fn g(a: [int], f) { a |> filter(f) }\ng([1, 2], |x| idiv(x, 0) > 0)",
        "fn g(f) { let m = map; m([1, 2], f) }\ng(|x| idiv(x, 0))",
        "fn c<! e>(it: FilterIterator<ArrayIterator<int>, int ! e>) -> int { count(it) }\nc(iter([1, 2]) |> filter(|x| idiv(x, 0) > 0))",
        "fn h(f) { let n = next; let mut it = iter([1, 2]) |> map(f); n(it) }\nh(|x| idiv(x, 0))",
        "fn z(f, g) { zip(iter([1]) |> map(f), iter([2]) |> map(g)) |> count() }\nz(|x| x, |x| idiv(x, 0))",
    ] {
        assert_eq!(session.fail_run(src), SourceFailureKind::DivisionByZero);
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn eager_map_callback_failure_propagates() {
    let mut session = TestSession::new();
    assert_eq!(
        session.fail_run("fn f(d) { [1, 2] |> map(|x| idiv(x, d)) }\nf(0)"),
        SourceFailureKind::DivisionByZero
    );
    assert_eq!(
        session.fail_run("[1, 2] |> map(|x| idiv(x, 0))"),
        SourceFailureKind::DivisionByZero
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn impl_declaring_pure_callback_effect_rejects_fallible_callback() {
    let mut session = TestSession::new();
    let error = session.fail_compilation(indoc! { r#"
        trait Apply<Self |-> ! CallbackEffect> {
            fn apply(value: Self, f: (int) -> int ! CallbackEffect) -> int;
        }
        struct Box { v: int }
        impl Apply for <Self = Box |-> ! CallbackEffect = ()> {
            fn apply(value, f) {
                f(value.v)
            }
        }
        Apply::apply(Box { v: 1 }, |x| idiv(x, 0))
    "# });
    let CompilationErrorImpl::TraitImplOutputEffectsMismatch { mismatches, .. } =
        error.into_inner()
    else {
        panic!("expected an output effects mismatch");
    };
    let [(name, declared, requested)] = mismatches.as_slice() else {
        panic!("expected one mismatch, got {mismatches:?}");
    };
    assert_eq!(name.as_str(), "CallbackEffect");
    assert_eq!(*declared, no_effects());
    assert!(requested.contains(Effect::Primitive(PrimitiveEffect::Fallible)));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn filter_callback_effect_reaches_caller() {
    let mut session = TestSession::new();
    let src = indoc! { r#"
        fn eager(a: [int], q: (int) -> bool ! read) { a |> filter(q) }
        fn lazy(a: [int], q: (int) -> bool ! read) { iter(a) |> filter(q) |> count() }
        fn generic(a: [int], p) { a |> filter(p) }
        fn count_declared<! e>(it: FilterIterator<ArrayIterator<int>, int ! e>) -> int { count(it) }
        fn lazy_map(a: [int]) -> int { iter(a) |> map(|x| idiv(x, 2)) |> count() }
    "# };
    assert_eq!(
        signature(&mut session, src, "eager"),
        "fn eager(a: [int], q: (int) -> bool ! read) -> [int] ! (read, fallible)"
    );
    assert_eq!(
        fn_effects(&mut session, src, "lazy"),
        effects(&[PrimitiveEffect::Fallible, PrimitiveEffect::Read])
    );
    assert_eq!(
        fn_effects(&mut session, src, "lazy_map"),
        effect(PrimitiveEffect::Fallible)
    );
    assert_eq!(
        signature(&mut session, src, "count_declared"),
        "fn count_declared<! e>(it: FilterIterator<ArrayIterator<int>, int ! e>) -> int ! (fallible, e)"
    );
    assert_eq!(
        signature(&mut session, src, "generic"),
        "fn generic<! e₀>(a: [int], p: (int) -> bool ! e₀) -> [int] ! (fallible, e₀)"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn collect_effect_reaches_caller() {
    let mut session = TestSession::new();
    let src = indoc! { r#"
        fn ce(a) { (iter(a) |> collect(): [int]) }
        fn use_ce() { ce([1]) }
        fn ce_concrete(a: [int]) { (iter(a) |> collect(): [int]) }
    "# };
    assert_eq!(
        fn_effects(&mut session, src, "ce_concrete"),
        effect(PrimitiveEffect::Fallible)
    );
    assert_eq!(
        fn_effects(&mut session, src, "use_ce"),
        effect(PrimitiveEffect::Fallible)
    );
}

// Generalization

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn callback_upper_bound_is_published() {
    let mut session = TestSession::new();
    let src = indoc! { r#"
        fn apply_f(f: (int) -> int ! fallible) -> int { f(1) }
        fn h(q) { (apply_f(|x| q(x)), q) }
    "# };
    assert_eq!(
        signature(&mut session, src, "h"),
        "fn h(q: (int) -> int ! fallible) -> (int, (int) -> int ! fallible) ! fallible"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn composed_callbacks_share_one_effect_variable() {
    let mut session = TestSession::new();
    assert_eq!(
        signature(&mut session, COMPOSE, "compose"),
        "fn compose<A, B, C ! e₀>(f: (A) -> B ! e₀, g: (B) -> C ! e₀) -> (A) -> C ! e₀ where B: Value"
    );
    // Callers keep their callbacks' effects separate.
    let src = format!(
        "{COMPOSE}fn r() {{ effects::read() }}\nfn use_compose() {{ compose(|x| x, |x| {{ r(); x }})(1) }}"
    );
    assert_eq!(
        fn_effects(&mut session, &src, "use_compose"),
        effect(PrimitiveEffect::Read)
    );
}

// Joins

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fallible_join_does_not_make_callbacks_fallible() {
    let mut session = TestSession::new();
    let src = format!(
        "{COMPOSE}{}",
        indoc! { r#"
            fn pick(c, f, g) {
                if c {
                    compose(f, g)
                } else {
                    |x| idiv(x, 0)
                }
            }
            fn elements(f, g) { [compose(f, g), |x| idiv(x, 0)] }
        "# }
    );
    assert_eq!(
        signature(&mut session, &src, "pick"),
        "fn pick<A, B ! e₀>(c: A, f: (int) -> B ! e₀, g: (B) -> int ! e₀) -> (int) -> int ! (fallible, e₀) where B: Value, A ⇝ bool"
    );
    assert_eq!(
        signature(&mut session, &src, "elements"),
        "fn elements<A ! e₀>(f: (int) -> A ! e₀, g: (A) -> int ! e₀) -> [(int) -> int ! (fallible, e₀)] where A: Value"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn pure_join_does_not_make_callbacks_pure() {
    let mut session = TestSession::new();
    let src = format!(
        "{COMPOSE}{}",
        indoc! { r#"
            fn pick(c, f, g) {
                if c {
                    compose(f, g)
                } else {
                    |x| x
                }
            }
        "# }
    );
    assert_eq!(
        signature(&mut session, &src, "pick"),
        "fn pick<A, B, C ! e₀>(c: A, f: (B) -> C ! e₀, g: (C) -> B ! e₀) -> (B) -> B ! e₀ where B: Value, C: Value, A ⇝ bool"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_loop_and_mutable_local_joins_keep_callbacks_apart() {
    let mut session = TestSession::new();
    let src = indoc! { r#"
        fn a(f) { [f, |x| idiv(x, 0)] }
        fn l(c: bool, f) {
            loop {
                if c {
                    break f
                } else {
                    break |x| idiv(x, 0)
                }
            }
        }
        fn m(f) { let mut g = f; g = |x| idiv(x, 0); g }
    "# };
    assert_eq!(
        signature(&mut session, src, "a"),
        "fn a<! e₀>(f: (int) -> int ! e₀) -> [(int) -> int ! (fallible, e₀)]"
    );
    assert_eq!(
        signature(&mut session, src, "l"),
        "fn l<! e₀>(c: bool, f: (int) -> int ! e₀) -> (int) -> int ! (fallible, e₀)"
    );
    assert_eq!(
        signature(&mut session, src, "m"),
        "fn m<! e₀>(f: (int) -> int ! e₀) -> (int) -> int ! (fallible, e₀)"
    );
}

// Upper bounds

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn upper_bounds_on_one_callback_intersect() {
    let mut session = TestSession::new();
    let src = indoc! { r#"
        fn use_fw(f: () -> int ! (fallible, write)) -> int { f() }
        fn use_fr(f: () -> int ! (fallible, read)) -> int { f() }
        fn both(q) { use_fw(|| q()) + use_fr(|| q()) }
    "# };
    assert_eq!(
        signature(&mut session, src, "both"),
        "fn both(q: () -> int ! fallible) -> int ! (read, write, fallible)"
    );
}

// Declared effect variables

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn declared_effect_variable_is_not_widened() {
    let mut session = TestSession::new();
    let src = indoc! { r#"
        fn g<! v>(f: (int) -> int ! (fallible, v)) -> int { f(1) }
        fn s1<! e>(p: (int) -> int ! e) -> int { g(p) }
    "# };
    assert_eq!(
        signature(&mut session, src, "s1"),
        "fn s1<! e>(p: (int) -> int ! e) -> int ! (fallible, e)"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn declared_effect_variable_is_not_specialized() {
    let mut session = TestSession::new();
    session.fail_compilation(indoc! { r#"
        fn apply_f(f: (int) -> int ! fallible) -> int { f(1) }
        fn s2<! e>(p: (int) -> int ! e) -> int { apply_f(p) }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effect_row_with_two_declared_variables_is_rejected() {
    let mut session = TestSession::new();
    session.fail_compilation("fn d<! e0, e1>(p: (int) -> int ! (e0, e1)) -> int { p(1) }");
    session.fail_compilation(
        "fn both<! A, B>(f: () -> int ! A, g: () -> int ! B) -> int { f() + g() }",
    );
    let src = "fn both<! E>(f: () -> int ! E, g: () -> int ! E) -> int { f() + g() }";
    assert_eq!(
        signature(&mut session, src, "both"),
        "fn both<! E>(f: () -> int ! E, g: () -> int ! E) -> int ! E"
    );
}

// Impl methods against trait methods

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn impl_method_accepting_narrower_callback_is_rejected() {
    let mut session = TestSession::new();
    session.fail_compilation(indoc! { r#"
        trait Run<Self> {
            fn run(x: Self, f: (int) -> int ! fallible) -> int;
        }
        struct S;
        impl Run for S {
            fn run(x: S, f: (int) -> int) -> int {
                f(1)
            }
        }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_dictionary_for_pure_callbacks_does_not_serve_a_generic_one() {
    let mut session = TestSession::new();
    assert_eq!(
        session.fail_run(indoc! { r#"
            fn generic<! E>(a: [int], f: (int) -> int ! E) { a |> map(f) }
            fn pure(a: [int]) { a |> map(|x| x) }
            (pure([1]), generic([1], |x| idiv(x, 0)))
        "# }),
        SourceFailureKind::DivisionByZero
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn impl_method_mutable_argument_types_are_invariant() {
    let mut session = TestSession::new();
    session.fail_compilation(indoc! { r#"
        trait Replace<Self> { fn replace(s: Self, x: &mut (() -> int)); }
        struct S;
        impl Replace {
            fn replace(s: S, x: &mut (() -> int ! fallible)) {
                x = || idiv(1, 0);
            }
        }
        let mut f: () -> int = || 1;
        Replace::replace(S, f);
        f()
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn concrete_impl_method_may_accept_wider_callbacks() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            trait Ignore<Self> { fn ignore(s: Self, f: () -> int) -> int; }
            struct S;
            impl Ignore for S {
                fn ignore(s: S, f: () -> int ! fallible) -> int { 7 }
            }
            fn use_it<T>(x: T) -> int where T: Ignore { ignore(x, || 3) }
            ignore(S, || 2) + use_it(S)
        "# }),
        int(14)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn nested_selection_relates_callback_effects_by_polarity() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            trait Ignore<Self |-> ! E> { fn ignore(s: Self, f: () -> int ! E) -> int; }
            trait Outer<Self> { fn outer(s: Self) -> int; }
            struct Base;
            struct Wrap<T>(T)
            impl Ignore for <Self = Base |-> ! E = fallible> {
                fn ignore(s: Base, f: () -> int ! fallible) -> int { 1 }
            }
            impl<T> Outer for <Self = Wrap<T>>
            where T: Ignore<! E = ()> {
                fn outer(s: Wrap<T>) -> int { ignore(s.0, || 2) }
            }
            outer(Wrap(Base))
        "# }),
        int(1)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn nested_selection_rejects_an_impl_accepting_fewer_callbacks() {
    let mut session = TestSession::new();
    session.fail_compilation(indoc! { r#"
        trait Ignore<Self |-> ! E> { fn ignore(s: Self, f: () -> int ! E) -> int; }
        trait Outer<Self> { fn outer(s: Self) -> int; }
        struct Base;
        struct Wrap<T>(T)
        impl Ignore for <Self = Base |-> ! E = ()> {
            fn ignore(s: Base, f: () -> int) -> int { 1 }
        }
        impl<T> Outer for <Self = Wrap<T>>
        where T: Ignore<! E = fallible> {
            fn outer(s: Wrap<T>) -> int { ignore(s.0, || 2) }
        }
        outer(Wrap(Base))
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn impl_method_callback_parameter_without_effects_compiles() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            trait Ignore<Self |-> ! E> { fn ignore(s: Self, f: () -> int ! E) -> int; }
            struct Base;
            impl Ignore for <Self = Base |-> ! E = ()> {
                fn ignore(s: Base, f: () -> int) -> int { f() }
            }
            ignore(Base, || 1)
        "# }),
        int(1)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mutable_argument_types_are_invariant_in_nested_function_types() {
    let mut session = TestSession::new();
    session.fail_compilation(indoc! { r#"
        fn overwrite(x: &mut (() -> int ! fallible)) {
            x = || idiv(1, 0);
        }
        trait Make<Self> {
            fn make(s: Self) -> (&mut (() -> int)) -> ();
        }
        struct S;
        impl Make for S {
            fn make(s: S) -> (&mut (() -> int ! fallible)) -> () {
                overwrite
            }
        }
        let write = Make::make(S);
        let mut f: () -> int = || 1;
        write(f);
        f()
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_type_parameters_preserve_callback_effect_requirements() {
    let mut session = TestSession::new();
    let error = session
        .try_compile(indoc! { r#"
        type Pure = () -> int;
        type Fallible = () -> int ! fallible;
        struct Consumer<T> { consume: (T) -> int }
        fn coerce(c: Consumer<Pure>) -> Consumer<Fallible> { c }
        fn pure_call(f: Pure) -> int { f() }
        fn bad() -> int {
            let d = coerce(Consumer { consume: pure_call });
            (d.consume)(|| idiv(1, 0))
        }
    "# })
        .expect_err("a consumer of pure callbacks cannot accept fallible callbacks");
    error.expect_invalid_effect_dependency(effect(PrimitiveEffect::Fallible), no_effects());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_type_parameters_preserve_nested_callback_effect_requirements() {
    let mut session = TestSession::new();
    let error = session
        .try_compile(indoc! { r#"
        type Pure = () -> int;
        type Fallible = () -> int ! fallible;
        struct Consumer<T> { consume: (T) -> int }
        fn coerce(c: Consumer<(Fallible) -> int>) -> Consumer<(Pure) -> int> { c }
    "# })
        .expect_err("nested callback effects must remain invariant in named types");
    error.expect_invalid_effect_dependency(effect(PrimitiveEffect::Fallible), no_effects());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_type_parameters_preserve_effect_polymorphism() {
    let mut session = TestSession::new();
    let src = indoc! { r#"
        struct Box<T>(T)
        fn identity<T>(x: Box<T>) -> Box<T> { x }
        fn apply<! E>(x: Box<(() -> int ! E)>) -> int { (identity(x).0)() }
    "# };
    assert_val_eq!(session.run(&format!("{src}\napply(Box(|| 7))")), int(7));
    assert_eq!(
        session.fail_run(&format!("{src}\napply(Box(|| idiv(1, 0)))")),
        SourceFailureKind::DivisionByZero,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effect_after_type_arguments_is_an_argument_of_the_outer_type() {
    let error = TestSession::new().fail_compilation(
        "struct Box<T>(T)
        fn f<! E>(g: Box<() -> int ! E>) -> int { 1 }",
    );
    let CompilationErrorImpl::WrongNumberOfEffectArguments {
        type_name,
        expected: 0,
        got: 1,
        function_type_span: Some(_),
        ..
    } = &*error
    else {
        panic!("unexpected diagnostic: {error:?}")
    };
    assert_eq!(*type_name, ustr("Box"));
    // No function type to give the effect to, so no hint.
    let error = TestSession::new().fail_compilation(
        "struct Box<T>(T)
        fn f<! E>(g: Box<int ! E>) -> int { 1 }",
    );
    assert!(
        matches!(
            &*error,
            CompilationErrorImpl::WrongNumberOfEffectArguments {
                function_type_span: None,
                ..
            }
        ),
        "{error:?}"
    );
    // The parentheses keep the effect on the function.
    assert_val_eq!(
        TestSession::new().run(
            "struct Box<T>(T)
            fn f<! E>(g: Box<(() -> int ! E)>) -> int { g.0() }
            f(Box(|| 3))"
        ),
        int(3)
    );
    // Wrapping these in parentheses would not parse, so no hint.
    for parenthesized in [
        "(() -> int) ! E",
        "((() -> int)) ! E",
        "(() -> int ! E) ! E",
    ] {
        let error = TestSession::new().fail_compilation(&format!(
            "struct Box<T>(T)
            fn f<! E>(g: Box<{parenthesized}>) -> int {{ 1 }}"
        ));
        assert!(
            matches!(
                &*error,
                CompilationErrorImpl::WrongNumberOfEffectArguments {
                    function_type_span: None,
                    ..
                }
            ),
            "{parenthesized}: {error:?}"
        );
    }
    // The hint is the argument in parentheses, which must compile.
    for function_type in ["() -> int ! E", "() -> (int) ! E", "() -> () -> int ! E"] {
        let error = TestSession::new().fail_compilation(&format!(
            "struct Box<T>(T)
            fn f<! E>(g: Box<{function_type}>) -> int {{ 1 }}"
        ));
        assert!(
            matches!(
                &*error,
                CompilationErrorImpl::WrongNumberOfEffectArguments {
                    function_type_span: Some(_),
                    ..
                }
            ),
            "{function_type}: {error:?}"
        );
        TestSession::new().compile(&format!(
            "struct Box<T>(T)
            fn f<! E>(g: Box<({function_type})>) -> int {{ 1 }}"
        ));
    }
}

const CALL_THROUGH_TRAIT: &str = indoc! { r#"
    trait Run<Self |-> ! E> {
        fn run(x: Self) -> int ! E;
    }
    struct Cb<! F>(() -> int ! F)
    impl<! F> Run for <Self = Cb<! F> |-> ! E = F> {
        fn run(x: Cb<! F>) -> int {
            (x.0)()
        }
    }
"# };

/// A serializer that calls its callback, relying on a prerequisite for that call to be pure.
const PURE_RUN_SERIALIZER: &str = indoc! { r#"
    struct Wrap<T>(T)
    impl<T> Serialize for Wrap<T>
    where T: Run<! E = ()> {
        fn serialize(x: Wrap<T>) -> DataValue {
            serialize(run(x.0))
        }
    }
"# };

fn expect_input_restriction(source: &str, expected: ImplEffectRestriction) {
    let error = TestSession::new().fail_compilation(source);
    let CompilationErrorImpl::TraitImplInputRestrictsEffect { restriction, .. } = &*error else {
        panic!("unexpected diagnostic for {source}: {error:?}")
    };
    assert_eq!(*restriction, expected, "{source}");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn impl_inputs_cannot_fix_effects() {
    let prelude = "struct Box<T>(T)
        type Pure = () -> int ! ();
        type Failing = () -> int ! fallible;
        trait Pick<Self> { fn pick(x: Self) -> int; }\n";
    for imp in [
        // Also through aliases, nested, and left unwritten.
        "impl Pick for Box<Pure> { fn pick(x: Box<Pure>) -> int { 1 } }",
        "impl Pick for Box<Failing> { fn pick(x: Box<Failing>) -> int { 2 } }",
        "impl<T> Pick for Box<(T, Pure)> where T: Value { fn pick(x: Box<(T, Pure)>) -> int { 1 } }",
        "impl Pick for Box<() -> int> { fn pick(x: Box<() -> int>) -> int { 1 } }",
    ] {
        expect_input_restriction(
            &format!("{prelude}{imp}"),
            ImplEffectRestriction::FixedInInput,
        );
    }
    expect_input_restriction(
        "struct Two<A, B>(A, B)
        trait Tr<Self> { fn go(x: Self) -> int; }
        impl<! E> Tr for Two<(() -> int ! E), (() -> int ! E)> {
            fn go(x: Two<(() -> int ! E), (() -> int ! E)>) -> int { 1 }
        }",
        ImplEffectRestriction::RepeatedInInput,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn every_function_form_selects_the_effect_polymorphic_impl() {
    assert_val_eq!(
        TestSession::new().run(&format!(
            "{CALL_THROUGH_TRAIT}
            fn f(g) {{ run(Cb(g)) }}
            fn h<! E>(g: () -> int ! E) -> int {{ run(Cb(g)) }}
            fn k(g: () -> int) -> int {{ run(Cb(g)) }}
            f(|| 1) + h(|| 2) + k(|| 3) + f(|| idiv(4, 2)) + h(|| idiv(4, 2)) + k(|| idiv(4, 2))"
        )),
        int(12)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_repeated_type_variable_equates_the_effects_of_the_caller() {
    let prelude = format!(
        "{CALL_THROUGH_TRAIT}
        trait Tr<Self |-> ! E> {{ fn go(x: Self) -> int ! E; }}
        struct Pair<A, B>(A, B)
        impl<T ! F> Tr for <Self = Pair<T, T> |-> ! E = F>
        where T: Run<! E = F> {{
            fn go(x: Pair<T, T>) -> int {{ run(x.0) + run(x.1) }}
        }}"
    );
    // Written generics stay distinct.
    TestSession::new().fail_compilation(&format!(
        "{prelude}
        fn f<! A, B>(a: () -> int ! A, b: () -> int ! B) -> int {{ go(Pair(Cb(a), Cb(b))) }}"
    ));
    // Inferred effects are merged, so the failure of either callback is visible in the caller.
    assert_val_eq!(
        TestSession::new().run(&format!(
            "{prelude}
            fn f(a, b) {{ go(Pair(Cb(a), Cb(b))) }}
            f(|| 1, || idiv(4, 2))"
        )),
        int(3)
    );
    assert_val_eq!(
        TestSession::new().run(&format!("{prelude}\ngo(Pair(Cb(|| 1), Cb(|| idiv(4, 2))))")),
        int(3)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn derivation_checks_prerequisites_with_the_real_effects() {
    let prelude = format!("{CALL_THROUGH_TRAIT}{PURE_RUN_SERIALIZER}");
    for (generic, value) in [
        // Through derivation, for a tuple and for a record.
        ("(Wrap(Cb(g)),)", "(Wrap(Cb(|| 3)),)"),
        ("{ a: Wrap(Cb(g)) }", "{ a: Wrap(Cb(|| 3)) }"),
    ] {
        TestSession::new().fail_compilation(&format!(
            "{prelude}
            fn f<! E>(g: () -> int ! E) -> DataValue {{ serialize({generic}) }}"
        ));
        // Also when a pure use already derived the impl that the erased effects would find.
        TestSession::new().fail_compilation(&format!(
            "{prelude}
            fn pure() -> DataValue {{ serialize({value}) }}
            fn f<! E>(g: () -> int ! E) -> DataValue {{ serialize({generic}) }}"
        ));
        // An unwritten effect is held to the prerequisite instead.
        TestSession::new().fail_compilation(&format!(
            "{prelude}
            fn f(g) {{ serialize({generic}) }}
            f(|| idiv(1, 0))"
        ));
        TestSession::new().run(&format!(
            "{prelude}
            fn f(g) {{ serialize({generic}) }}
            f(|| 3)"
        ));
        TestSession::new().run(&format!("{prelude}\nserialize({value})"));
    }
    // Through a source impl whose own prerequisite carries no visible effect.
    TestSession::new().fail_compilation(&format!(
        "{prelude}
        struct Outer<T>(T)
        impl<T> Serialize for Outer<T> where T: Serialize {{
            fn serialize(x: Outer<T>) -> DataValue {{ serialize(x.0) }}
        }}
        fn f<! E>(g: () -> int ! E) -> DataValue {{ serialize(Outer(Wrap(Cb(g)))) }}"
    ));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_failed_effect_requirement_is_an_error_not_an_absent_impl() {
    // Derivation could serve `Other` if the source impl did not count as selected.
    let error = TestSession::new().fail_compilation(&format!(
        "{CALL_THROUGH_TRAIT}
        struct Other<T>(T)
        impl<T> Serialize for Other<T> where T: Run<! E = ()> {{
            fn serialize(x: Other<T>) -> DataValue {{ serialize(1) }}
        }}
        impl<! F> Serialize for Cb<! F> {{
            fn serialize(x: Cb<! F>) -> DataValue {{ serialize(2) }}
        }}
        serialize(Other(Cb(|| idiv(1, 0))))"
    ));
    assert!(
        !matches!(&*error, CompilationErrorImpl::TraitImplNotFound { .. }),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_missing_impl_stays_an_error_when_a_member_has_one() {
    let error = TestSession::new().fail_compilation(indoc! { r#"
struct Cb<! E>(() -> int ! E)
struct Outer<T>(T)
trait Get<Self |-> Out> { fn get(x: Self) -> Out; }
impl<! E> Get for <Self = Cb<! E> |-> Out = int> {
    fn get(x: Cb<! E>) -> int { 1 }
}
fn f<! E>(g: () -> int ! E) -> int { get(Outer(Cb(g))) }
f(|| 5)
"# });
    assert!(
        matches!(&*error, CompilationErrorImpl::TraitImplNotFound { .. }),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn selection_considers_the_whole_structure_before_effects() {
    for source in [
        indoc! { r#"
struct Cb<T>(T)
type Pure = () -> int ! ();
type Failing = () -> int ! fallible;
struct Pair<A, B>(A, B)
struct Mark<T>(T)
trait Select<Self, Other> { fn select(x: Self, y: Other) -> int; }
impl<T> Select for <Self = Pair<T, T>, Other = Mark<int>> where T: Value {
    fn select(x: Pair<T, T>, y: Mark<int>) -> int { 1 }
}
impl<A, B> Select for <Self = Pair<A, B>, Other = Mark<bool>> where A: Value, B: Value {
    fn select(x: Pair<A, B>, y: Mark<bool>) -> int { 2 }
}
let a: Cb<Pure> = Cb(|| 5);
let b: Cb<Failing> = Cb(|| idiv(4, 2));
select(Pair(a, b), Mark(true))
"# },
        indoc! { r#"
struct Cb<T>(T)
type Pure = () -> int ! ();
type Failing = () -> int ! fallible;
struct Pair<A, B>(A, B)
struct Mark<T>(T)
trait Select<Self, Other> { fn select(x: Self, y: Other) -> int; }
impl<A, B> Select for <Self = Pair<A, B>, Other = Mark<bool>> where A: Value, B: Value {
    fn select(x: Pair<A, B>, y: Mark<bool>) -> int { 2 }
}
impl<T> Select for <Self = Pair<T, T>, Other = Mark<int>> where T: Value {
    fn select(x: Pair<T, T>, y: Mark<int>) -> int { 1 }
}
let a: Cb<Pure> = Cb(|| 5);
let b: Cb<Failing> = Cb(|| idiv(4, 2));
select(Pair(a, b), Mark(true))
"# },
    ] {
        assert_val_eq!(TestSession::new().run(source), int(2));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_prerequisite_output_types_do_not_separate_impls() {
    for source in [
        indoc! { r#"
struct Cb<T>(T)
struct X<T>(T)
struct W<T>(T)
type Pure = () -> int ! ();
type Failing = () -> int ! fallible;
trait Source<Self |-> Item> { fn source(x: Self) -> Item; }
impl<! E> Source for <Self = X<(() -> int ! E)> |-> Item = Cb<(() -> int ! E)>> {
    fn source(x: X<(() -> int ! E)>) -> Cb<(() -> int ! E)> { Cb(x.0) }
}
trait R<Self> { fn r(x: Self) -> int; }
impl<T> R for W<T> where T: Value, X<T>: Source<Item = Cb<Pure>> {
    fn r(x: W<T>) -> int { 1 }
}
impl<T> R for W<T> where T: Value, X<T>: Source<Item = Cb<Failing>> {
    fn r(x: W<T>) -> int { 2 }
}
let pure: Pure = || 5;
let widened: Failing = || 5;
(r(W(pure)), r(W(widened)))
"# },
        indoc! { r#"
struct Cb<T>(T)
struct X<T>(T)
struct W<T>(T)
type Pure = () -> int ! ();
type Failing = () -> int ! fallible;
trait Source<Self |-> Item> { fn source(x: Self) -> Item; }
impl<! E> Source for <Self = X<(() -> int ! E)> |-> Item = Cb<(() -> int ! E)>> {
    fn source(x: X<(() -> int ! E)>) -> Cb<(() -> int ! E)> { Cb(x.0) }
}
trait R<Self> { fn r(x: Self) -> int; }
impl<T> R for W<T> where T: Value, X<T>: Source<Item = Cb<Failing>> {
    fn r(x: W<T>) -> int { 2 }
}
impl<T> R for W<T> where T: Value, X<T>: Source<Item = Cb<Pure>> {
    fn r(x: W<T>) -> int { 1 }
}
let pure: Pure = || 5;
let widened: Failing = || 5;
(r(W(pure)), r(W(widened)))
"# },
    ] {
        let error = TestSession::new().fail_compilation(source);
        assert!(
            matches!(
                &*error,
                CompilationErrorImpl::OverlappingTraitImpls {
                    effects_ignored: true,
                    ..
                }
            ),
            "{error:?}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_nested_effect_mismatch_does_not_fall_back_to_derivation() {
    let error = TestSession::new().fail_compilation(indoc! { r#"
struct Cb<! E>(() -> int ! E)
struct Out<T>(T)
struct W<T>(T)
type Pure = () -> int ! ();
trait Source<Self |-> Item> { fn source(x: Self) -> Item; }
impl<! E> Source for <Self = Cb<! E> |-> Item = Out<(() -> int ! E)>> {
    fn source(x: Cb<! E>) -> Out<(() -> int ! E)> { Out(x.0) }
}
impl<T> Serialize for W<T> where T: Value, T: Source<Item = Out<Pure>> {
    fn serialize(x: W<T>) -> DataValue { serialize(1) }
}
impl<! E> Serialize for Cb<! E> {
    fn serialize(x: Cb<! E>) -> DataValue { serialize(2) }
}
serialize(W(Cb(|| idiv(1, 0))))
"# });
    assert!(
        matches!(
            &*error,
            CompilationErrorImpl::TraitImplEffectsMismatch { .. }
        ),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn derivation_requires_only_what_it_uses() {
    // `Default` constructs the default variant alone, so the payload's prerequisite is irrelevant.
    TestSession::new().run(indoc! { r#"
trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
struct Cb<! F>(() -> int ! F)
impl<! F> Run for <Self = Cb<! F> |-> ! E = F> {
    fn run(x: Cb<! F>) -> int { (x.0)() }
}
impl<! F> Default for Cb<! F> {
    fn default() -> Cb<! F> { Cb(|| 5) }
}
struct Wrap<T>(T)
impl<T> Default for Wrap<T> where T: Value, T: Default, T: Run<! E = ()> {
    fn default() -> Wrap<T> { Wrap(default()) }
}
enum Maybe<! F> { #[default] None, Some(Wrap<Cb<! F>>) }
fn f<! E>(g: () -> int ! E) -> int { let x: Maybe<! E> = default(); 1 }
f(|| idiv(1, 0))
"# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_concrete_prerequisite_outputs_do_not_separate_impls() {
    for source in [
        indoc! { r#"
struct Cb<T>(T)
struct Seed<T>(T)
struct W<T>(T)
type Pure = () -> int ! ();
type Failing = () -> int ! fallible;
trait Source<Self |-> Item> { fn source(x: Self) -> Item; }
impl Source for <Self = Seed<int> |-> Item = Cb<Failing>> {
 fn source(x: Seed<int>) -> Cb<Failing> { Cb(||idiv(4,2)) }
}
trait R<Self> { fn r(x: Self) -> int; }
impl<T> R for W<T> where T: Value, Seed<T>: Source<Item = Cb<Pure>> {
 fn r(x: W<T>) -> int { 1 }
}
impl<T> R for W<T> where T: Value, Seed<T>: Source<Item = Cb<Failing>> {
 fn r(x: W<T>) -> int { 2 }
}
r(W(0))"# },
        indoc! { r#"
struct Cb<T>(T)
struct Seed<T>(T)
struct W<T>(T)
type Pure = () -> int ! ();
type Failing = () -> int ! fallible;
trait Source<Self |-> Item> { fn source(x: Self) -> Item; }
impl Source for <Self = Seed<int> |-> Item = Cb<Failing>> {
 fn source(x: Seed<int>) -> Cb<Failing> { Cb(||idiv(4,2)) }
}
trait R<Self> { fn r(x: Self) -> int; }
impl<T> R for W<T> where T: Value, Seed<T>: Source<Item = Cb<Failing>> {
 fn r(x: W<T>) -> int { 2 }
}
impl<T> R for W<T> where T: Value, Seed<T>: Source<Item = Cb<Pure>> {
 fn r(x: W<T>) -> int { 1 }
}
r(W(0))"# },
    ] {
        let error = TestSession::new().fail_compilation(source);
        assert!(
            matches!(
                &*error,
                CompilationErrorImpl::OverlappingTraitImpls {
                    effects_ignored: true,
                    ..
                }
            ),
            "{error:?}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_do_not_decide_what_improvement_infers() {
    // Effects do not choose the type of the literal: it defaults to `int` in every case.
    for source in [
        indoc! { r#"
struct Cb<T>(T)
struct W<T>(T)
trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
impl<! E> Run for <Self = Cb<(() -> int ! E)> |-> ! E = E> {
 fn run(x: Cb<(() -> int ! E)>) -> int { x.0() }
}
trait Pick<Self, Other> { fn pick(x: Self, y: Other) -> int; }
impl<T> Pick for <Self = Cb<T>, Other = W<int>>
where T: Value, Cb<T>: Run<! E = ()> {
 fn pick(x: Cb<T>, y: W<int>) -> int { 1 }
}
impl<T> Pick for <Self = Cb<T>, Other = W<float>>
where T: Value, Cb<T>: Run<! E = fallible> {
 fn pick(x: Cb<T>, y: W<float>) -> int { 2 }
}
type F = () -> int ! ();
let g: F = || 5;
pick(Cb(g), W(0))
"# },
        indoc! { r#"
struct Cb<T>(T)
struct W<T>(T)
trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
impl<! E> Run for <Self = Cb<(() -> int ! E)> |-> ! E = E> {
 fn run(x: Cb<(() -> int ! E)>) -> int { x.0() }
}
trait Pick<Self, Other> { fn pick(x: Self, y: Other) -> int; }
impl<T> Pick for <Self = Cb<T>, Other = W<float>>
where T: Value, Cb<T>: Run<! E = fallible> {
 fn pick(x: Cb<T>, y: W<float>) -> int { 2 }
}
impl<T> Pick for <Self = Cb<T>, Other = W<int>>
where T: Value, Cb<T>: Run<! E = ()> {
 fn pick(x: Cb<T>, y: W<int>) -> int { 1 }
}
type F = () -> int ! ();
let g: F = || 5;
pick(Cb(g), W(0))
"# },
    ] {
        assert_val_eq!(TestSession::new().run(source), int(1));
    }
    for source in [
        indoc! { r#"
struct Cb<T>(T)
struct W<T>(T)
trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
impl<! E> Run for <Self = Cb<(() -> int ! E)> |-> ! E = E> {
 fn run(x: Cb<(() -> int ! E)>) -> int { x.0() }
}
trait Pick<Self, Other> { fn pick(x: Self, y: Other) -> int; }
impl<T> Pick for <Self = Cb<T>, Other = W<int>>
where T: Value, Cb<T>: Run<! E = ()> {
 fn pick(x: Cb<T>, y: W<int>) -> int { 1 }
}
impl<T> Pick for <Self = Cb<T>, Other = W<float>>
where T: Value, Cb<T>: Run<! E = fallible> {
 fn pick(x: Cb<T>, y: W<float>) -> int { 2 }
}
type F = () -> int ! fallible;
let g: F = || 5;
pick(Cb(g), W(0))
"# },
        indoc! { r#"
struct Cb<T>(T)
struct W<T>(T)
trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
impl<! E> Run for <Self = Cb<(() -> int ! E)> |-> ! E = E> {
 fn run(x: Cb<(() -> int ! E)>) -> int { x.0() }
}
trait Pick<Self, Other> { fn pick(x: Self, y: Other) -> int; }
impl<T> Pick for <Self = Cb<T>, Other = W<float>>
where T: Value, Cb<T>: Run<! E = fallible> {
 fn pick(x: Cb<T>, y: W<float>) -> int { 2 }
}
impl<T> Pick for <Self = Cb<T>, Other = W<int>>
where T: Value, Cb<T>: Run<! E = ()> {
 fn pick(x: Cb<T>, y: W<int>) -> int { 1 }
}
type F = () -> int ! fallible;
let g: F = || 5;
pick(Cb(g), W(0))
"# },
    ] {
        let error = TestSession::new().fail_compilation(source);
        assert!(
            matches!(
                &*error,
                CompilationErrorImpl::TraitImplEffectsMismatch { .. }
            ),
            "{error:?}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn structural_selection_erases_effects_through_nested_prerequisites() {
    for source in [
        indoc! { r#"
struct Cb<T>(T)
struct Out<T>(T)
struct Inner<T>(T)
struct Outer<T>(T)
type Pure = () -> int ! ();
type Failing = () -> int ! fallible;
trait Source<Self |-> Item> { fn source(x: Self) -> Item; }
trait Gate<Self> { fn gate(x: Self) -> int; }
impl<! E> Source for <Self = Cb<(() -> int ! E)> |-> Item = Out<(() -> int ! E)>> {
 fn source(x: Cb<(() -> int ! E)>) -> Out<(() -> int ! E)> { Out(x.0) }
}
impl<T> Gate for Inner<T> where T: Value, T: Source<Item = Out<Failing>> {
 fn gate(x: Inner<T>) -> int { 1 }
}
impl<T> Serialize for Outer<T> where T: Value, Inner<T>: Gate {
 fn serialize(x: Outer<T>) -> DataValue { serialize(1) }
}
impl<! E> Serialize for Cb<(() -> int ! E)> {
 fn serialize(x: Cb<(() -> int ! E)>) -> DataValue { serialize(2) }
}
let cb: Cb<Pure> = Cb(||5);
serialize(Outer(cb))
"# },
        indoc! { r#"
struct Cb<T>(T)
struct Out<T>(T)
struct Inner<T>(T)
struct Outer<T>(T)
type Pure = () -> int ! ();
type Failing = () -> int ! fallible;
trait Source<Self |-> Item> { fn source(x: Self) -> Item; }
trait Gate<Self> { fn gate(x: Self) -> int; }
impl<! E> Serialize for Cb<(() -> int ! E)> {
 fn serialize(x: Cb<(() -> int ! E)>) -> DataValue { serialize(2) }
}
impl<T> Serialize for Outer<T> where T: Value, Inner<T>: Gate {
 fn serialize(x: Outer<T>) -> DataValue { serialize(1) }
}
impl<T> Gate for Inner<T> where T: Value, T: Source<Item = Out<Failing>> {
 fn gate(x: Inner<T>) -> int { 1 }
}
impl<! E> Source for <Self = Cb<(() -> int ! E)> |-> Item = Out<(() -> int ! E)>> {
 fn source(x: Cb<(() -> int ! E)>) -> Out<(() -> int ! E)> { Out(x.0) }
}
let cb: Cb<Pure> = Cb(||5);
serialize(Outer(cb))
"# },
    ] {
        let error = TestSession::new().fail_compilation(source);
        assert!(
            matches!(
                &*error,
                CompilationErrorImpl::TraitImplEffectsMismatch { .. }
            ),
            "{error:?}"
        );
    }
    for source in [
        indoc! { r#"
struct Cb<T>(T)
struct Out<T>(T)
struct Inner<T>(T)
struct Outer<T>(T)
type Pure = () -> int ! ();
type Failing = () -> int ! fallible;
trait Source<Self |-> Item> { fn source(x: Self) -> Item; }
trait Gate<Self> { fn gate(x: Self) -> int; }
impl<! E> Source for <Self = Cb<(() -> int ! E)> |-> Item = Out<(() -> int ! E)>> {
 fn source(x: Cb<(() -> int ! E)>) -> Out<(() -> int ! E)> { Out(x.0) }
}
impl<T> Gate for Inner<T> where T: Value, T: Source<Item = Out<Failing>> {
 fn gate(x: Inner<T>) -> int { 1 }
}
impl<T> Serialize for Outer<T> where T: Value, Inner<T>: Gate {
 fn serialize(x: Outer<T>) -> DataValue { serialize(1) }
}
impl<! E> Serialize for Cb<(() -> int ! E)> {
 fn serialize(x: Cb<(() -> int ! E)>) -> DataValue { serialize(2) }
}
let cb: Cb<Failing> = Cb(||5);
serialize(Outer(cb))
"# },
        indoc! { r#"
struct Cb<T>(T)
struct Out<T>(T)
struct Inner<T>(T)
struct Outer<T>(T)
type Pure = () -> int ! ();
type Failing = () -> int ! fallible;
trait Source<Self |-> Item> { fn source(x: Self) -> Item; }
trait Gate<Self> { fn gate(x: Self) -> int; }
impl<! E> Serialize for Cb<(() -> int ! E)> {
 fn serialize(x: Cb<(() -> int ! E)>) -> DataValue { serialize(2) }
}
impl<T> Serialize for Outer<T> where T: Value, Inner<T>: Gate {
 fn serialize(x: Outer<T>) -> DataValue { serialize(1) }
}
impl<T> Gate for Inner<T> where T: Value, T: Source<Item = Out<Failing>> {
 fn gate(x: Inner<T>) -> int { 1 }
}
impl<! E> Source for <Self = Cb<(() -> int ! E)> |-> Item = Out<(() -> int ! E)>> {
 fn source(x: Cb<(() -> int ! E)>) -> Out<(() -> int ! E)> { Out(x.0) }
}
let cb: Cb<Failing> = Cb(||5);
serialize(Outer(cb))
"# },
    ] {
        TestSession::new().run(source);
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_custom_value_impl_with_wrong_effects_does_not_fall_back_to_derivation() {
    for source in [
        indoc! { r#"
struct Cb<T>(T)
struct Wrap<T>(T)
trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
impl<! E> Run for <Self = Cb<(() -> int ! E)> |-> ! E = E> {
 fn run(x: Cb<(() -> int ! E)>) -> int { x.0() }
}
impl<T> Value for Wrap<T> where T: Value, T: Run<! E = ()> {
 fn eq(x: Wrap<T>, y: Wrap<T>) -> bool { run(x.0) == run(y.0) }
 fn to_string(x: Wrap<T>) -> string { to_string(run(x.0)) }
 fn hash(x: Wrap<T>, state: &mut hasher) { hash(run(x.0), state) }
 fn clone(x: Wrap<T>) -> Wrap<T> { Wrap(x.0) }
 fn drop(x: &mut Wrap<T>) {}
}
type F = () -> int ! fallible; let cb: Cb<F> = Cb(||5);
to_string(Wrap(cb))"# },
        indoc! { r#"
struct Cb<T>(T)
struct Wrap<T>(T)
trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
impl<! E> Run for <Self = Cb<(() -> int ! E)> |-> ! E = E> {
 fn run(x: Cb<(() -> int ! E)>) -> int { x.0() }
}
impl<T> Value for Wrap<T> where T: Value, T: Run<! E = ()> {
 fn eq(x: Wrap<T>, y: Wrap<T>) -> bool { run(x.0) == run(y.0) }
 fn to_string(x: Wrap<T>) -> string { to_string(run(x.0)) }
 fn hash(x: Wrap<T>, state: &mut hasher) { hash(run(x.0), state) }
 fn clone(x: Wrap<T>) -> Wrap<T> { Wrap(x.0) }
 fn drop(x: &mut Wrap<T>) {}
}
type F = () -> int ! fallible; let cb: Cb<F> = Cb(||5);
to_string((Wrap(cb),))"# },
    ] {
        let mut session = TestSession::new();
        session.allow_unsafe();
        let error = session.fail_compilation(source);
        assert!(
            matches!(
                &*error,
                CompilationErrorImpl::TraitImplEffectsMismatch { .. }
            ),
            "{error:?}"
        );
    }
    for source in [
        indoc! { r#"
struct Cb<T>(T)
struct Wrap<T>(T)
trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
impl<! E> Run for <Self = Cb<(() -> int ! E)> |-> ! E = E> {
 fn run(x: Cb<(() -> int ! E)>) -> int { x.0() }
}
impl<T> Value for Wrap<T> where T: Value, T: Run<! E = ()> {
 fn eq(x: Wrap<T>, y: Wrap<T>) -> bool { run(x.0) == run(y.0) }
 fn to_string(x: Wrap<T>) -> string { to_string(run(x.0)) }
 fn hash(x: Wrap<T>, state: &mut hasher) { hash(run(x.0), state) }
 fn clone(x: Wrap<T>) -> Wrap<T> { Wrap(x.0) }
 fn drop(x: &mut Wrap<T>) {}
}
type F = () -> int ! (); let cb: Cb<F> = Cb(||5);
to_string(Wrap(cb))"# },
        indoc! { r#"
struct Cb<T>(T)
struct Wrap<T>(T)
trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
impl<! E> Run for <Self = Cb<(() -> int ! E)> |-> ! E = E> {
 fn run(x: Cb<(() -> int ! E)>) -> int { x.0() }
}
impl<T> Value for Wrap<T> where T: Value, T: Run<! E = ()> {
 fn eq(x: Wrap<T>, y: Wrap<T>) -> bool { run(x.0) == run(y.0) }
 fn to_string(x: Wrap<T>) -> string { to_string(run(x.0)) }
 fn hash(x: Wrap<T>, state: &mut hasher) { hash(run(x.0), state) }
 fn clone(x: Wrap<T>) -> Wrap<T> { Wrap(x.0) }
 fn drop(x: &mut Wrap<T>) {}
}
type F = () -> int ! (); let cb: Cb<F> = Cb(||5);
to_string((Wrap(cb),))"# },
    ] {
        let mut session = TestSession::new();
        session.allow_unsafe();
        session.run(source);
    }
}

const DEFAULT_METHOD_HELPERS: &str = indoc! { r#"
    trait Size<Self> { fn size(x: Self) -> int; }
    impl<! F> Size for Cb<! F> {
        fn size(x: Cb<! F>) -> int { 7 }
    }
    struct W<T>(T)
    trait Pure<Self> { fn pure(x: Self) -> int; }
    impl<T> Pure for W<T> where T: Run<! E = ()> {
        fn pure(x: W<T>) -> int { run(x.0) }
    }
    struct M<! F>(() -> int ! F)
"# };

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn selection_does_not_strengthen_the_contract_of_a_default_method() {
    let prelude = format!("{CALL_THROUGH_TRAIT}{PURE_RUN_SERIALIZER}{DEFAULT_METHOD_HELPERS}");
    let imp = "impl<! F> D for <Self = M<! F> |-> ! E = F> {}";
    // An impl that applies for every effect serves every effect.
    assert_val_eq!(
        TestSession::new().run(&format!(
            "{prelude}
            trait D<Self |-> ! E> {{ fn go(x: Self, g: () -> int ! E) -> int {{ size(Cb(g)) }} }}
            {imp}
            go(M(|| 1), || 1) + go(M(|| idiv(4, 2)), || idiv(4, 2))"
        )),
        int(14)
    );
    // An effect the contract exposes may be performed.
    assert_val_eq!(
        TestSession::new().run(&format!(
            "{prelude}
            trait D<Self |-> ! E> {{ fn go(x: Self, g: () -> int ! E) -> int ! E {{ run(Cb(g)) }} }}
            {imp}
            go(M(|| 1), || 1) + go(M(|| idiv(4, 2)), || idiv(4, 2))"
        )),
        int(3)
    );
    // What an impl requires of the effect, the default cannot promise.
    for body in [
        "run(Cb(g))",
        "pure(W(Cb(g)))",
        "to_string(serialize((Wrap(Cb(g)),)))",
    ] {
        TestSession::new().fail_compilation(&format!(
            "{prelude}
            trait D<Self |-> ! E> {{ fn go(x: Self, g: () -> int ! E) -> int {{ {body}; 1 }} }}"
        ));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effect_independent_selection_holds_across_modules() {
    const LIB: &str = r#"
        pub trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
        pub struct Cb<! F>(() -> int ! F)
        pub fn cb<! F>(f: () -> int ! F) -> Cb<! F> { Cb(f) }
        impl<! F> Run for <Self = Cb<! F> |-> ! E = F> {
            fn run(x: Cb<! F>) -> int { (x.0)() }
        }
        pub struct Wrap<T>(T)
        pub fn wrap<T>(x: T) -> Wrap<T> { Wrap(x) }
        impl<T> Serialize for Wrap<T> where T: Run<! E = ()> {
            fn serialize(x: Wrap<T>) -> DataValue { serialize(run(x.0)) }
        }
        pub fn warm() -> DataValue { serialize((wrap(cb(|| 3)),)) }
    "#;
    let session = || {
        let mut session = TestSession::new();
        session
            .try_compile_module("lib", LIB)
            .unwrap_or_else(|error| panic!("{error:?}"));
        session
    };
    // The prerequisite of an imported impl uses the real effects, through derivation too, even
    // when the imported module already derived the erased form.
    for term in ["lib::wrap(lib::cb(g))", "(lib::wrap(lib::cb(g)),)"] {
        assert!(
            session()
                .try_compile_module(
                    "user",
                    &format!("fn f<! E>(g: () -> int ! E) -> DataValue {{ serialize({term}) }}"),
                )
                .is_err(),
            "{term}"
        );
    }
    // An importing module may not restrict effects in its own impl either.
    let error = session()
        .try_compile_module(
            "user",
            "use lib::{Run, Cb};
            struct Box<T>(T)
            impl Run for <Self = Box<Cb<! fallible>> |-> ! E = ()> {
                fn run(x: Box<Cb<! fallible>>) -> int { 1 }
            }",
        )
        .expect_err("the impl fixes an effect");
    assert!(
        matches!(
            &*error,
            CompilationErrorImpl::TraitImplInputRestrictsEffect { .. }
        ),
        "{error:?}"
    );
    // A polymorphic impl from another module serves every effect.
    let mut session = session();
    assert_val_eq!(
        session.run(
            "use lib::{Run, cb};
            fn f(g) { run(cb(g)) }
            f(|| 1) + f(|| idiv(4, 2))"
        ),
        int(3)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_effect_mismatch_does_not_hide_a_nested_output_type_mismatch() {
    // `Get` produces `int`, so the `W<int>` candidate cannot apply, whatever the effects of `Run`.
    assert_val_eq!(
        TestSession::new().run(indoc! { r#"
struct Seed<T>(T)
struct W<T>(T)
trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
impl<T> Run for <Self = Seed<T> |-> ! E = fallible> where T: Value {
 fn run(x: Seed<T>) -> int { 2 }
}
trait Get<Self |-> Item> { fn get(x: Self) -> Item; }
impl<T> Get for <Self = Seed<T> |-> Item = int> where T: Value, Seed<T>: Run<! E = ()> {
 fn get(x: Seed<T>) -> int { 3 }
}
trait Pick<Self, Other> { fn pick(x: Self, y: Other) -> int; }
impl<T> Pick for <Self = Seed<T>, Other = W<int>> where T: Value, Seed<T>: Get<Item = bool> {
 fn pick(x: Seed<T>, y: W<int>) -> int { 1 }
}
impl<T> Pick for <Self = Seed<T>, Other = W<float>> where T: Value {
 fn pick(x: Seed<T>, y: W<float>) -> int { 2 }
}
let x: Seed<int> = Seed(0); pick(x, W(0))"# }),
        int(2)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_effect_requirement_of_a_selected_impl_is_reported_where_it_is_applied() {
    let source = format!(
        "{CALL_THROUGH_TRAIT}{PURE_RUN_SERIALIZER}
        fn f<! E>(g: () -> int ! E) -> DataValue {{ serialize((Wrap(Cb(g)),)) }}"
    );
    let error = TestSession::new().fail_compilation(&source);
    let CompilationErrorImpl::InvalidEffectDependency { source_span, .. } = &*error else {
        panic!("unexpected diagnostic: {error:?}")
    };
    let call = source.rfind("serialize(").expect("the program has a call");
    assert_eq!(source_span.start_usize(), call, "{error:?}");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn outputs_of_a_concrete_impl_differing_only_in_effects_are_an_effect_error() {
    let error = TestSession::new().fail_compilation(indoc! { r#"
        struct Cb<T>(T)
        struct Seed(int)
        struct W<T>(T)
        type Pure = () -> int ! ();
        type Failing = () -> int ! fallible;
        trait Source<Self |-> Item> { fn source(x: Self) -> Item; }
        impl Source for <Self = Seed |-> Item = Cb<Failing>> {
            fn source(x: Seed) -> Cb<Failing> { Cb(|| idiv(4, 2)) }
        }
        trait R<Self> { fn r(x: Self) -> int; }
        impl<T> R for W<T> where T: Value, Seed: Source<Item = Cb<Pure>> {
            fn r(x: W<T>) -> int { 1 }
        }
    "# });
    assert!(
        matches!(
            &*error,
            CompilationErrorImpl::TraitImplEffectsMismatch { .. }
        ),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_custom_value_impl_checks_prerequisites_with_the_real_effects() {
    const PRELUDE: &str = indoc! { r#"
trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
struct Cb<! E>(() -> int ! E)
impl<! E> Run for <Self = Cb<! E> |-> ! E = E> { fn run(x: Cb<! E>) -> int { (x.0)() } }
struct Wrap<T>(T)
impl<T> Value for Wrap<T> where T: Value, T: Run<! E = ()> {
fn eq(x: Wrap<T>, y: Wrap<T>) -> bool { run(x.0) == run(y.0) }
fn to_string(x: Wrap<T>) -> string { to_string(run(x.0)) }
fn hash(x: Wrap<T>, state: &mut hasher) { hash(run(x.0), state) }
fn clone(x: Wrap<T>) -> Wrap<T> { Wrap(x.0) }
fn drop(x: &mut Wrap<T>) {}
}
"# };
    for term in ["Wrap(Cb(g))", "(Wrap(Cb(g)),)", "{ a: Wrap(Cb(g)) }"] {
        let mut session = TestSession::new();
        session.allow_unsafe();
        session.fail_compilation(&format!(
            "{PRELUDE}
            fn f<! E>(g: () -> int ! E) -> string {{ to_string({term}) }}
            f(|| idiv(1, 0))"
        ));
    }
    // A pure callback runs the source impl, whether its effect is written or inferred.
    for (term, expected) in [
        ("Wrap(Cb(|| 5))", "5"),
        ("(Wrap(Cb(|| 5)),)", "(5)"),
        ("Some(Wrap(Cb(|| 5)))", "Some (5)"),
        ("Wrap(Cb(g))", "5"),
    ] {
        let mut session = TestSession::new();
        session.allow_unsafe();
        assert_val_eq!(
            session.run(&format!(
                "{PRELUDE}
                let g: () -> int ! () = || 5;
                to_string({term})"
            )),
            string(expected),
            "{term}"
        );
    }
    // Effects do not reach the derived rendering: a failing callback is an error.
    for term in ["Wrap(Cb(g))", "(Wrap(Cb(g)),)"] {
        let mut session = TestSession::new();
        session.allow_unsafe();
        session.fail_compilation(&format!(
            "{PRELUDE}
            let g = || idiv(1, 0);
            to_string({term})"
        ));
    }
}
