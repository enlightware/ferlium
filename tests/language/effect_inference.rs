// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Soundness and precision of inferred effects: callback effects reaching their callers through
//! trait outputs, joins, declared effect variables and generalization.

use test_log::test;

use indoc::indoc;
use ustr::ustr;

use crate::harness::{TestSession, int};
use ferlium::{
    compiler::error::{CompilationErrorImpl, SourceFailureKind},
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
