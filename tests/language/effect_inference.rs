// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Soundness and precision of inferred effects: callback effects reaching their callers through
//! trait outputs, joins, declared effect variables and generalization.

use test_log::test;

use indoc::indoc;
use ustr::ustr;

use crate::harness::{TestSession, float, int, string};
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

/// Runs `call` after `prelude` and the two `functions`, declared in both orders.
fn assert_in_both_orders(prelude: &str, functions: [&str; 2], call: &str, expected: isize) {
    for [first, second] in [functions, [functions[1], functions[0]]] {
        let src = format!("{prelude}\n{first}\n{second}\n{call}");
        assert_val_eq!(TestSession::new().run(&src), int(expected));
    }
}

/// Checks the signature of `function` with the two `functions` declared in both orders.
fn assert_signature_in_both_orders(functions: [&str; 2], function: &str, expected: &str) {
    for [first, second] in [functions, [functions[1], functions[0]]] {
        let src = format!("{first}\n{second}\n");
        assert_eq!(signature(&mut TestSession::new(), &src, function), expected);
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
    error.expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
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
    error.expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
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

// Written effect generics in mutually recursive functions

const MUTUAL_F: &str = "fn f<! E>(g: () -> int ! E, n: int) -> int {
    if n > 0 {
        h(g, n - 1)
    } else {
        g()
    }
}
";
const MUTUAL_H: &str = "fn h<! F>(g: () -> int ! F, n: int) -> int {
    if n > 0 {
        f(g, n - 1)
    } else {
        g()
    }
}
";

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mutually_recursive_effect_generics_work_in_any_order() {
    let calls = "let a = [10, 20];
        f(|| 1, 3) + h(|| a[1], 2) + f(|| a[0], 2) + h(|| 2, 1)";
    for declarations in [
        format!("{MUTUAL_F}{MUTUAL_H}"),
        format!("{MUTUAL_H}{MUTUAL_F}"),
    ] {
        let mut session = TestSession::new();
        assert_val_eq!(session.run(&format!("{declarations}{calls}")), int(33));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mutually_recursive_effect_generics_stay_independent_for_callers() {
    let src = format!("{MUTUAL_F}{MUTUAL_H}");
    assert_eq!(
        signature(&mut TestSession::new(), &src, "f"),
        "fn f<! E>(g: () -> int ! E, n: int) -> int ! E"
    );
    assert_eq!(
        signature(&mut TestSession::new(), &src, "h"),
        "fn h<! F>(g: () -> int ! F, n: int) -> int ! F"
    );
    let mut session = TestSession::new();
    assert_eq!(
        session.fail_run(&format!("{src}\nh(|| idiv(1, 0), 1)")),
        SourceFailureKind::DivisionByZero,
    );
    let pure_caller = format!("{src}\nfn pure_caller() -> int {{ f(|| 1, 2) }}");
    assert_eq!(
        fn_effects(&mut TestSession::new(), &pure_caller, "pure_caller"),
        no_effects()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effect_generics_work_across_a_longer_cycle() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
        fn a1<! A>(g: () -> int ! A, n: int) -> int {
            if n > 0 {
                b1(g, n - 1)
            } else {
                g()
            }
        }
        fn b1<! B>(g: () -> int ! B, n: int) -> int {
            if n > 0 {
                c1(g, n - 1)
            } else {
                g()
            }
        }
        fn c1<! C>(g: () -> int ! C, n: int) -> int {
            if n > 0 {
                a1(g, n - 1)
            } else {
                g()
            }
        }
        let v = [4];
        a1(|| 1, 5) + c1(|| v[0], 5)
    "# }),
        int(5)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn crossed_effect_generics_keep_their_names_in_any_order() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
        fn p<! E1, E2>(x: () -> int ! E1, y: () -> int ! E2, n: int) -> int {
            if n > 0 {
                q(y, x, n - 1)
            } else {
                n
            }
        }
        fn q<! F1, F2>(x: () -> int ! F1, y: () -> int ! F2, n: int) -> int {
            if n > 0 {
                p(y, x, n - 1)
            } else {
                n
            }
        }
        let v = [4];
        p(|| 1, || v[0], 3)
    "# }),
        int(0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effect_generics_work_in_invariant_positions() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
        fn f<! E>(gs: [() -> int ! E], n: int) -> int {
            if n > 0 {
                h(gs, n - 1)
            } else {
                gs[0]()
            }
        }
        fn h<! F>(gs: [() -> int ! F], n: int) -> int {
            if n > 0 {
                f(gs, n - 1)
            } else {
                gs[0]()
            }
        }
        let v = [3];
        f([|| v[0]], 2) + h([|| 9], 1)
    "# }),
        int(12)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_of_two_generics_cannot_share_a_row_through_a_cycle() {
    let mut session = TestSession::new();
    session.fail_compilation(indoc! { r#"
        fn f<! E, F>(a: () -> int ! E, b: () -> int ! F, n: int) -> int {
            if n > 0 {
                h(a, n - 1) + h(b, n - 1)
            } else {
                0
            }
        }
        fn h<! X>(g: () -> int ! X, n: int) -> int {
            if n > 0 {
                f(g, g, n - 1)
            } else {
                g()
            }
        }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effect_generics_of_a_group_work_with_an_impl_in_any_order() {
    let types = "struct Foo(int)\ntrait Tally<Self> { fn tally(x: Self) -> int; }\n";
    let imp = "impl Tally for Foo { fn tally(x: Foo) -> int { h(|| 5, 0) + 1 } }\n";
    let caller = "fn f<! E>(g: () -> int ! E, n: int) -> int {
        if n > 0 {
            h(g, n - 1)
        } else {
            g() + tally(Foo(n))
        }
    }\n";
    for src in [
        format!("{types}{imp}{MUTUAL_H}{caller}"),
        format!("{caller}{MUTUAL_H}{types}{imp}"),
    ] {
        let mut session = TestSession::new();
        assert_val_eq!(session.run(&format!("{src}f(|| 1, 2)")), int(7));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn validating_a_group_does_not_repeat_its_warnings() {
    let mut session = TestSession::new();
    let module_id = session
        .compile(&format!(
            "{MUTUAL_H}{}",
            "fn f<! E>(g: () -> int ! E, n: int) -> int { return h(g, n) }"
        ))
        .module_id;
    let compiler_session = session.session();
    let diagnostics = compiler_session
        .modules()
        .info(module_id)
        .unwrap()
        .diagnostics();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
}

/// Check the result of `call` in both orders of `functions`, after `prelude`.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn crossed_effect_generics_publish_their_source_names() {
    let p = indoc! { r#"
        fn p<! E1, E2>(x: () -> int ! E1, y: () -> int ! E2, n: int) -> int {
            if n > 0 {
                q(y, x, n - 1)
            } else {
                x()
            }
        }
    "# };
    let q = indoc! { r#"
        fn q<! F1, F2>(x: () -> int ! F1, y: () -> int ! F2, n: int) -> int {
            if n > 0 {
                p(y, x, n - 1)
            } else {
                y()
            }
        }
    "# };
    for src in [format!("{p}{q}"), format!("{q}{p}")] {
        assert_eq!(
            signature(&mut TestSession::new(), &src, "p"),
            "fn p<! E1, E2>(x: () -> int ! E1, y: () -> int ! E2, n: int) -> int ! E1"
        );
        assert_eq!(
            signature(&mut TestSession::new(), &src, "q"),
            "fn q<! F1, F2>(x: () -> int ! F1, y: () -> int ! F2, n: int) -> int ! F2"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unrelated_effect_generics_keep_their_own_effects() {
    let f = "fn f<! E>(g: () -> int ! E, n: int) -> int {
        if n > 0 {
            h(|| 1, n - 1)
        } else {
            g()
        }
    }";
    let h = "fn h<! F>(g: () -> int ! F, n: int) -> int {
        if n > 0 {
            f(|| 1, n - 1)
        } else {
            g()
        }
    }";
    assert_in_both_orders("", [f, h], "f(|| 3, 2)", 1);
    let src = format!("{f}\n{h}\n");
    assert_eq!(
        signature(&mut TestSession::new(), &src, "f"),
        "fn f<! E>(g: () -> int ! E, n: int) -> int ! E"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn call_in_a_group_may_instantiate_an_effect_generic_concretely() {
    let f = "fn f<! E>(g: () -> int ! E, n: int) -> int {
        let a = [1];
        if n > 0 {
            h(|| a[0], n - 1)
        } else {
            g()
        }
    }";
    assert_in_both_orders("", [f, MUTUAL_H], "f(|| 1, 2)", 1);
    let src = format!("{f}\n{MUTUAL_H}");
    assert_eq!(
        signature(&mut TestSession::new(), &src, "f"),
        "fn f<! E>(g: () -> int ! E, n: int) -> int ! (fallible, E)"
    );
    assert_eq!(
        signature(&mut TestSession::new(), &src, "h"),
        "fn h<! F>(g: () -> int ! F, n: int) -> int ! (fallible, F)"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn call_in_a_group_may_instantiate_with_a_row() {
    let f = "fn f<! E>(g: () -> int ! E, n: int) -> int {
        let a = [1];
        if n > 0 {
            h(|| a[0], n - 1)
        } else {
            g()
        }
    }";
    let h = "fn h<! F>(g: () -> int ! (fallible, F), n: int) -> int {
        if n > 0 {
            f(g, n - 1)
        } else {
            g()
        }
    }";
    assert_in_both_orders("", [f, h], "f(|| 1, 2)", 1);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generics_of_one_function_can_be_called_with_equal_arguments() {
    let f = "fn f<! E, F>(a: () -> int ! E, b: () -> int ! F, n: int) -> int {
        if n > 0 {
            h(a, n - 1) + h(b, n - 1)
        } else {
            0
        }
    }";
    let h = "fn h<! X>(g: () -> int ! X, n: int) -> int {
        if n > 0 {
            f(g, g, n - 1)
        } else {
            0
        }
    }";
    assert_in_both_orders("", [f, h], "f(|| 1, || 2, 2)", 0);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn self_recursion_can_swap_effect_generics() {
    let mut session = TestSession::new();
    let src = indoc! { r#"
        fn f<! E, F>(a: () -> int ! E, b: () -> int ! F, n: int) -> int {
            if n > 0 {
                f(b, a, n - 1)
            } else {
                0
            }
        }
    "# };
    assert_val_eq!(session.run(&format!("{src}\nf(|| 1, || 2, 2)")), int(0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unannotated_helper_in_a_group_is_generic() {
    let mut session = TestSession::new();
    let src = indoc! { r#"
        fn f<! E>(g: () -> int ! E, n: int) -> int {
            if n > 0 {
                k(g, n - 1)
            } else {
                g()
            }
        }
        fn k(g, n: int) -> int {
            if n > 0 {
                f(g, n - 1)
            } else {
                g()
            }
        }
    "# };
    assert_eq!(
        signature(&mut session, src, "k"),
        "fn k<! e₀>(g: () -> int ! e₀, n: int) -> int ! e₀"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unused_effect_generics_in_a_group_disappear() {
    let f = "fn f<! E>(n: int) -> int {
        if n > 0 {
            h(n - 1)
        } else {
            1
        }
    }";
    let h = "fn h<! F>(n: int) -> int {
        if n > 0 {
            f(n - 1)
        } else {
            2
        }
    }";
    assert_in_both_orders("", [f, h], "f(2)", 1);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn group_with_effect_generics_passes_dictionaries() {
    let f = "fn f<T ! E>(x: T, g: () -> int ! E, n: int) -> T where T: Num {
        if n > 0 {
            h(x + x, g, n - 1)
        } else {
            g();
            x
        }
    }";
    let h = "fn h<U ! F>(x: U, g: () -> int ! F, n: int) -> U where U: Num {
        if n > 0 {
            f(x * x, g, n - 1)
        } else {
            x
        }
    }";
    assert_in_both_orders("", [f, h], "f(2, || 1, 2) + h(3, || 1, 1)", 25);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn group_with_effect_generics_propagates_inferred_requirements() {
    let f = "fn f<T ! E>(x: T, g: () -> int ! E, n: int) -> T {
        if n > 0 {
            h(x, g, n - 1)
        } else {
            g();
            x
        }
    }";
    let h = "fn h<U ! F>(x: U, g: () -> int ! F, n: int) -> U {
        if n > 0 {
            f(x, g, n - 1)
        } else {
            x + x
        }
    }";
    assert_in_both_orders("", [f, h], "f(2, || 1, 1)", 4);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn group_with_effect_generics_passes_user_trait_dictionaries() {
    let prelude = indoc! { r#"
        trait Size<Self> {
            fn size(x: Self) -> int;
        }
        impl Size for int {
            fn size(x: int) -> int {
                x
            }
        }
        impl Size for string {
            fn size(x: string) -> int {
                9
            }
        }
    "# };
    let f = "fn f<T ! E>(x: T, g: () -> int ! E, n: int) -> int {
        if n > 0 {
            h(x, g, n - 1)
        } else {
            size(x) + g()
        }
    }";
    let h = "fn h<U ! F>(x: U, g: () -> int ! F, n: int) -> int {
        if n > 0 {
            f(x, g, n - 1)
        } else {
            g()
        }
    }";
    assert_in_both_orders(prelude, [f, h], r#"f(5, || 1, 2) + h("s", || 1, 1)"#, 16);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn written_type_generic_stays_general_in_a_group_with_effect_generics() {
    let mut session = TestSession::new();
    session.fail_compilation(indoc! { r#"
        fn f<T ! E>(x: T, g: () -> int ! E, n: int) -> int {
            if n > 0 {
                h(true, g, n - 1)
            } else {
                g()
            }
        }
        fn h<U ! F>(x: U, g: () -> int ! F, n: int) -> int {
            if n > 0 {
                f(x, g, n - 1)
            } else {
                0
            }
        }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn body_cannot_pin_its_own_effect_generic_through_recursion() {
    let mut session = TestSession::new();
    session.fail_compilation(indoc! { r#"
        fn p(k: () -> int ! fallible) -> int {
            k()
        }
        fn f<! E>(g: () -> int ! E, n: int) -> int {
            if n > 0 {
                f(g, n - 1)
            } else {
                p(g)
            }
        }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_effect_generic_takes_a_failing_and_a_pure_callback_in_its_group() {
    // Each call of `h` in `f` has its own instance of `F`.
    let h = "fn h<! F>(g: () -> int ! F, n: int) {
        if n > 0 {
            f(n - 1);
            g
        } else {
            g
        }
    }";
    let f = "fn f(n: int) -> int {
        let a = [1];
        let failing = h(|| a[0], n);
        p(h(|| 1, n)) + failing()
    }";
    let p = "fn p(k: () -> int ! ()) -> int { k() }";
    assert_in_both_orders(p, [h, f], "f(1)", 2);
    assert_signature_in_both_orders(
        [h, &format!("{p}\n{f}")],
        "h",
        "fn h<! F>(g: () -> int ! F, n: int) -> () -> int ! F ! fallible",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unwritten_position_with_two_generics_of_one_function_is_rejected() {
    let mut session = TestSession::new();
    let error = session.fail_compilation(indoc! { r#"
        fn f<! E, F>(a: () -> int ! E, b: () -> int ! F, x, n: int) -> int {
            if n > 0 {
                h(a, x, n - 1) + h(b, x, n - 1)
            } else {
                0
            }
        }
        fn h<! X>(g: () -> int ! X, x, n: int) -> int {
            let chosen = if n > 1 {
                g
            } else {
                x
            };
            if n > 0 {
                f(g, g, chosen, n - 1)
            } else {
                0
            }
        }
    "# });
    // The effect of `x` would be both `E` and `F`, as it would without the recursion.
    assert!(matches!(
        &*error,
        CompilationErrorImpl::EffectVariablesCombined { first, second, .. }
            if *first == ustr("E") && *second == ustr("F")
    ));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn each_body_of_a_group_has_its_own_trait_applications() {
    let f = "fn c1<! e>(it: FilterIterator<ArrayIterator<int>, int ! e>, n: int) -> int {
        if n > 0 {
            c2(it, n - 1)
        } else {
            count(it)
        }
    }";
    let h = "fn c2<! d>(it: FilterIterator<ArrayIterator<int>, int ! d>, n: int) -> int {
        if n > 0 {
            c1(it, n - 1)
        } else {
            count(it) + 1
        }
    }";
    assert_in_both_orders("", [f, h], "1", 1);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn output_effect_of_a_requirement_joins_the_written_generic_in_a_group() {
    let prelude = indoc! { r#"
        trait Do<Self |-> ! Eff> {
            fn run(x: Self) -> int ! Eff;
        }
        struct P;
        struct Q;
        impl Do for P {
            fn run(x: P) -> int {
                1
            }
        }
        impl Do for Q {
            fn run(x: Q) -> int {
                idiv(4, 2)
            }
        }
    "# };
    let f = "fn f<T ! E>(x: T, g: () -> int ! E, n: int) -> int where T: Do {
        if n > 0 {
            h(x, g, n - 1)
        } else {
            run(x) + g()
        }
    }";
    let h = "fn h<U ! F>(x: U, g: () -> int ! F, n: int) -> int where U: Do {
        if n > 0 {
            f(x, g, n - 1)
        } else {
            g()
        }
    }";
    assert_in_both_orders(prelude, [f, h], "f(P, || 1, 2) + h(Q, || 1, 1)", 5);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn output_effect_of_a_requirement_is_kept_in_self_recursion() {
    let mut session = TestSession::new();
    let src = indoc! { r#"
        trait Do<Self |-> ! Eff> {
            fn run(x: Self) -> int ! Eff;
        }
        fn f<T ! E>(x: T, g: () -> int ! E, n: int) -> int where T: Do {
            if n > 0 {
                f(x, g, n - 1)
            } else {
                run(x) + g()
            }
        }
    "# };
    assert_eq!(
        signature(&mut session, src, "f"),
        "fn f<T ! E>(x: T, g: () -> int ! E, n: int) -> int ! E where T: Do < ! Eff = E>"
    );
}

// The remaining shapes of written effect generics in recursive groups.

/// Check `function`'s signature in both orders of `functions`.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn one_way_forwarding_keeps_each_written_generic() {
    let f = "fn f<! E>(g: () -> int ! E, n: int) -> int {
        if n > 0 {
            h(g, n - 1)
        } else {
            0
        }
    }";
    let h = "fn h<! F>(g: () -> int ! F, n: int) -> int {
        if n > 0 {
            f(|| 1, n - 1)
        } else {
            g()
        }
    }";
    assert_in_both_orders("", [f, h], "f(|| 3, 2)", 0);
    assert_signature_in_both_orders(
        [f, h],
        "f",
        "fn f<! E>(g: () -> int ! E, n: int) -> int ! E",
    );
    assert_signature_in_both_orders(
        [f, h],
        "h",
        "fn h<! F>(g: () -> int ! F, n: int) -> int ! F",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unannotated_parameter_in_a_group_takes_each_written_generic() {
    let f = "fn f<! E>(g: () -> int ! E, x, n: int) -> int {
        if n > 0 {
            h(g, x, n - 1)
        } else {
            x()
        }
    }";
    let h = "fn h<! F>(g: () -> int ! F, x, n: int) -> int {
        if n > 0 {
            f(g, x, n - 1)
        } else {
            g()
        }
    }";
    assert_in_both_orders("", [f, h], "f(|| 1, || 2, 2)", 2);
    assert_signature_in_both_orders(
        [f, h],
        "f",
        "fn f<! E>(g: () -> int ! E, x: () -> int ! E, n: int) -> int ! E",
    );
    assert_signature_in_both_orders(
        [f, h],
        "h",
        "fn h<! F>(g: () -> int ! F, x: () -> int ! F, n: int) -> int ! F",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn returned_callback_in_a_group_takes_each_written_generic() {
    let f = "fn f<! E>(g: () -> int ! E, n: int) {
        if n > 0 {
            h(g, n - 1)
        } else {
            g
        }
    }";
    let h = "fn h<! F>(g: () -> int ! F, n: int) {
        if n > 0 {
            f(g, n - 1)
        } else {
            g
        }
    }";
    assert_in_both_orders("", [f, h], "f(|| 1, 2)()", 1);
    assert_signature_in_both_orders(
        [f, h],
        "f",
        "fn f<! E>(g: () -> int ! E, n: int) -> () -> int ! E",
    );
    assert_signature_in_both_orders(
        [f, h],
        "h",
        "fn h<! F>(g: () -> int ! F, n: int) -> () -> int ! F",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fallibility_declared_on_both_functions_of_a_group() {
    let f = "fn f<! E>(g: () -> int ! (fallible, E), n: int) -> int {
        let a = [1];
        if n > 0 {
            h(|| a[0], n - 1)
        } else {
            g()
        }
    }";
    let h = "fn h<! F>(g: () -> int ! (fallible, F), n: int) -> int {
        if n > 0 {
            f(g, n - 1)
        } else {
            g()
        }
    }";
    assert_in_both_orders("", [f, h], "f(|| 1, 2)", 1);
    assert_signature_in_both_orders(
        [f, h],
        "f",
        "fn f<! E>(g: () -> int ! (fallible, E), n: int) -> int ! (fallible, E)",
    );
    assert_signature_in_both_orders(
        [f, h],
        "h",
        "fn h<! F>(g: () -> int ! (fallible, F), n: int) -> int ! (fallible, F)",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fallibility_declared_where_it_arrives_without_forwarding() {
    let f = "fn f<! E>(g: () -> int ! E, n: int) -> int {
        let a = [1];
        if n > 0 {
            h(|| a[0], n - 1)
        } else {
            g()
        }
    }";
    let h = "fn h<! F>(g: () -> int ! (fallible, F), n: int) -> int {
        if n > 0 {
            f(|| 1, n - 1)
        } else {
            g()
        }
    }";
    assert_in_both_orders("", [f, h], "f(|| 1, 2)", 1);
    assert_signature_in_both_orders(
        [f, h],
        "f",
        "fn f<! E>(g: () -> int ! E, n: int) -> int ! (fallible, E)",
    );
    assert_signature_in_both_orders(
        [f, h],
        "h",
        "fn h<! F>(g: () -> int ! (fallible, F), n: int) -> int ! (fallible, F)",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn type_and_effect_generics_are_independent_for_callers() {
    let f = "fn f<T ! E>(x: T, g: (T) -> int ! E, n: int) -> int {
        if n > 0 {
            h(x, g, n - 1)
        } else {
            g(x)
        }
    }";
    let h = "fn h<U ! F>(x: U, g: (U) -> int ! F, n: int) -> int {
        if n > 0 {
            f(x, g, n - 1)
        } else {
            g(x)
        }
    }";
    assert_in_both_orders("", [f, h], r#"f(1, |x| x + 1, 2) + h("a", |s| 1, 1)"#, 3);
    assert_signature_in_both_orders(
        [f, h],
        "f",
        "fn f<T ! E>(x: T, g: (T) -> int ! E, n: int) -> int ! E ",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unannotated_helper_keeps_its_own_generic_between_written_ones() {
    let mut session = TestSession::new();
    let src = indoc! { r#"
        fn f<! E>(g: () -> int ! E, n: int) -> int {
            if n > 0 {
                k(g, n - 1)
            } else {
                g()
            }
        }
        fn k(g, n: int) -> int {
            if n > 0 {
                h(g, n - 1)
            } else {
                g()
            }
        }
        fn h<! F>(g: () -> int ! F, n: int) -> int {
            if n > 0 {
                f(g, n - 1)
            } else {
                g()
            }
        }
    "# };
    assert_eq!(
        signature(&mut session, src, "k"),
        "fn k<! e₀>(g: () -> int ! e₀, n: int) -> int ! e₀"
    );
    assert_val_eq!(session.run(&format!("{src}\nf(|| 1, 3)")), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn concrete_effect_through_an_unannotated_helper_leaves_the_helper_generic() {
    let f = "fn f<! E>(g: () -> int ! E, n: int) -> int {
        let a = [1];
        if n > 0 {
            k(|| a[0], n - 1)
        } else {
            g()
        }
    }";
    let k = "fn k(g, n: int) -> int {
        if n > 0 {
            f(g, n - 1)
        } else {
            g()
        }
    }";
    assert_in_both_orders("", [f, k], "f(|| 1, 2)", 1);
    assert_signature_in_both_orders(
        [f, k],
        "f",
        "fn f<! E>(g: () -> int ! E, n: int) -> int ! (fallible, E)",
    );
    // `k` gets `|| a[0]` from `f` once, but its own callback can be any: it behaves as if
    // `f` were written out in it.
    assert_signature_in_both_orders(
        [f, k],
        "k",
        "fn k<! e₀>(g: () -> int ! e₀, n: int) -> int ! (fallible, e₀)",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn group_without_written_generics_infers_them() {
    let f = "fn f(g, n: int) -> int {
        let a = [1];
        if n > 0 {
            h(|| a[0], n - 1)
        } else {
            g()
        }
    }";
    let h = "fn h(g, n: int) -> int {
        if n > 0 {
            f(g, n - 1)
        } else {
            g()
        }
    }";
    assert_in_both_orders("", [f, h], "f(|| 1, 2)", 1);
    // `h` gets `|| a[0]` from `f` once, but the callback of `f` can be any, as if its effect
    // were written.
    for name in ["f", "h"] {
        assert_signature_in_both_orders(
            [f, h],
            name,
            &format!("fn {name}<! e₀>(g: () -> int ! e₀, n: int) -> int ! (fallible, e₀)"),
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn call_outside_recursion_instantiates_a_written_generic() {
    let f = "fn f<! E>(g: () -> int ! E, n: int) -> int {
        let a = [1];
        if n > 0 {
            h(|| a[0], n - 1)
        } else {
            g()
        }
    }";
    let h = "fn h<! F>(g: () -> int ! F, n: int) -> int {
        g() + n
    }";
    assert_in_both_orders("", [f, h], "f(|| 1, 2)", 2);
    assert_signature_in_both_orders(
        [f, h],
        "f",
        "fn f<! E>(g: () -> int ! E, n: int) -> int ! (fallible, E)",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn self_recursion_with_a_declared_row_keeps_its_signature() {
    let src = "fn f<! E>(g: () -> int ! (fallible, E), n: int) -> int {
        let a = [1];
        if n > 0 {
            f(|| a[0], n - 1)
        } else {
            g()
        }
    }\n";
    assert_eq!(
        signature(&mut TestSession::new(), src, "f"),
        "fn f<! E>(g: () -> int ! (fallible, E), n: int) -> int ! (fallible, E)"
    );
    assert_val_eq!(TestSession::new().run(&format!("{src}f(|| 1, 2)")), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn helper_with_an_unwritten_callback_effect_stays_generic_in_a_group() {
    let f = "fn f<! E>(g: () -> int ! E, n: int) -> int {
        if n > 0 {
            p(g, n - 1)
        } else {
            0
        }
    }";
    let p = "fn p(k: () -> int, n: int) -> int {
        f(k, 0) + k()
    }";
    assert_in_both_orders("", [f, p], "f(|| 1, 2)", 1);
    assert_signature_in_both_orders(
        [f, p],
        "p",
        "fn p<! e₀>(k: () -> int ! e₀, n: int) -> int ! e₀",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn crossed_programs_with_a_failure_still_fail_at_runtime() {
    let p = "fn p<! E1, E2>(x: () -> int ! E1, y: () -> int ! E2, n: int) -> int {
        if n > 0 {
            q(y, x, n - 1)
        } else {
            x()
        }
    }";
    let q = "fn q<! F1, F2>(x: () -> int ! F1, y: () -> int ! F2, n: int) -> int {
        if n > 0 {
            p(y, x, n - 1)
        } else {
            y()
        }
    }";
    for [first, second] in [[p, q], [q, p]] {
        let mut session = TestSession::new();
        assert_eq!(
            session.fail_run(&format!("{first}\n{second}\np(|| idiv(1, 0), || 1, 2)")),
            SourceFailureKind::DivisionByZero,
        );
    }
}

const APPLY: &str = "fn apply(g) { g() }";

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn returned_function_in_a_group_keeps_its_own_effect_generic() {
    let f = "fn f<! E>(n: int) {
        if n > 0 {
            f(n - 1)
        } else {
            apply
        }
    }";
    assert_in_both_orders("", [APPLY, f], "f(1)(|| idiv(4, 2))", 2);
    // Each use of the result chooses its effect.
    assert_in_both_orders(
        "",
        [APPLY, f],
        "let k = f(1); k(|| 1) + f(1)(|| idiv(4, 2))",
        3,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn returned_function_keeps_its_own_effect_beside_a_used_generic() {
    let f = "fn f<! E>(h: () -> int ! E, n: int) {
        if n > 0 {
            f(h, n - 1)
        } else {
            h();
            apply
        }
    }";
    assert_in_both_orders("", [APPLY, f], "f(|| 1, 1)(|| idiv(4, 2))", 2);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn returned_function_across_a_cycle_keeps_its_own_effect() {
    let f = "fn f<! E>(n: int) {
        if n > 0 {
            h(n - 1)
        } else {
            apply
        }
    }";
    let h = "fn h<! F>(n: int) {
        f(n)
    }";
    assert_in_both_orders(APPLY, [f, h], "f(1)(|| idiv(4, 2)) + h(1)(|| 3)", 5);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn returned_closure_in_a_group_keeps_its_effect() {
    let f = "fn f<! E>(n: int) {
        if n > 0 {
            f(n - 1)
        } else {
            || idiv(1, 0)
        }
    }
    fn run(g: () -> int ! ()) -> int {
        g()
    }";
    let mut session = TestSession::new();
    session.fail_compilation(&format!("{f}\nrun(f(1))"));
    assert_eq!(
        session.fail_run(&format!("{f}\nf(1)()")),
        SourceFailureKind::DivisionByZero
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn returned_closure_takes_the_generic_it_captures() {
    let src = "fn f<! E>(g: () -> int ! E, n: int) {
        if n > 0 {
            f(g, n - 1)
        } else {
            || g() + 1
        }
    }
    fn run(g: () -> int ! ()) -> int {
        g()
    }
    run(f(|| 1, 1))";
    assert_val_eq!(TestSession::new().run(src), int(2));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn given_does_not_serve_a_concrete_query() {
    let src = "fn f<T>(x: T) -> T where T: Num {
        let a: int = 1 + 2;
        if a > 2 {
            x + x
        } else {
            x
        }
    }
    f(3.5)";
    assert_val_eq!(TestSession::new().run(src), float(7.0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn given_serves_an_inferred_query_that_becomes_the_generic() {
    let src = "fn f<T>(x: T) -> T where T: Num {
        let add = |a, b| a + b;
        add(x, x)
    }
    f(3)";
    assert_val_eq!(TestSession::new().run(src), int(6));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn given_serves_an_inferred_query_in_a_group_with_contracts() {
    let src = "fn f<T ! E>(x: T, g: () -> int ! E, n: int) -> T where T: Num {
        let add = |a, b| a + b;
        if n > 0 {
            add(f(x, g, n - 1), x)
        } else {
            g();
            x
        }
    }
    f(3, || 1, 2)";
    assert_val_eq!(TestSession::new().run(src), int(9));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn given_does_not_serve_a_concrete_query_without_an_impl() {
    let mut session = TestSession::new();
    session
        .fail_compilation(
            "struct S { v: int }
            fn f<T>(x: T, s: S) -> T where T: Num {
                let t = s + s;
                x
            }",
        )
        .expect_trait_impl_not_found("Num", &["Self = S"]);
    session
        .fail_compilation(
            "struct S { v: int }
            trait Tr<Self> where Self: Num {
                fn go(x: Self, s: S) -> Self {
                    let t = s + s;
                    x
                }
            }",
        )
        .expect_trait_impl_not_found("Num", &["Self = S"]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_mixes_a_given_with_concrete_and_inferred_queries() {
    let src = "trait Tr<Self> where Self: Num {
        fn go(x: Self) -> Self {
            let k: int = 1 + 2;
            let add = |a, b| a + b;
            add(x, x)
        }
    }
    impl Tr for int {}
    go(3)";
    assert_val_eq!(TestSession::new().run(src), int(6));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn diverging_recursion_with_an_effect_generic_returns_never() {
    let f = "fn f<! E>(n: int) { f(n) }";
    assert_val_eq!(TestSession::new().run(&format!("{f}\n1")), int(1));
    assert_eq!(
        signature(&mut TestSession::new(), f, "f"),
        "fn f(n: int) -> never"
    );
    // The whole cycle diverges, so both functions return never.
    let f = "fn f<! E>(n: int) { h(n) }";
    let h = "fn h(n: int) { f(n) }";
    assert_signature_in_both_orders([f, h], "f", "fn f(n: int) -> never");
    assert_signature_in_both_orders([f, h], "h", "fn h(n: int) -> never");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn group_publishes_the_quantifiers_of_its_contract() {
    let f = "fn f<T ! E>(x, y: T, g: () -> int ! E, n: int) {
        if n > 0 {
            h(x, y, g, n - 1)
        } else {
            (x, y, g())
        }
    }";
    let h = "fn h(x, y, g, n) { f(x, y, g, n) }";
    assert_in_both_orders("", [f, h], "let r = f(true, \"s\", || 3, 2); r.2", 3);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn calls_in_a_group_share_its_types() {
    // `f` returns what `h` returns, so a result `h` discards still has `h`'s type.
    let f = "fn f<! E>() { h(f()) }";
    let h = "fn h<T>(x: T) -> T { f(); x }";
    assert_in_both_orders("", [f, h], "1", 1);
    // The same signatures as without the effect generic.
    assert_signature_in_both_orders([f, h], "f", "fn f<A>() -> A where A: Value");
    assert_signature_in_both_orders([f, h], "h", "fn h<T>(x: T) -> T where T: Value");
    let f = "fn f<! E>(g: () -> int ! E, x, n: int) {
        if n > 0 {
            h(g, x, n - 1)
        } else {
            x
        }
    }";
    let h = "fn h<T>(g, x: T, n: int) -> T {
        if n > 0 {
            f(g, x, n - 1);
            x
        } else {
            x
        }
    }";
    assert_in_both_orders("", [f, h], "f(|| 1, 7, 3)", 7);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_written_effect_in_a_requirement_of_a_group_stays_that_generic() {
    // `E` is inside an input of the requirement, which the body needs as written.
    let src = indoc! { "
        struct Pair<T, F>(T, F)
        trait Check<Self> { fn check(x: Self) -> int; }
        impl<! E> Check for Pair<int, (() -> int ! E)> {
            fn check(x: Pair<int, (() -> int ! E)>) -> int { 7 }
        }
        fn f<T, ! E>(x: T, g: () -> int ! E, n: int) -> int
        where Pair<T, (() -> int ! E)>: Check {
            if n > 0 { f(x, g, n - 1) }
            else { check(Pair(x, g)) }
        }
    " };
    assert_val_eq!(
        TestSession::new().run(&format!("{src}f(1, || 2, 3)")),
        int(7)
    );
    assert_eq!(
        signature(&mut TestSession::new(), src, "f"),
        "fn f<T ! E>(x: T, g: () -> int ! E, n: int) -> int where T: Value, Pair<T, () -> int ! E>: Check"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn the_shapes_of_a_group_do_not_depend_on_the_effects_of_its_types() {
    // The types of the group have one instance, so `h` gets both `Cb<! fallible>` and a pure
    // `Cb`, and `pick` only takes the pure one: seeking the types must not check this.
    let prelude = indoc! { "
        struct Cb<! E>(() -> int ! E)
        trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
        impl<! E> Run for <Self = Cb<! E> |-> ! E = E> {
            fn run(x: Cb<! E>) -> int { x.0() }
        }
        trait Pick<Self> { fn pick(x: Self) -> int; }
        impl<T> Pick for T where T: Run<! E = ()> {
            fn pick(x: T) -> int { 7 }
        }
        fn make() -> Cb<! fallible> { Cb(|| idiv(4, 2)) }
    " };
    let h = "fn h(g, n: int) { if n > 0 { f(|| 1, n - 1); g } else { g } }";
    let f = "fn f<! E>(unused: () -> int ! E, n: int) -> int {
        let failing = h(make(), n);
        pick(h(Cb(|| 1), n)) + run(failing)
    }";
    assert_in_both_orders(prelude, [h, f], "f(|| 1, 1)", 9);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_can_make_two_types_of_a_group_one() {
    // The closure has the effect of `g`, so both calls of `read` are one application of
    // `Read`, with one output: this is only known once effects are inferred.
    let src = indoc! { "
        struct Pair<T, F>(T, F)
        trait Read<Self |-> Out> { fn read(x: Self) -> Out; }
        impl<! E> Read for <Self = Pair<int, (() -> int ! E)> |-> Out = int> {
            fn read(x: Pair<int, (() -> int ! E)>) -> int { x.0 }
        }
        fn f<T, ! E>(x: T, g: () -> int ! E, n: int) {
            let a = read(Pair(x, g));
            let b = read(Pair(x, || g()));
            if n > 0 { f(x, g, n - 1); };
            (a, b)
        }
    " };
    assert_val_eq!(
        TestSession::new().run(&format!("{src}let r = f(3, || 2, 1); r.0 + r.1")),
        int(6)
    );
    assert_eq!(
        signature(&mut TestSession::new(), src, "f"),
        "fn f<T, B ! E>(x: T, g: () -> int ! E, n: int) -> (B, B) where T: Value, B: Value, Pair<T, () -> int ! E>: Read <Out = B>"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_type_that_a_requirement_gives_is_found_across_a_group() {
    // Each function gets its result type from `Read`, and calls the other without using the
    // result: in the first round the other's contract does not say yet what gives that type.
    let prelude = indoc! { "
        struct Pair<T, F>(T, F)
        trait Read<Self |-> Out> { fn read(x: Self) -> Out; }
        impl<! E> Read for <Self = Pair<int, (() -> int ! E)> |-> Out = int> {
            fn read(x: Pair<int, (() -> int ! E)>) -> int { x.0 }
        }
    " };
    let f = "fn f<T, ! E>(x: T, g: () -> int ! E, n: int) {
        if n > 0 { h(x, g, n - 1); };
        read(Pair(x, g))
    }";
    let h = "fn h<U, ! F>(x: U, g: () -> int ! F, n: int) {
        if n > 0 { f(x, g, n - 1); };
        read(Pair(x, g))
    }";
    assert_in_both_orders(prelude, [f, h], "f(3, || 2, 3)", 3);
    // The application that `f` makes and the one that calling `h` needs are one.
    for [first, second] in [[f, h], [h, f]] {
        assert_eq!(
            signature(
                &mut TestSession::new(),
                &format!("{prelude}{first}\n{second}\n"),
                "f"
            ),
            "fn f<T, B ! E>(x: T, g: () -> int ! E, n: int) -> B where T: Value, B: Value, Pair<T, () -> int ! E>: Read <Out = B>"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_application_through_a_called_function_is_the_one_of_the_caller() {
    // Outside a group too: the effect of `g` in the requirement of `h` is that of `f` only
    // once effects are inferred.
    let src = indoc! { "
        struct Pair<T, F>(T, F)
        trait Read<Self |-> Out> { fn read(x: Self) -> Out; }
        impl<! E> Read for <Self = Pair<int, (() -> int ! E)> |-> Out = int> {
            fn read(x: Pair<int, (() -> int ! E)>) -> int { x.0 }
        }
        fn h<U, ! F>(x: U, g: () -> int ! F) { read(Pair(x, g)) }
        fn f<T, ! E>(x: T, g: () -> int ! E) { h(x, g); read(Pair(x, g)) }
    " };
    assert_val_eq!(TestSession::new().run(&format!("{src}f(3, || 2)")), int(3));
    assert_eq!(
        signature(&mut TestSession::new(), src, "f"),
        "fn f<T, B ! E>(x: T, g: () -> int ! E) -> B where T: Value, B: Value, Pair<T, () -> int ! E>: Read <Out = B>"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_field_read_through_a_call_of_a_group_has_the_effect_of_its_declaration() {
    // The recursive call needs the field `kind` with an effect of its own, which is the one of
    // the body's own read, not all that the call performs.
    let src = indoc! { "
        fn f<! E>(tok, a: [int], g: () -> int ! E, n: int) -> int {
            if n == 0 {
                tok.kind + a[0] + g()
            } else {
                f(tok, a, g, n - 1)
            }
        }
    " };
    assert_val_eq!(
        TestSession::new().run(&format!("{src}f({{ kind: 1 }}, [2], || 3, 2)")),
        int(6)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_type_that_only_requirements_of_a_group_name_is_not_the_body_to_choose() {
    // The types of the payloads of `Some` are in no signature: the function is generic over
    // them, and its body does not default them or close the variants.
    let src = indoc! { "
        fn inspect<! E>(n, left, right, g: () -> bool ! E) {
            if n == 0 {
                match left {
                    Some(number) => match right {
                        Some(flag) => number == 1 and flag and g(),
                        _ => false,
                    },
                    _ => false,
                }
            } else {
                inspect(n - 1, left, right, g)
            }
        }
        if inspect(1, Some(1), Some(true), || true) {
            1
        } else {
            0
        }
    " };
    assert_val_eq!(TestSession::new().run(src), int(1));
    // The same for the outputs of a trait: the iterator of `a` and its items.
    let src = indoc! { "
        fn r<! E>(a, n, g: () -> int ! E) {
            let mut i = iter(a);
            let x = next(i);
            if n == 0 {
                g()
            } else {
                item(x, a, n - 1, g)
            }
        }
        fn item(x, a, n, g) {
            r(a, n, g)
        }
        r([1, 2], 2, || 5)
    " };
    assert_val_eq!(TestSession::new().run(src), int(5));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn the_contracts_of_a_group_do_not_grow_with_its_unrolling() {
    // Each use of `f` as a value needs `Num` for its type, at an effect that nothing
    // determines: it takes its least solution, so these requirements are one. With an effect
    // of its own for each, every copy of `f` would bring those of the copies that it uses,
    // without end.
    for src in [
        "fn f<! E>(a) { f + 0 == f + 0 }",
        "fn f<! E>(a) { f + 0 == h + 0 }\nfn h(a) { f == f + f }",
        "fn result<! E>(mut a) { a.a.a.c() != result and result + 0 == item + 0 + 1 + 0 }\nfn item<z, c, result>(a) { result == result + result + result + item }",
    ] {
        assert_val_eq!(
            TestSession::new().run(&format!("{src}\n0")),
            int(0),
            "{src}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_group_without_a_finite_contract_is_rejected() {
    // `step` gives a callback whose effect is the output of `Tr` for the effect of the one it
    // gets, and `f` passes it to itself: unrolled, `f` needs `Tr` at the effect of `g`, at the
    // output of that, and so on without end. Its contract grows until the bound on rounds.
    let prelude = "struct Pair<A, B>(A, B)
trait Tr<Self |-> ! Out> {
    fn tr(x: Self) -> int ! Out;
}
impl<! E> Tr for <Self = Pair<int, (() -> int ! E)> |-> ! Out = E> {
    fn tr(x: Pair<int, (() -> int ! E)>) -> int { (x.1)() }
}
fn step<T, ! E, O>(x: T, g: () -> int ! E) -> (() -> int ! O)
where Pair<T, (() -> int ! E)>: Tr<! Out = O> {
    || tr(Pair(x, g))
}";
    let body = "{
    if n == 0 {
        0
    } else {
        f(x, step(x, g), n - 1)
    }
}";
    TestSession::new()
        .fail_compilation(&format!(
            "{prelude}\nfn f<T>(x: T, g, n: int) -> int {body}\nf(3, || 1, 2)"
        ))
        .expect_recursive_group_body_does_not_fit("f");
    // The requirement written with its output equal to its input is a finite contract.
    assert_val_eq!(
        TestSession::new().run(&format!(
            "{prelude}
fn f<T, ! E>(x: T, g: () -> int ! E, n: int) -> int
where Pair<T, (() -> int ! E)>: Tr<! Out = E> {body}
f(3, || 1, 2)"
        )),
        int(0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_effect_that_only_an_inferred_requirement_names_takes_its_least_solution() {
    // Each use of `f` as a value needs `Conv` for its type, at effects that nothing
    // determines: they are pure, and the requirement is one however many times `f` is
    // unrolled.
    let conv = "struct Wrap<T>(T)
trait Conv<Self |-> O> { fn conv(x: Self) -> O; }
impl<! E, F> Conv for <Self = Wrap<((int, () -> int ! E) -> int ! F)> |-> O = int> {
    fn conv(x: Wrap<((int, () -> int ! E) -> int ! F)>) -> int { 0 }
}";
    let f = "fn f<T>(a: T, g: () -> int) -> int {
    let u = conv(Wrap(f));
    g()
}";
    for src in [format!("{conv}\n{f}"), format!("{f}\n{conv}")] {
        assert_val_eq!(
            TestSession::new().run(&format!("{src}\nf(0, || 7)")),
            int(7),
            "{src}"
        );
        assert_eq!(
            signature(&mut TestSession::new(), &src, "f"),
            "fn f<T, B ! e₀>(a: T, g: () -> int ! e₀) -> int ! e₀ \
             where B: Value, Wrap<(T, () -> int) -> int>: Conv <O = B>",
            "{src}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn the_requirements_of_a_group_keep_the_effects_of_its_signature_apart() {
    // The two requirements of `f` differ only by the effects of its two callbacks, which its
    // callers choose: they stay two, as without the recursive call.
    let prelude = "struct Cb<T>(T)
trait Select<Self, Other> {
    fn select(x: Self, y: Other) -> int;
}
impl<! E> Select for <Self = int, Other = Cb<(() -> int ! E)>> {
    fn select(x: int, y: Cb<(() -> int ! E)>) -> int { x }
}";
    let header = "fn f<T, ! E, F>(x: T, n: int, g: () -> int ! E, h: () -> int ! F) -> int";
    let selections = [
        "select(x, Cb(g)) + select(x, Cb(h))",
        "select(x, Cb(h)) + select(x, Cb(g))",
    ];
    for (index, selection) in selections.into_iter().enumerate() {
        let alone = format!("{header} {{\n    {selection}\n}}");
        let recursive = format!(
            "{header} {{
    if n == 0 {{
        {selection}
    }} else {{
        f(x, n - 1, g, h)
    }}
}}"
        );
        for function in [alone, recursive] {
            let src = format!("{prelude}\n{function}\n");
            assert_val_eq!(
                TestSession::new().run(&format!("{src}f(3, 1, || 1, || idiv(4, 2))")),
                int(6),
                "{function}"
            );
            if index == 0 {
                assert_eq!(
                    signature(&mut TestSession::new(), &src, "f"),
                    "fn f<T ! E, F>(x: T, n: int, g: () -> int ! E, h: () -> int ! F) -> int \
                     where Select <Self = T, Other = Cb<() -> int ! E>>, \
                     Select <Self = T, Other = Cb<() -> int ! F>>",
                    "{function}"
                );
            }
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn the_requirements_of_a_group_keep_the_effects_that_other_requirements_determine_apart() {
    // The two `Select` requirements of `f` differ only by effects that no signature names,
    // and that the caller's `T` determines, as the outputs of `First` and of `Second`.
    let prelude = "struct Pair<A, B>(A, B)
trait Select<Self> {}
impl<! E> Select for Pair<int, (() -> int ! E)> {}
trait First<Self |-> ! E>
where Pair<Self, (() -> int ! E)>: Select {
    fn first(x: Self) -> int;
}
trait Second<Self |-> ! E>
where Pair<Self, (() -> int ! E)>: Select {
    fn second(x: Self) -> int;
}
impl First for <Self = int |-> ! E = ()> {
    fn first(x: int) -> int { x }
}
impl Second for <Self = int |-> ! E = (fallible)> {
    fn second(x: int) -> int { x }
}";
    let header = "fn f<T, ! Unused>(x: T, n: int) -> int";
    for sum in ["first(x) + second(x)", "second(x) + first(x)"] {
        let alone = format!("{header} {{\n    {sum}\n}}");
        let recursive = format!(
            "{header} {{
    if n == 0 {{
        {sum}
    }} else {{
        f(x, n - 1)
    }}
}}"
        );
        for function in [alone, recursive] {
            assert_val_eq!(
                TestSession::new().run(&format!("{prelude}\n{function}\nf(3, 1)")),
                int(6),
                "{function}"
            );
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_effect_generic_that_no_call_determines_is_ambiguous() {
    let prelude = "struct Pair<A, B>(A, B)
trait Select<Self> {}
impl<! E> Select for Pair<int, (() -> int ! E)> {}
trait Run<Self |-> ! E> {
    fn run(x: Self) -> int ! E;
}
impl Run for <Self = int |-> ! E = (fallible)> {
    fn run(x: int) -> int { idiv(4, x) }
}";
    // No parameter of `one` has the effect `E`, and no output of a trait gives it: no call
    // says what it is.
    TestSession::new()
        .fail_compilation(&format!(
            "{prelude}
fn one<T, ! E>(x: T) -> int
where Pair<T, (() -> int ! E)>: Select {{ 3 }}
one(3)"
        ))
        .expect_ambiguous_effect_generic("E");
    // An output of a trait is determined by the types of the caller, and so is what its
    // effect is an input of.
    assert_val_eq!(
        TestSession::new().run(&format!(
            "{prelude}
fn two<T, ! E>(x: T) -> int
where T: Run<! E = E>, Pair<T, (() -> int ! E)>: Select {{ 3 }}
two(3)"
        )),
        int(3)
    );
    // Outputs that only give the inputs of one another, in a circle, determine nothing.
    // The first requirement written is the one reported.
    for (requirements, name) in [
        (
            "Pair<T, (() -> int ! E)>: R<! O = F>, Pair<T, (() -> int ! F)>: S<! O = E>",
            "E",
        ),
        (
            "Pair<T, (() -> int ! F)>: S<! O = E>, Pair<T, (() -> int ! E)>: R<! O = F>",
            "F",
        ),
    ] {
        TestSession::new()
            .fail_compilation(&format!(
                "struct Pair<A, B>(A, B)
trait R<Self |-> ! O> {{}}
trait S<Self |-> ! O> {{}}
fn f<T, ! E, F>(x: T) -> int
where {requirements} {{ 7 }}
0"
            ))
            .expect_ambiguous_effect_generic(name);
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_effect_travels_around_a_long_cycle_in_any_order() {
    // The failure of `f8` reaches `f0` after one round for each function between them.
    let mut functions = vec![
        "fn f0<! E>(g: () -> int ! E, n: int) -> int { if n == 0 { g() } else { f1(g, n - 1) } }"
            .to_string(),
    ];
    for index in 1..8 {
        functions.push(format!(
            "fn f{index}(g, n: int) -> int {{ if n == 0 {{ g() }} else {{ f{}(g, n - 1) }} }}",
            index + 1
        ));
    }
    functions.push(
        "fn f8(g, n: int) -> int { if n == 0 { idiv(4, 2) } else { f0(g, n - 1) } }".to_string(),
    );
    let reversed = functions.iter().rev().cloned().collect::<Vec<_>>();
    for functions in [functions, reversed] {
        let src = functions.join("\n");
        assert_val_eq!(
            TestSession::new().run(&format!("{src}\nf0(|| 1, 0) + f0(|| 1, 8)")),
            int(3)
        );
        assert_eq!(
            signature(&mut TestSession::new(), &src, "f0"),
            "fn f0<! E>(g: () -> int ! E, n: int) -> int ! (fallible, E)"
        );
        for name in ["f1", "f4", "f8"] {
            assert_eq!(
                signature(&mut TestSession::new(), &src, name),
                format!("fn {name}<! e₀>(g: () -> int ! e₀, n: int) -> int ! (fallible, e₀)")
            );
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_inferred_function_of_a_group_takes_each_use_of_it_apart() {
    // `s` calls `r` with a callback that can fail and with its own `f1`: two instances of the
    // effect of `r`'s second parameter.
    let r = "fn r(f0, f1, n: int) -> int {
        if n > 0 {
            s(f1, f1, n - 1)
        } else {
            f1(n)
        }
    }";
    let s = "fn s<! E0, E1>(f0: (int) -> int ! E0, f1: (int) -> int ! E1, n: int) -> int {
        if n > 0 {
            r(f0, |z| idiv(z, 1), n - 1) + r(f0, f1, n - 1)
        } else {
            f1(n)
        }
    }";
    assert_in_both_orders("", [r, s], "s(|x| x, |x| x + 1, 2)", 1);
    assert_signature_in_both_orders(
        [r, s],
        "r",
        "fn r<! e₀, e₁>(f0: (int) -> int ! e₀, f1: (int) -> int ! e₁, n: int) -> int ! (fallible, e₁)",
    );
    assert_signature_in_both_orders(
        [r, s],
        "s",
        "fn s<! E0, E1>(f0: (int) -> int ! E0, f1: (int) -> int ! E1, n: int) -> int ! (fallible, E1)",
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
    let CompilationErrorImpl::TraitOutputEffectMismatch {
        trait_ref, span, ..
    } = &*error
    else {
        panic!("unexpected diagnostic: {error:?}")
    };
    assert_eq!(trait_ref, "Run");
    let call = source.rfind("serialize(").expect("the program has a call");
    assert_eq!(span.start_usize(), call, "{error:?}");
}

/// The bound `Run<! E = ()>` of a callee, a selected impl or a trait meets a written generic of
/// the query: the diagnostic names the trait, its output effect and the written generic.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_effect_output_bound_met_by_a_written_generic_names_the_trait_and_the_generic() {
    for (program, generic) in [
        (
            "fn p<T>(x: T) -> int where T: Run<! E = ()> { run(x) }
            fn f<! G>(g: () -> int ! G) -> int { p(Cb(g)) }",
            "G",
        ),
        (
            "struct Wrap<T>(T)
            impl<T> Serialize for Wrap<T> where T: Run<! E = ()> {
                fn serialize(x: Wrap<T>) -> DataValue { serialize(run(x.0)) }
            }
            fn f<! G>(g: () -> int ! G) -> DataValue { serialize(Wrap(Cb(g))) }",
            "G",
        ),
        (
            "trait Twice<Self> where Self: Run<! E = ()> {
                fn twice(x: Self) -> int { run(x) + run(x) }
            }
            impl<! G> Twice for Cb<! G> {}",
            "G",
        ),
        // The generic reaches the application through an inferred effect.
        (
            "fn p<T>(x: T) -> int where T: Run<! E = ()> { run(x) }
            fn f<! G>(g: () -> int ! G) -> int { let both = [|| 1, g]; p(Cb(both[0])) }",
            "G",
        ),
    ] {
        let error = TestSession::new().fail_compilation(&format!("{CALL_THROUGH_TRAIT}{program}"));
        let CompilationErrorImpl::TraitOutputEffectMismatch {
            trait_ref,
            output,
            source,
            target,
            names,
            ..
        } = &*error
        else {
            panic!("unexpected diagnostic for {program}: {error:?}")
        };
        assert_eq!(trait_ref, "Run", "{program}");
        assert_eq!(output.as_str(), "E", "{program}");
        assert_eq!(
            NamedEffectRow(source, names).to_string(),
            generic,
            "{program}"
        );
        assert!(target.is_empty(), "{program}: {error:?}");
    }
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

/// A callback wrapped for [`Run`], whose effect is the callback's.
const RUN_PRELUDE: &str = indoc! { r#"
struct Cb<T>(T)
trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
impl<! E> Run for <Self = Cb<(() -> int ! E)> |-> ! E = E> {
 fn run(x: Cb<(() -> int ! E)>) -> int { x.0() }
}
"# };

/// A custom `Value` impl for `name<T>` with `prerequisites` besides `T: Value`, whose
/// `to_string` returns `name` without running anything.
fn named_value_impl(name: &str, prerequisites: &str) -> String {
    format!(
        "struct {name}<T>(T)
impl<T> Value for {name}<T> where T: Value, {prerequisites} {{
 fn eq(x: {name}<T>, y: {name}<T>) -> bool {{ true }}
 fn to_string(x: {name}<T>) -> string {{ \"{name}\" }}
 fn hash(x: {name}<T>, state: &mut hasher) {{}}
 fn clone(x: {name}<T>) -> {name}<T> {{ {name}(x.0) }}
 fn drop(x: &mut {name}<T>) {{}}
}}
"
    )
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_custom_value_impl_restricts_an_inferred_callback_effect() {
    let prelude = format!(
        "{RUN_PRELUDE}{}",
        named_value_impl("Wrap", "T: Run<! E = ()>")
    );
    // Directly, and through compiler-provided containers.
    for term in [
        "Wrap(Cb(g))",
        "(Wrap(Cb(g)), 1)",
        "{ a: Wrap(Cb(g)) }",
        "Some(Wrap(Cb(g)))",
        "[Wrap(Cb(g))]",
        "({ a: (Wrap(Cb(g)),) },)",
    ] {
        let src = format!("{prelude}fn f(g: () -> int) -> string {{ to_string({term}) }}\n");
        let mut session = TestSession::new();
        session.allow_unsafe();
        assert_eq!(
            signature(&mut session, &src, "f"),
            "fn f(g: () -> int) -> string",
            "{term}"
        );
        let mut session = TestSession::new();
        session.allow_unsafe();
        session.fail_compilation(&format!("{src}f(|| idiv(1, 0))"));
    }
    let mut session = TestSession::new();
    session.allow_unsafe();
    assert_val_eq!(
        session.run(&format!(
            "{prelude}fn f(g: () -> int) -> string {{ to_string(Wrap(Cb(g))) }}\nf(|| 5)"
        )),
        string("Wrap")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_inapplicable_custom_value_impl_does_not_restrict_effects() {
    // `Missing` has no impl, so the custom impl does not apply and `Value` is derived.
    let src = format!(
        "{RUN_PRELUDE}trait Missing<Self> {{ fn missing(x: Self) -> int; }}\n{}\
         fn h(g: () -> int) -> string {{ to_string(Wrap(Cb(g))) }}\n",
        named_value_impl("Wrap", "T: Missing, T: Run<! E = ()>")
    );
    let mut session = TestSession::new();
    session.allow_unsafe();
    assert_eq!(
        signature(&mut session, &src, "h"),
        "fn h<! e₀>(g: () -> int ! e₀) -> string"
    );
    let mut session = TestSession::new();
    session.allow_unsafe();
    assert_val_eq!(
        session.run(&format!("{src}let a = [1];\nh(|| a[0])")),
        string("Wrap (Cb (<function>))")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_custom_value_impls_restrict_effects_across_the_cycle() {
    // The restriction is on the far side of the cycle from the call.
    let left = named_value_impl("Left", "Right<T>: Value");
    let right = named_value_impl("Right", "T: Run<! E = ()>, Left<T>: Value");
    let f = "fn f(g: () -> int) -> string { to_string(Left(Cb(g))) }\n";
    for [first, second] in [[&left, &right], [&right, &left]] {
        let src = format!("{RUN_PRELUDE}{first}{second}{f}");
        let mut session = TestSession::new();
        session.allow_unsafe();
        assert_eq!(
            signature(&mut session, &src, "f"),
            "fn f(g: () -> int) -> string"
        );
        let mut session = TestSession::new();
        session.allow_unsafe();
        assert_val_eq!(session.run(&format!("{src}f(|| 5)")), string("Left"));
        let mut session = TestSession::new();
        session.allow_unsafe();
        session.fail_compilation(&format!("{src}f(|| idiv(1, 0))"));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_recursive_type_carries_the_restriction_of_a_custom_value_impl() {
    // The derived `Value` of `Chain` needs the one of `Wrap` at each link, and its own.
    let prelude = format!(
        "{RUN_PRELUDE}struct Wrap<T>(T)
impl<T> Value for Wrap<T> where T: Value, T: Run<! E = ()> {{
 fn eq(x: Wrap<T>, y: Wrap<T>) -> bool {{ run(x.0) == run(y.0) }}
 fn to_string(x: Wrap<T>) -> string {{ to_string(run(x.0)) }}
 fn hash(x: Wrap<T>, state: &mut hasher) {{}}
 fn clone(x: Wrap<T>) -> Wrap<T> {{ Wrap(x.0) }}
 fn drop(x: &mut Wrap<T>) {{}}
}}
enum Chain<T> {{ End, Link(Wrap<T>, Chain<T>) }}
"
    );
    for (body, expected) in [
        (
            "to_string(Chain::Link(Wrap(Cb(g)), Chain::Link(Wrap(Cb(g)), Chain::End)))",
            string("Chain::Link (5, Chain::Link (5, Chain::End))"),
        ),
        (
            "let a = Chain::Link(Wrap(Cb(g)), Chain::End);\n to_string(a == a)",
            string("true"),
        ),
    ] {
        let src = format!("{prelude}fn f(g: () -> int) -> string {{ {body} }}\n");
        let mut session = TestSession::new();
        session.allow_unsafe();
        assert_eq!(
            signature(&mut session, &src, "f"),
            "fn f(g: () -> int) -> string",
            "{body}"
        );
        let mut session = TestSession::new();
        session.allow_unsafe();
        assert_val_eq!(session.run(&format!("{src}f(|| 5)")), expected);
        let mut session = TestSession::new();
        session.allow_unsafe();
        session.fail_compilation(&format!("{src}f(|| idiv(1, 0))"));
    }
    // Taking a chain apart drops the rest of it, which needs the impl too.
    let src = format!(
        "{prelude}fn first<T>(c: Chain<T>, other: T) -> T {{
    match c {{
        Link(w, rest) => w.0,
        End => other,
    }}
}}
fn f(g: () -> int) -> int {{ run(first(Chain::Link(Wrap(Cb(g)), Chain::End), Cb(g))) }}
"
    );
    let mut session = TestSession::new();
    session.allow_unsafe();
    assert_eq!(
        signature(&mut session, &src, "first"),
        "fn first<T>(c: Chain<T>, other: T) -> T where T: Value, Wrap<T>: Value"
    );
    assert_eq!(
        signature(&mut session, &src, "f"),
        "fn f(g: () -> int) -> int"
    );
    let mut session = TestSession::new();
    session.allow_unsafe();
    assert_val_eq!(session.run(&format!("{src}f(|| 5)")), int(5));
    let mut session = TestSession::new();
    session.allow_unsafe();
    session.fail_compilation(&format!("{src}f(|| idiv(1, 0))"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fixed_output_effects_of_prerequisites_are_upper_bounds() {
    // A pure callback fits a bound allowing failure.
    let mut session = TestSession::new();
    session.allow_unsafe();
    assert_val_eq!(
        session.run(&format!(
            "{RUN_PRELUDE}{}to_string(Wrap(Cb(|| 5)))",
            named_value_impl("Wrap", "T: Run<! E = (fallible)>")
        )),
        string("Wrap")
    );
    // Two bounds on one application need not be equal, whether they meet in one function or
    // around a cycle of impls: a pure callback fits both.
    for (impls, term, expected) in [
        (
            format!(
                "{}{}",
                named_value_impl("A", "T: Run<! E = (fallible)>"),
                named_value_impl("B", "T: Run<! E = ()>")
            ),
            "let a = to_string(A(Cb(g)));\n let b = to_string(B(Cb(g)));\n f\"{a}{b}\"",
            "AB",
        ),
        (
            format!(
                "{}{}",
                named_value_impl("Left", "T: Run<! E = (fallible)>, Right<T>: Value"),
                named_value_impl("Right", "T: Run<! E = ()>, Left<T>: Value")
            ),
            "to_string(Left(Cb(g)))",
            "Left",
        ),
    ] {
        let src = format!("{RUN_PRELUDE}{impls}fn f(g: () -> int) -> string {{ {term} }}\n");
        let mut session = TestSession::new();
        session.allow_unsafe();
        assert_eq!(
            signature(&mut session, &src, "f"),
            "fn f(g: () -> int) -> string",
            "{term}"
        );
        let mut session = TestSession::new();
        session.allow_unsafe();
        assert_val_eq!(session.run(&format!("{src}f(|| 5)")), string(expected));
    }
    // The same holds for other traits.
    assert_val_eq!(
        TestSession::new().run(&format!(
            "{RUN_PRELUDE}struct Wrap<T>(T)
trait Show<Self> {{ fn show(x: Self) -> string; }}
impl<T> Show for Wrap<T> where T: Run<! E = (fallible)> {{ fn show(x: Wrap<T>) -> string {{ \"a\" }} }}
trait Tell<Self> {{ fn tell(x: Self) -> string; }}
impl<T> Tell for Wrap<T> where T: Run<! E = ()> {{ fn tell(x: Wrap<T>) -> string {{ \"b\" }} }}
let w = Wrap(Cb(|| 5));
let a = show(w);
let b = tell(w);
f\"{{a}}{{b}}\""
        )),
        string("ab")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_imported_custom_value_impl_restricts_an_inferred_callback_effect() {
    let mut session = TestSession::new();
    session.allow_unsafe();
    let lib = RUN_PRELUDE
        .replace("struct Cb", "pub struct Cb")
        .replace("trait Run", "pub trait Run")
        + &named_value_impl("Wrap", "T: Run<! E = ()>").replace("struct Wrap", "pub struct Wrap");
    session
        .try_compile_module("lib", &lib)
        .unwrap_or_else(|error| panic!("{error:?}"));
    let src = "fn f(g: () -> int) -> string { to_string(lib::Wrap(lib::Cb(g))) }\n";
    assert_eq!(
        signature(&mut session, src, "f"),
        "fn f(g: () -> int) -> string"
    );
    assert_val_eq!(session.run(&format!("{src}f(|| 5)")), string("Wrap"));
    session.fail_compilation(&format!("{src}f(|| idiv(1, 0))"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fixed_output_effect_bounds_combine_whatever_their_order() {
    // Performed effects fit every bound, so the bounds intersect: here `run` is pure.
    let run = |impl_effect: &str, bounds: [&str; 2]| {
        format!(
            "trait Run<Self |-> ! E> {{ fn run(x: Self) -> int ! E; }}
impl Run for <Self = int |-> ! E = {impl_effect}> {{ fn run(x: int) -> int {{ idiv(10, x) }} }}
fn f<T>(x: T) -> int where T: Run<! E = {}>, T: Run<! E = {}> {{ run(x) }}
fn pure(g: () -> int ! ()) -> int {{ g() }}
pure(|| f(5))",
            bounds[0], bounds[1]
        )
    };
    for bounds in [["(fallible)", "()"], ["()", "(fallible)"]] {
        assert_val_eq!(
            TestSession::new().run(&run("()", bounds).replace("idiv(10, x)", "x")),
            int(5),
            "{bounds:?}"
        );
        // An implementation that fails does not fit the pure bound.
        TestSession::new().fail_compilation(&run("(fallible)", bounds));
    }
    // Received effects include every bound, so the bounds unite: a failing callback is accepted.
    for bounds in [["(fallible)", "()"], ["()", "(fallible)"]] {
        assert_val_eq!(
            TestSession::new().run(&format!(
                "trait Apply<Self |-> ! E> {{ fn apply(x: Self, g: () -> int ! E) -> int; }}
impl<! E> Apply for <Self = int |-> ! E = E> {{ fn apply(x: int, g: () -> int ! E) -> int {{ x }} }}
fn f<T>(x: T) -> int where T: Apply<! E = {}>, T: Apply<! E = {}> {{
    let a = [1];
    apply(x, || a[0])
}}
let n: int = 5;
f(n)",
                bounds[0], bounds[1]
            )),
            int(5),
            "{bounds:?}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_default_method_may_perform_the_output_effect_of_its_trait() {
    // Directly, and through a function bounded by the trait.
    let step = |twice: &str, via: &str| {
        format!(
            "struct Cb<T>(T)
fn forward<T, ! F>(x: T) -> int where T: Step<! E = F> {{ step(x) }}
trait Step<Self |-> ! E> {{
    fn step(x: Self) -> int ! E;
    fn twice(x: Self) -> int{twice}
    fn via(x: Self) -> int{via}
}}
impl<! E> Step for <Self = Cb<(() -> int ! E)> |-> ! E = E> {{
    fn step(x: Cb<(() -> int ! E)>) -> int {{ x.0() }}
}}
fn pure(k: () -> int ! ()) -> int {{ k() }}
fn f(g: () -> int) -> int {{ twice(Cb(g)) + via(Cb(g)) }}
"
        )
    };
    let src = step(" ! E { step(x) + step(x) }", " ! E { forward(x) }");
    assert_eq!(
        signature(&mut TestSession::new(), &src, "f"),
        "fn f<! e₀>(g: () -> int ! e₀) -> int ! e₀"
    );
    assert_val_eq!(
        TestSession::new().run(&format!("{src}pure(|| f(|| 2))")),
        int(6)
    );
    for call in [
        "twice(Cb(|| idiv(1, 0)))",
        "via(Cb(|| idiv(1, 0)))",
        "f(|| idiv(1, 0))",
    ] {
        TestSession::new().fail_compilation(&format!("{src}pure(|| {call})"));
        assert_eq!(
            TestSession::new().fail_run(&format!("{src}{call}")),
            SourceFailureKind::DivisionByZero
        );
    }
    // A default method cannot perform more than it declares, nor declare less than it performs.
    for (twice, via) in [
        (" { step(x) }", " ! E { forward(x) }"),
        (" ! E { step(x) }", " { forward(x) }"),
        (" ! E { step(x) + idiv(1, 0) }", " ! E { forward(x) }"),
    ] {
        TestSession::new().fail_compilation(&format!("{}1", step(twice, via)));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fixed_output_effect_bounds_of_a_trait_combine_in_its_default_methods() {
    // The bounds are the default method's givens: `run` is pure, the callback may fail.
    let program = |impl_effect: &str, run_body: &str, bounds: [&str; 2]| {
        format!(
            "trait Run<Self |-> ! E> {{ fn run(x: Self) -> int ! E; }}
impl Run for <Self = int |-> ! E = {impl_effect}> {{ fn run(x: int) -> int {{ {run_body} }} }}
trait Apply<Self |-> ! E> {{ fn apply(x: Self, g: () -> int ! E) -> int; }}
impl<! E> Apply for <Self = int |-> ! E = E> {{ fn apply(x: int, g: () -> int ! E) -> int {{ x }} }}
trait Tr<Self>
where Self: Run<! E = {0}>, Self: Run<! E = {1}>, Self: Apply<! E = {0}>, Self: Apply<! E = {1}> {{
    fn go(x: Self) -> int {{
        let a = [1];
        run(x) + apply(x, || a[0])
    }}
}}
impl Tr for int {{}}
go(5)",
            bounds[0], bounds[1]
        )
    };
    for bounds in [["(fallible)", "()"], ["()", "(fallible)"]] {
        assert_val_eq!(
            TestSession::new().run(&program("()", "x", bounds)),
            int(10),
            "{bounds:?}"
        );
        // An implementation that fails does not fit the pure bound.
        TestSession::new().fail_compilation(&program("(fallible)", "idiv(10, x)", bounds));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_given_bound_fits_a_callees_fixed_bound_by_polarity() {
    // A default method's given is evidence; a helper's `where` clause is a bound it must fit.
    let program = |method: &str, given: &str, helper: &str| {
        format!(
            "trait Run<Self |-> ! E> {{ fn run(x: Self) -> int ! E; }}
impl Run for <Self = int |-> ! E = ()> {{ fn run(x: int) -> int {{ x }} }}
trait Apply<Self |-> ! E> {{ fn apply(x: Self, g: () -> int ! E) -> int; }}
impl<! E> Apply for <Self = int |-> ! E = E> {{ fn apply(x: int, g: () -> int ! E) -> int {{ x }} }}
trait Both<Self |-> ! E> {{ fn both(x: Self, g: () -> int ! E) -> int ! E; }}
impl<! E> Both for <Self = int |-> ! E = E> {{ fn both(x: int, g: () -> int ! E) -> int {{ x }} }}
fn helper_run<T>(x: T) -> int where T: Run<! E = {helper}> {{ run(x) }}
fn helper_apply<T>(x: T) -> int where T: Apply<! E = {helper}> {{ apply(x, || 1) }}
fn helper_both<T>(x: T) -> int where T: Both<! E = {helper}> {{ both(x, || 1) }}
trait Tr<Self> where Self: {method}<! E = {given}> {{
    fn go(x: Self) -> int ! fallible {{ helper_{}(x) }}
}}
impl Tr for int {{}}
go(5)",
            method.to_lowercase()
        )
    };
    let (pure, fallible) = ("()", "(fallible)");
    for (method, given, helper, accepted) in [
        // Performed: evidence that does not fail fits a bound permitting failure, not conversely.
        ("Run", pure, fallible, true),
        ("Run", fallible, pure, false),
        // Received: evidence accepting failing callbacks fits a bound on pure ones, not conversely.
        ("Apply", fallible, pure, true),
        ("Apply", pure, fallible, false),
        // Invariant: the bounds must be equal.
        ("Both", fallible, fallible, true),
        ("Both", pure, fallible, false),
    ] {
        let src = program(method, given, helper);
        if accepted {
            assert_val_eq!(
                TestSession::new().run(&src),
                int(5),
                "{method} {given} {helper}"
            );
        } else {
            TestSession::new().fail_compilation(&src);
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_literal_defaults_through_an_impl_with_effect_parameters() {
    // An impl with an effect parameter is a blanket impl; it still lets `5` default to `int`.
    for call in ["apply(5, || 1)", "f(5)"] {
        assert_val_eq!(
            TestSession::new().run(&format!(
                "trait Apply<Self |-> ! E> {{ fn apply(x: Self, g: () -> int ! E) -> int; }}
impl<! E> Apply for <Self = int |-> ! E = E> {{ fn apply(x: int, g: () -> int ! E) -> int {{ x }} }}
fn f<T>(x: T) -> int where T: Apply<! E = (fallible)> {{ apply(x, || 1) }}
{call}"
            )),
            int(5),
            "{call}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_imported_impl_builds_private_evidence_from_its_consumers_requirements() {
    // Private Check evidence is discharged in lib; its public Run requirement is supplied
    // by the consumer. An arbitrary T: PrivateTrait could not be an exported contract.
    let lib = RUN_PRELUDE
        .replace("struct Cb", "pub struct Cb")
        .replace("trait Run", "pub trait Run")
        + "trait Check<Self> {}\nimpl<T> Check for [T] where T: Run<! E = ()> {}\n"
        + &named_value_impl("Wrap", "[T]: Check").replace("struct Wrap", "pub struct Wrap")
        + "pub trait Show<Self> { fn show(x: Self) -> string; }
impl<T> Show for Wrap<T> where [T]: Check { fn show(x: Wrap<T>) -> string { \"shown\" } }
";
    for (call, expected) in [
        ("to_string(lib::Wrap(lib::Cb(g)))", "Wrap"),
        ("lib::Show::show(lib::Wrap(lib::Cb(g)))", "shown"),
    ] {
        let mut session = TestSession::new();
        session.allow_unsafe();
        session
            .try_compile_module("lib", &lib)
            .unwrap_or_else(|error| panic!("{error:?}"));
        let src = format!("fn f(g: () -> int) -> string {{ {call} }}\n");
        assert_eq!(
            signature(&mut session, &src, "f"),
            "fn f(g: () -> int) -> string",
            "{call}"
        );
        assert_val_eq!(session.run(&format!("{src}f(|| 5)")), string(expected));
        session.fail_compilation(&format!("{src}f(|| idiv(1, 0))"));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn accessors_of_a_subscript_keep_the_same_written_effect_names() {
    // `E` is not used, so `F` comes first, in each accessor.
    let src = indoc! { "
        subscript held<! E, F>(slot: &mut (() -> int ! F), x: () -> int) -> (() -> int ! F) {
            ref { if false { slot->[held](x) = slot }; slot }
            mut { if false { let z = slot->[held](x); z(); }; slot }
        }
        let mut slot = || 5;
        let f = slot->[held](|| idiv(1, 0));
        f()
    " };
    let mut session = TestSession::new();
    session.allow_experimental();
    let module_id = session.compile(src).module_id;
    let compiler_session = session.session();
    let module = compiler_session.expect_fresh_module(module_id);
    let rendered = module.format_with(&compiler_session.modules()).to_string();
    let accessors: Vec<_> = rendered
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with("fn held::"))
        .collect();
    assert_eq!(accessors.len(), 2, "{rendered}");
    for accessor in accessors {
        assert!(
            accessor.contains(
                "<! F, e₁>(slot: &mut () -> int ! F, x: () -> int ! e₁) -> place () -> int ! F"
            ),
            "{accessor}"
        );
    }
    let mut session = TestSession::new();
    session.allow_experimental();
    assert_val_eq!(session.run(src), int(5));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_effect_left_unwritten_in_an_annotation_is_not_a_written_generic() {
    // In a local annotation: the closure may fail, whatever `E` is.
    assert_val_eq!(
        TestSession::new().run(indoc! { "
            fn f<! E>(a: () -> int ! E, n: int) -> int {
                let y: () -> int = || idiv(4, n);
                y() + a()
            }
            f(|| 1, 2)
        " }),
        int(3)
    );
    // In a parameter: the effect of `x` is its own, so a failing `x` leaves the result pure.
    let f = "fn f<! E>(a: () -> int ! E, x: () -> int) -> (() -> int ! E) { a }\n";
    assert_eq!(
        signature(&mut TestSession::new(), f, "f"),
        "fn f<! E, e₁>(a: () -> int ! E, x: () -> int ! e₁) -> () -> int ! E"
    );
    assert_val_eq!(
        TestSession::new().run(&format!(
            "{f}fn pure(k: () -> int ! ()) -> int {{ k() }}
            pure(f(|| 1, || idiv(1, 0)))"
        )),
        int(1)
    );
    // Each parameter's unwritten effect is its own, and a written generic keeps its name when
    // one before it is not used.
    assert_eq!(
        signature(
            &mut TestSession::new(),
            "fn f<! E, F>(a: () -> int ! F, x: () -> int, y: () -> int) -> int { a() }",
            "f"
        ),
        "fn f<! F, e₁, e₂>(a: () -> int ! F, x: () -> int ! e₁, y: () -> int ! e₂) -> int ! F"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_effect_left_unwritten_in_a_requirement_is_inferred() {
    // A requirement that the body does not use is met by any implementation, whatever the
    // body performs.
    for (body, expected) in [("n", 0), ("let a = [1]; a[n]", 1)] {
        let h =
            format!("{CALL_THROUGH_TRAIT}fn h<T>(x: T, n: int) -> int where T: Run {{ {body} }}\n");
        assert_val_eq!(
            TestSession::new().run(&format!("{h}h(Cb(|| idiv(1, 0)), 0)")),
            int(expected),
            "{body}"
        );
        assert_val_eq!(
            TestSession::new().run(&format!(
                "{h}fn user<! G>(g: () -> int ! G) -> int {{ h(Cb(g), 0) }}
                user(|| 1)"
            )),
            int(expected),
            "{body}"
        );
    }
    // A requirement that the body uses adds its effect to the function's.
    let h = format!(
        "{CALL_THROUGH_TRAIT}fn h<T>(x: T, n: int) -> int where T: Run {{
            let a = [n];
            run(x) + a[0]
        }}\n"
    );
    assert_eq!(
        signature(&mut TestSession::new(), &h, "h"),
        "fn h<T ! e₀>(x: T, n: int) -> int ! (fallible, e₀) where T: Run < ! E = e₀>"
    );
    assert_eq!(
        TestSession::new().fail_run(&format!("{h}h(Cb(|| idiv(1, 0)), 0)")),
        SourceFailureKind::DivisionByZero
    );
    // Likewise for the requirement of an impl.
    let outer = format!(
        "{CALL_THROUGH_TRAIT}trait Outer<Self> {{ fn outer(s: Self) -> int; }}
        struct Wrap<T>(T)
        impl<T> Outer for Wrap<T> where T: Run {{ fn outer(s: Wrap<T>) -> int {{ 7 }} }}\n"
    );
    assert_val_eq!(
        TestSession::new().run(&format!("{outer}outer(Wrap(Cb(|| idiv(1, 0))))")),
        int(7)
    );
}
