// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! The impls and functions of a module are inferred the same way whatever their source order.

#[cfg(not(target_arch = "wasm32"))]
use std::thread;

use test_log::test;

use ferlium::compiler::error::CompilationErrorImpl;
use indoc::indoc;
use itertools::Itertools;

use crate::harness::{TestSession, int};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

/// Every order of `items`.
fn permutations<'a>(items: &[&'a str]) -> Vec<Vec<&'a str>> {
    items.iter().copied().permutations(items.len()).collect()
}

/// The module made of `header`, then `items` in `order`, then `tail`.
fn module(header: &str, order: &[&str], tail: &str) -> String {
    format!("{header}\n{}\n{tail}", order.join("\n"))
}

/// Run the module in every order of `items`, expecting the integer `expected`.
fn expect_in_every_order(header: &str, items: &[&str], tail: &str, expected: isize) {
    for order in permutations(items) {
        let source = module(header, &order, tail);
        let mut session = TestSession::new();
        assert_val_eq!(session.run(&source), int(expected), "in:\n{source}");
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn functions_and_impls_use_impls_declared_later() {
    // A function and an impl use a later generic impl at a concrete type, and an impl with
    // inferred outputs.
    expect_in_every_order(
        indoc! { r#"
            trait Size<Self> { fn bag_size(x: Self) -> int; }
            trait Count<Self |-> Output> { fn bag_count(x: Self) -> Output; }
            trait Total<Self> { fn total_of(x: Self) -> int; }
            struct Bag<T>([T])
        "# },
        &[
            "impl<T> Size for Bag<T> { fn bag_size(bag: Bag<T>) -> int { len(bag.0) } }",
            "fn use_it(bag: Bag<int>) -> int { bag_size(bag) + bag_count(bag) }",
            "impl Count { fn bag_count(bag: Bag<int>) -> int { 10 } }",
            "impl Total for int { fn total_of(x: int) -> int { bag_size(Bag([x, x])) } }",
        ],
        "use_it(Bag([1, 2, 3])) * 10 + total_of(0)",
        132,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_written_impl_is_used_instead_of_a_derived_one() {
    // Without the written impl, `Default` would be derived for `W`. A function or an impl that
    // needs it must see the written impl, wherever it is declared.
    expect_in_every_order(
        indoc! { r#"
            trait Make<Self> { fn make(x: Self) -> int; }
            struct W(int)
        "# },
        &[
            "fn get() -> W { default() }",
            "impl Make for int { fn make(x: int) -> int { let w: W = default(); w.0 + x } }",
            "impl Default { fn default() -> W { W(5) } }",
        ],
        "get().0 * 10 + make(1)",
        56,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn improvement_waits_for_unfinished_impls() {
    // `first` learns its result type through the single `Extract` impl whose head matches
    // `[x]`, so this helper of the `Use` impl gets the same signature whatever the order.
    let header = indoc! { r#"
        trait Extract<Self |-> Item> { fn extract(value: Self) -> Item ! fallible; }
        trait Use<Self> { fn use_it(x: Self) -> int ! fallible; }
    "# };
    let items = [
        "impl<T> Extract for <Self = [T] |-> Item = T> where T: Value { fn extract(value: [T]) -> T { value[0] } }",
        "fn first(x) { extract([x]) }",
        "impl Use for int { fn use_it(x: int) -> int { first(x) + 1 } }",
    ];
    let mut signatures = Vec::new();
    for order in permutations(&items) {
        let source = module(header, &order, "");
        let mut session = TestSession::new();
        let first = session.compile_and_get_fn_def(&source, "first");
        signatures.push(
            first
                .ty_scheme
                .display(&session.std_module_env())
                .to_string(),
        );
    }
    assert!(
        signatures
            .iter()
            .all(|signature| *signature == signatures[0]),
        "{signatures:#?}"
    );
    assert!(signatures[0].contains("-> A"), "{}", signatures[0]);
    expect_in_every_order(header, &items, "use_it(1)", 2);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn impls_waiting_for_each_other_without_a_cycle_are_inferred() {
    // `run` needs `Pick` for `int`; the `Pick` impl for `float` needs `Run` for `int`. No impl
    // depends on itself, so all are inferred, whatever the order.
    expect_in_every_order(
        indoc! { r#"
            trait Run<Self> { fn run(x: Self) -> int; }
            trait Pick<Self> { fn pick(x: Self) -> int; }
        "# },
        &[
            "impl Run { fn run(x: int) -> int { pick(x) } }",
            "impl Pick { fn pick(x: float) -> int { run(1) + 1 } }",
            "impl Pick { fn pick(x: int) -> int { 7 } }",
        ],
        "run(1) * 10 + pick(1.5)",
        78,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn helpers_of_impls_wait_for_the_impls_they_use() {
    // The `Use` impl calls `helper`, which needs the `Show` impl.
    expect_in_every_order(
        indoc! { r#"
            trait Use<Self> { fn use_it(x: Self) -> int; }
            trait Show<Self> { fn show(x: Self) -> int; }
            struct W(int)
        "# },
        &[
            "impl Use { fn use_it(x: int) -> int { helper(x) } }",
            "fn helper(x: int) -> int { show(W(x)) }",
            "impl Show { fn show(w: W) -> int { w.0 + 1 } }",
        ],
        "use_it(1)",
        2,
    );
    // A helper calling an impl whose interface is written works while that impl calls it.
    expect_in_every_order(
        "trait Use<Self> { fn use_it(x: Self) -> int; }",
        &[
            "impl Use for int { fn use_it(x: int) -> int { if x > 0 { helper(x - 1) + 1 } else { 0 } } }",
            "fn helper(x: int) -> int { use_it(x) }",
        ],
        "use_it(3)",
        3,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_impl_and_a_helper_needing_each_other_unfinished_are_rejected() {
    // The impl needs `helper` to be inferred first, and `helper` needs the impl's interface,
    // which is only known once the impl is inferred.
    let header = "trait Use<Self> { fn use_it(x: Self) -> int; }";
    let items = [
        "impl Use { fn use_it(x: int) -> int { helper(x) } }",
        "fn helper(x: int) -> int { use_it(x) }",
    ];
    for order in permutations(&items) {
        let mut session = TestSession::new();
        let error = session.fail_compilation(&module(header, &order, "use_it(1)"));
        match error.into_inner() {
            CompilationErrorImpl::InferenceBlockedByPendingImpls { blocked } => {
                assert!(!blocked.is_empty())
            }
            other => panic!("expected InferenceBlockedByPendingImpls, got {other:?}"),
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_generic_impl_and_a_generic_helper_calling_each_other_are_inferred() {
    // `helper` keeps its requirement on `Bag<T>`, which the impl provides when calling it.
    expect_in_every_order(
        indoc! { r#"
            struct Bag<T>([T])
            trait Use<Self> { fn use_it(x: Self, n: int) -> int; }
        "# },
        &[
            indoc! { r#"
                impl<T> Use for Bag<T> {
                    fn use_it(x: Bag<T>, n: int) -> int {
                        if n == 0 {
                            0
                        } else {
                            helper(x, n - 1) + 1
                        }
                    }
                }
            "# },
            "fn helper<T>(x: Bag<T>, n: int) -> int { use_it(x, n) }",
        ],
        "helper(Bag([1]), 3)",
        3,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_generic_impl_and_a_helper_selecting_it_are_rejected() {
    let header = indoc! { r#"
        struct Bag<T>([T])
        trait Use<Self> { fn use_it(x: Self) -> int; }
        trait Conv<Self |-> Out> { fn conv(x: Self) -> Out; }
    "# };
    for items in [
        // `helper` needs the impl to be selected at `Bag<int>`.
        [
            "impl<T> Use for Bag<T> { fn use_it(x: Bag<T>) -> int { helper(Bag([1])) } }",
            "fn helper(x: Bag<int>) -> int { use_it(x) }",
        ],
        // `helper` learns `Out` from the impl.
        [
            "impl<T> Conv for <Self = Bag<T> |-> Out = int> { fn conv(x: Bag<T>) -> int { helper(x) } }",
            "fn helper<T>(x: Bag<T>) -> int { conv(x) }",
        ],
    ] {
        for order in permutations(&items) {
            let mut session = TestSession::new();
            let error = session.fail_compilation(&module(header, &order, ""));
            assert!(matches!(
                error.into_inner(),
                CompilationErrorImpl::InferenceBlockedByPendingImpls { .. }
            ));
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_failed_candidate_does_not_block_a_successful_one() {
    // The first `Pick` needs `P`, which is unfinished, and `Q`, which does not exist. It cannot
    // apply, so that `P` is unfinished must not make `helper` wait for it: `P` calls `helper`.
    expect_in_every_order(
        indoc! { r#"
            struct Bag<T>(T)
            trait Pick<Self> { fn pick(x: Self) -> int; }
            trait P<Self> { fn p(x: Self) -> int; }
            trait Q<Self> { fn q(x: Self) -> int; }
        "# },
        &[
            "impl<T> Pick for Bag<T> where Bag<T>: P, Bag<T>: Q { fn pick(x: Bag<T>) -> int { 1 } }",
            "impl<T> Pick for Bag<[T]> { fn pick(x: Bag<[T]>) -> int { 2 } }",
            "fn helper(x: Bag<[int]>) -> int { pick(x) }",
            "impl<T> P for Bag<[T]> { fn p(x: Bag<[T]>) -> int { helper(Bag([1])) } }",
        ],
        "helper(Bag([1]))",
        2,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_candidate_waiting_for_an_unfinished_impl_is_retried() {
    // Without another candidate, `helper` must wait for `P`, for `Pick` to apply.
    expect_in_every_order(
        indoc! { r#"
            struct Bag<T>(T)
            trait Pick<Self> { fn pick(x: Self) -> int; }
            trait P<Self> { fn p(x: Self) -> int; }
        "# },
        &[
            "impl<T> Pick for Bag<T> where Bag<T>: P { fn pick(x: Bag<T>) -> int { 1 } }",
            "fn helper(x: Bag<[int]>) -> int { pick(x) }",
            "impl<T> P for Bag<[T]> { fn p(x: Bag<[T]>) -> int { 3 } }",
        ],
        "helper(Bag([1]))",
        1,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn functions_keep_written_generics_whatever_impls_exist() {
    // The only impl fits `[T]` by narrowing `T`, which stays generic: the call decides.
    let header = "trait A<Self> { fn a(x: Self) -> int; }";
    let items = [
        "impl<U> A for [[U]] { fn a(x: [[U]]) -> int { 1 } }",
        "fn f<T>(x: [T]) -> int { a(x) }",
    ];
    expect_in_every_order(header, &items, "f([[1]])", 1);
    for order in permutations(&items) {
        let mut session = TestSession::new();
        session.fail_compilation(&module(header, &order, "f([1])"));
    }
    // The same with an output to learn: the impl selected at the call provides it.
    expect_in_every_order(
        "trait C<Self |-> O> { fn c(x: Self) -> O; }",
        &[
            "impl<U> C for <Self = [[U]] |-> O = int> { fn c(x: [[U]]) -> int { 7 } }",
            "fn f<T>(x: [T]) { c(x) }",
        ],
        "f([[1]])",
        7,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn subtype_bounds_do_not_narrow_written_generics() {
    // `[x]` only bounds `T` by the element type, which the candidate would narrow.
    let header = "trait A<Self> { fn a(x: Self) -> int; }";
    let items = [
        "impl<U> A for [[U]] { fn a(x: [[U]]) -> int { 1 } }",
        "fn f<T>(x: T) -> int { a([x]) }",
    ];
    expect_in_every_order(header, &items, "f([1])", 1);
    expect_in_every_order(
        "trait C<Self |-> O> { fn c(x: Self) -> O; }",
        &[
            "impl<U> C for <Self = [[U]] |-> O = int> { fn c(x: [[U]]) -> int { 7 } }",
            "fn f<T>(x: T) { c([x]) }",
        ],
        "f([1])",
        7,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn candidates_merging_written_generics_cannot_be_selected() {
    // The call decides: `Pair<U, U>` fits only if `T` and `S` are the same type.
    expect_in_every_order(
        indoc! { r#"
            struct Pair<X, Y>(X, Y)
            trait A<Self> { fn a(x: Self) -> int; }
        "# },
        &[
            "impl<U> A for Pair<U, U> { fn a(x: Pair<U, U>) -> int { 1 } }",
            "fn f<T, S>(x: Pair<T, S>) -> int { a(x) }",
        ],
        "f(Pair(1, 2))",
        1,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn other_variables_still_learn_beside_written_generics() {
    expect_in_every_order(
        "trait Pick<A, B> { fn pick(x: A, y: B) -> int; }",
        &[
            "impl<U> Pick for <A = [U], B = int> { fn pick(x: [U], y: int) -> int { 7 } }",
            "fn f<T>(x: [T]) -> int { pick(x, default()) }",
        ],
        "f([1])",
        7,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generics_of_recursive_functions_may_share_their_inference() {
    expect_in_every_order(
        "",
        &[
            "fn f<T>(x: T, n: int) -> T { if n > 0 { g(x, n - 1) } else { x } }",
            "fn g<U>(x: U, n: int) -> U { if n > 0 { f(x, n - 1) } else { x } }",
        ],
        "f(7, 2)",
        7,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn impl_methods_cannot_narrow_or_merge_written_generics() {
    for source in [
        indoc! { r#"
            trait B<Self> { fn b(x: Self) -> int; }
            impl<T> B for [T] { fn b(x: [T]) -> int { let y: [int] = x; 1 } }
        "# },
        indoc! { r#"
            trait P<X, Y> { fn p(x: X, y: Y) -> int; }
            impl<T, U> P for <X = T, Y = U> { fn p(x: T, y: U) -> int { let l = [x, y]; 1 } }
        "# },
    ] {
        let mut session = TestSession::new();
        let error = session.fail_compilation(source);
        assert!(
            matches!(
                error.into_inner(),
                CompilationErrorImpl::InvalidGenericParams { .. }
            ),
            "{source}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn holes_and_unannotated_arguments_still_learn_from_impls() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            trait C<Self |-> O> { fn c(x: Self) -> O; }
            impl<U> C for <Self = [U] |-> O = int> { fn c(x: [U]) -> int { 7 } }
            fn g<T>(x: T, y) { c([(x, y)]) }
            g(1, 2.5)
        "# }),
        int(7)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn literals_do_not_call_a_local_from_int() {
    expect_in_every_order(
        indoc! { r#"
            trait A<Self> { fn a(x: Self) -> int; }
            trait B<Self> { fn b(x: Self) -> int; }
        "# },
        &[
            "fn from_int(x: int) -> int { x + x }",
            "impl A for int { fn a(x: int) -> int { 1 } }",
            "impl B for int { fn b(x: int) -> int { from_int(x) } }",
            "fn one() -> int { 1 }",
        ],
        "a(0) * 100 + one() * 10 + b(2)",
        114,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn for_loops_do_not_call_a_local_iter_or_next() {
    expect_in_every_order(
        indoc! { r#"
            trait A<Self> { fn a(x: Self) -> int; }
            trait B<Self> { fn b(x: Self) -> int; }
        "# },
        &[
            "fn iter(x: int) -> int { x }",
            "fn next<T>(x: &mut T) -> Option<int> { None }",
            "impl A for int { fn a(x: int) -> int { let mut total = 0; for item in 0..3 { total += 1; }; total } }",
            "impl B for int { fn b(x: int) -> int { let mut y = iter(x); next(y); 0 } }",
        ],
        "a(0) + b(0)",
        3,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn casts_do_not_call_a_local_cast() {
    expect_in_every_order(
        "",
        &[
            "fn cast(x: float) -> int { 99 }",
            "fn f() -> int { 3.0 as int }",
        ],
        "f() + cast(1.5)",
        102,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unfinished_impls_fitting_by_narrowing_still_prevent_selection() {
    // The `[[U]]` impl cannot be selected for `helper`, but it stops `helper` from selecting the
    // other impl, whose `bool` would reject the call.
    expect_in_every_order(
        indoc! { r#"
            trait Pick<A, B> { fn pick(x: A, y: B) -> int; }
            trait Use<Self> { fn use_it(x: Self) -> int; }
        "# },
        &[
            "impl<U> Pick for <A = [U], B = bool> { fn pick(x: [U], y: bool) -> int { 7 } }",
            "fn helper<T>(x: [T], y) -> int { pick(x, y) }",
            "impl Use for int { fn use_it(x: int) -> int { helper([[x]], (1: int)) } }",
            "impl<U> Pick for <A = [[U]], B = int> { fn pick(x: [[U]], y: int) -> int { 8 } }",
        ],
        "use_it(1)",
        8,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_ambiguous_impl_method_is_an_ordinary_error() {
    let items = [
        "impl<U> Pick for <A = [U], B = bool> { fn pick(x: [U], y: bool) -> int { 7 } }",
        "impl<U> Pick for <A = [[U]], B = int> { fn pick(x: [[U]], y: int) -> int { 8 } }",
        "impl Use for int { fn use_it(x: int) -> int { pick([[x]], default()) } }",
    ];
    let header = indoc! { r#"
        trait Pick<A, B> { fn pick(x: A, y: B) -> int; }
        trait Use<Self> { fn use_it(x: Self) -> int; }
    "# };
    for order in permutations(&items) {
        let mut session = TestSession::new();
        let error = session.fail_compilation(&module(header, &order, ""));
        assert!(
            matches!(
                error.into_inner(),
                CompilationErrorImpl::UnresolvedConstraints { .. }
            ),
            "{order:?}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_impls_requiring_each_other_are_inferred() {
    expect_in_every_order(
        indoc! { r#"
            trait A<Self> { fn a(x: Self) -> int; }
            trait B<Self> { fn b(x: Self) -> int; }
        "# },
        &[
            "impl A for [int] { fn a(x: [int]) -> int { 1 } }",
            "impl<T> A for [[T]] where [T]: B { fn a(x: [[T]]) -> int { 2 } }",
            "impl<T> B for [T] where [T]: A { fn b(x: [T]) -> int { 3 } }",
        ],
        "a([[1]]) + b([1])",
        5,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_impls_requiring_each_other_with_written_outputs_are_inferred() {
    expect_in_every_order(
        indoc! { r#"
            trait A<Self> { fn a(x: Self) -> int; }
            trait C<Self |-> O> { fn c(x: Self) -> O; }
        "# },
        &[
            "impl A for [int] { fn a(x: [int]) -> int { 1 } }",
            "impl<T> A for [[T]] where [T]: C<O = int> { fn a(x: [[T]]) -> int { 2 } }",
            "impl<T> C for <Self = [T] |-> O = int> where [T]: A { fn c(x: [T]) -> int { 3 } }",
        ],
        "a([[1]]) + c([1])",
        5,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn projections_preserve_written_generics_before_trait_improvement() {
    for (shape, projection, value) in [
        ("T", "x.0", "P(0)"),
        ("Q<T>", "x.0.0", "P(Q(0))"),
        ("{ value: Q<T> }", "x.0.value.0", "P({ value: Q(0) })"),
    ] {
        let header = format!(
            "trait Read<Self> {{ fn read(x: Self) -> int; }}
             trait Hidden<Self> {{ fn hidden(x: Self) -> int; }}
             trait Use<Self> {{ fn use_it(x: Self) -> int; }}
             struct Q<T>(T)
             struct P<T>({shape})"
        );
        let use_impl = format!(
            "impl<T> Use for P<T> where [T]: Hidden {{
                fn use_it(x: P<T>) -> int {{ hidden([{projection}]) }}
             }}"
        );
        let items = [
            "impl Read for [int] { fn read(x: [int]) -> int { 7 } }",
            "impl<T> Hidden for [T] where [T]: Read { fn hidden(x: [T]) -> int { read(x) } }",
            &use_impl,
        ];
        expect_in_every_order(&header, &items, &format!("use_it({value})"), 7);
        // The impl keeps its requirement; it does not make unsupported instantiations valid.
        let mut session = TestSession::new();
        session.fail_compilation(&module(
            &header,
            &items,
            &format!("use_it({})", value.replace('0', "true")),
        ));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn other_impls_do_not_narrow_a_written_generic() {
    // Whatever the order, `T` stays generic, so `B` applies wherever `A` does.
    expect_in_every_order(
        indoc! { r#"
            trait A<Self> { fn a(x: Self) -> int; }
            trait B<Self> { fn b(x: Self) -> int; }
        "# },
        &[
            "impl<U> A for [[U]] { fn a(x: [[U]]) -> int { 1 } }",
            "impl<T> B for [T] where [T]: A { fn b(x: [T]) -> int { a(x) + 2 } }",
            "impl<U> A for [(U, U)] { fn a(x: [(U, U)]) -> int { 4 } }",
        ],
        "b([(1, 1)]) * 10 + b([[1]])",
        63,
    );
}

#[test]
#[cfg(not(target_arch = "wasm32"))]
fn reaching_the_solver_depth_limit_waits_for_unfinished_impls() {
    // The chain ends just beyond the limit of the solver, in an impl that the consumer needs.
    const CHAIN: usize = 130;
    let traits = (0..CHAIN)
        .map(|i| format!("trait P{i}<Self> {{}}"))
        .join("\n");
    let chain = (0..CHAIN)
        .map(|i| format!("impl<T> P{i} for T where T: P{} {{}}", i + 1))
        .join("\n");
    let header = format!(
        "{traits}\n\
        trait P{CHAIN}<Self> {{ fn end(x: Self) -> int; }}\n\
        trait Use<Self> {{ fn use_it(x: Self) -> int; }}\n\
        {chain}\n\
        fn demand<T>(x: T) -> int where T: P0 {{ 1 }}"
    );
    // Solving this deep does not fit the default stack of a test thread.
    thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            expect_in_every_order(
                &header,
                &[
                    "impl Use for int { fn use_it(x: int) -> int { demand(x) } }",
                    &format!("impl P{CHAIN} {{ fn end(x: int) -> int {{ 0 }} }}"),
                ],
                "use_it(0)",
                1,
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn inherited_defaults_calling_module_functions_are_inferred_first() {
    expect_in_every_order(
        "",
        &[
            "trait Twice<Self> { fn base(x: Self) -> int; fn twice(x: Self) -> int { double(base(x)) } }",
            "fn double(x: int) -> int { x * 2 }",
            "impl Twice for int { fn base(x: int) -> int { x + 1 } }",
        ],
        "twice(4)",
        10,
    );
}
