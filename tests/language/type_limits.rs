// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! The limits on the height and size of types, which bound the stack and the work that types
//! cost the compiler, whatever their source.

use test_log::test;

use crate::harness::{TestSession, int};
use ferlium::{
    compiler::error::{CompilationErrorImpl, CompilerLimitKind},
    types::r#type::{TYPE_HEIGHT_LIMIT, TYPE_SIZE_LIMIT},
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

/// Assert that compiling `src` exceeds the type limit `kind`, and return the value that exceeded
/// it and the source text that the error points at.
fn type_limit_error(src: &str, kind: CompilerLimitKind) -> (usize, String) {
    let error = TestSession::new().fail_compilation(src);
    let CompilationErrorImpl::CompilerLimitExceeded(error) = error.into_inner() else {
        panic!("expected a type limit error for:\n{src}");
    };
    let limit = match kind {
        CompilerLimitKind::TypeHeight => TYPE_HEIGHT_LIMIT,
        CompilerLimitKind::TypeSize => TYPE_SIZE_LIMIT,
        _ => unreachable!("not a type limit"),
    };
    assert_eq!((error.kind, error.limit), (kind, limit as usize));
    assert!(error.actual > error.limit);
    assert!(!error.span.is_synthesized(), "the error has a location");
    let at = src[error.span.start_usize()..error.span.end_usize()].to_string();
    (error.actual, at)
}

/// Assert that compiling `src` exceeds the type limit `kind` with the value `actual`, and return
/// the source text that the error points at.
fn assert_type_limit(src: &str, kind: CompilerLimitKind, actual: usize) -> String {
    let (error_actual, at) = type_limit_error(src, kind);
    assert_eq!(error_actual, actual);
    at
}

/// `n` aliases, each wrapping the previous one in `W`, and a function taking the last.
fn alias_chain(n: usize) -> String {
    let aliases = (1..=n)
        .map(|i| format!("type D{i} = W<D{}>;", i - 1))
        .collect::<Vec<_>>()
        .join("\n");
    format!("struct W<T>(T)\ntype D0 = int;\n{aliases}\nfn f(x: D{n}) -> int {{ 1 }}\n0")
}

/// A chain of aliases is as high as its length: the deepest that a function can take compiles,
/// and the alias that crosses the limit is an error, at its definition. The function type is one
/// level more than its argument.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn alias_chains_are_limited_in_height() {
    let deepest = TYPE_HEIGHT_LIMIT as usize - 2;
    assert_val_eq!(TestSession::new().run(&alias_chain(deepest)), int(0));
    let src = alias_chain(TYPE_HEIGHT_LIMIT as usize);
    let at = assert_type_limit(&src, CompilerLimitKind::TypeHeight, 129);
    assert_eq!(at, format!("W<D{}>", TYPE_HEIGHT_LIMIT - 1));
}

/// `n` aliases from `D1` to `Dn`, each a pair of the previous one, from `D0 = int`: the size
/// doubles at each, `Di` having 2^(i+1) - 1 nodes.
fn pair_aliases(n: usize) -> String {
    let aliases = (1..=n)
        .map(|i| format!("type D{i} = (D{0}, D{0});", i - 1))
        .collect::<Vec<_>>()
        .join("\n");
    format!("type D0 = int;\n{aliases}")
}

/// The pair aliases up to `Dn`, and nothing else.
fn pair_chain(n: usize) -> String {
    format!("{}\n0", pair_aliases(n))
}

/// The size counts a repeated part at each of its occurrences, so a chain of pairs reaches it
/// at a small height.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn shared_parts_count_at_each_occurrence() {
    // `D11` has 2^12 - 1 nodes.
    assert_val_eq!(TestSession::new().run(&pair_chain(11)), int(0));
    let at = assert_type_limit(&pair_chain(12), CompilerLimitKind::TypeSize, (1 << 13) - 1);
    assert_eq!(at, "(D11, D11)");
}

/// `n` lets, each wrapping the previous value in `W`, from `base`.
fn let_chain(n: usize, base: &str) -> String {
    let lets = (1..=n)
        .map(|i| format!("    let a{i} = W(a{});", i - 1))
        .collect::<Vec<_>>()
        .join("\n");
    format!("struct W<T>(T)\nfn g() -> int {{\n    let a0 = {base};\n{lets}\n    1\n}}\ng()")
}

/// Inferred types are limited as written ones are, at the expression that crosses the limit,
/// whether the innermost type is known or still a variable.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn inferred_types_are_limited_in_height() {
    let deepest = TYPE_HEIGHT_LIMIT as usize - 1;
    for base in ["true", "1"] {
        assert_val_eq!(TestSession::new().run(&let_chain(deepest, base)), int(1));
        let src = let_chain(deepest + 1, base);
        let at = assert_type_limit(&src, CompilerLimitKind::TypeHeight, 129);
        assert_eq!(at, format!("let a{0} = W(a{1});", deepest + 1, deepest));
    }
}

/// `n` functions, each applying the previous one twice to its argument: let-polymorphism makes
/// the type of the last one doubly exponential in `n`.
fn doubling_functions(n: usize) -> String {
    let functions = (1..=n)
        .map(|i| format!("fn f{i}(x) {{ f{0}(f{0}(x)) }}", i - 1))
        .collect::<Vec<_>>()
        .join("\n");
    format!("fn f0(x) {{ (x, x) }}\n{functions}\n0")
}

/// A type that grows by instantiation is refused when it is built, before any work on it. Its
/// size is measured once the substitution that builds it is complete.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn types_grown_by_instantiation_are_limited_in_size() {
    assert_val_eq!(TestSession::new().run(&doubling_functions(3)), int(0));
    let src = doubling_functions(4);
    let (_, at) = type_limit_error(&src, CompilerLimitKind::TypeSize);
    assert_eq!(at, "fn f4(x) { f3(f3(x)) }");
}

/// A function or trait method, as `kind`, taking `args` arguments, each a pair chain of `D9`,
/// of 1023 nodes.
fn wide_signature(kind: &str, args: usize) -> String {
    let aliases = pair_aliases(9);
    let params = (0..args)
        .map(|i| format!("a{i}: D9"))
        .collect::<Vec<_>>()
        .join(", ");
    let item = match kind {
        "fn" => format!("fn f({params}) -> int {{ 1 }}"),
        _ => format!("trait W<T> {{ fn f({params}) -> T; }}"),
    };
    format!("{aliases}\n{item}\n0")
}

/// The type of a function is limited as a whole: arguments each within the limits may exceed
/// them together.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn signatures_are_limited_as_a_whole() {
    for kind in ["fn", "trait"] {
        // 1 + 4 · 1023 + 1 nodes.
        assert_val_eq!(TestSession::new().run(&wide_signature(kind, 4)), int(0));
        let src = wide_signature(kind, 5);
        let at = assert_type_limit(&src, CompilerLimitKind::TypeSize, 5 * 1023 + 2);
        assert!(at.starts_with("fn f(a0: D9"), "{at}");
    }
}

/// A recursive type of `variants` variants, sharing one payload of `width` occurrences of the
/// type, and a generic function receiving it.
fn shared_recursive_payload(variants: usize, width: usize) -> String {
    let payload = vec!["R<T>"; width].join(", ");
    let variants = (0..variants)
        .map(|i| format!("V{i}(P<T>)"))
        .collect::<Vec<_>>()
        .join(" | ");
    format!(
        "type P<T> = ({payload});\ntype R<T> = {variants} | N(T);\n\
         fn gen<T>(r: R<T>) -> int {{ 1 }}\nfn main(r: R<int>) -> int {{ gen(r) }}\n0"
    )
}

/// The size of a recursive type counts each of its members once, however many share it, so a
/// type within the limits stays within them when substitution rebuilds it. Counted at each
/// occurrence, the payload would be over the limit: 1 + 40 · (1 + 110) + 1 nodes.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn shared_recursive_members_count_once() {
    let src = shared_recursive_payload(40, 110);
    assert_val_eq!(TestSession::new().run(&src), int(0));
}

/// A recursive alias is measured once its group is built, and checked at its definition, used or
/// not.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_aliases_are_limited_at_their_definition() {
    let alias = "Link(R) | One(D11) | Two(D11) | End";
    let src = format!("{}\ntype R = {alias};\n0", pair_aliases(11));
    let (_, at) = type_limit_error(&src, CompilerLimitKind::TypeSize);
    assert_eq!(at, alias);
}

/// A function type can be a member of a recursive type, as `(R<T>) -> R<T>` is of `R<T>`. It
/// then counts that type once, whether written as an alias, or as the signature of a function or
/// of a trait method, although its parameter and its result, each the whole type, would together
/// exceed the size limit.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_signatures_count_their_type_once() {
    let src = format!(
        "{}\ntype R<T> = Step((R<T>) -> R<T>) | Data(D10) | Item(T) | End;\n\
         type Sig = (R<int>) -> R<int>;\n\
         fn f(x: R<int>) -> R<int> {{ x }}\n\
         trait M<Self> {{ fn g(x: R<Self>) -> R<Self>; }}\n\
         impl M for int {{ fn g(x: R<int>) -> R<int> {{ x }} }}\n0",
        pair_aliases(10)
    );
    assert_val_eq!(TestSession::new().run(&src), int(0));
}

/// Defaulting a type variable tries candidates, and a limit reached while checking one is
/// reported, rather than taken as the candidate not applying.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn defaulting_reports_type_limits() {
    let growing = "trait R<Self> {}\nimpl<T> R for T where (T, T): R {}";
    for (function, use_site) in [
        ("fn mk<T>() -> [T] where T: R { [] }", "mk()"),
        ("fn s<T>(x: Option<T>) -> int where T: R { 0 }", "s(None)"),
    ] {
        let src = format!("{growing}\n{function}\n{use_site}");
        let (_, at) = type_limit_error(&src, CompilerLimitKind::TypeSize);
        assert_eq!(at, "(T, T): R");
    }
}

/// `n` structural aliases in a ring, each holding the next one twice, and a function taking the
/// first: the paths through the ring double at each member.
fn ring_of_joins(n: usize) -> String {
    let aliases = (0..n)
        .map(|i| format!("type R{i} = T{i}(R{0}, R{0}) | N{i};", (i + 1) % n))
        .collect::<Vec<_>>()
        .join("\n");
    format!("{aliases}\nfn f(x: R0) -> R0 {{ x }}")
}

/// A recursive type costs the compiler its members, not its paths, of which there can be
/// exponentially many: the largest ring that the height limit allows compiles, also as the input
/// of a written impl, whose effects are checked along every path.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_types_cost_their_members_not_their_paths() {
    // The ring has a member for each alias and each payload, so its height is twice its length,
    // plus one for `()`.
    let longest = (TYPE_HEIGHT_LIMIT as usize - 1) / 2;
    let ring = ring_of_joins(longest);
    assert_val_eq!(TestSession::new().run(&format!("{ring}\n0")), int(0));
    let src = format!(
        "{ring}\nstruct Wrap<T>(T)\ntrait Marker<Self> {{}}\nimpl Marker for Wrap<R0> {{}}\n0"
    );
    assert_val_eq!(TestSession::new().run(&src), int(0));
    let src = format!("{}\n0", ring_of_joins(longest + 1));
    let (_, at) = type_limit_error(&src, CompilerLimitKind::TypeHeight);
    assert!(at.starts_with('T'), "{at}");
}
