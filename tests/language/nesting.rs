// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! The nesting limit of source code, which bounds the stack that compilation needs.

use test_log::test;

use crate::harness::{TestSession, int};
use ferlium::{
    compiler::error::{CompilationError, CompilationErrorImpl},
    parser::nesting::NESTING_LIMIT,
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

/// A value of any type, which no function returns: a type as deep as the nesting limit allows is
/// as high as the type limit allows, so no function can take or return it, as its own type is
/// one level higher.
const ANY: &str = "return 0";

fn nest(n: usize, open: &str, leaf: &str, close: &str) -> String {
    format!("{}{leaf}{}", open.repeat(n), close.repeat(n))
}

/// Assert that `error` is the nesting error, and return where it points.
fn assert_too_deep(error: CompilationError) -> usize {
    match error.into_inner() {
        CompilationErrorImpl::ParsingFailed(errors) => {
            let (message, span) = &errors[0];
            assert!(
                message.contains(&format!("the limit is {NESTING_LIMIT} levels")),
                "{message}"
            );
            span.start_usize()
        }
        other => panic!("expected a nesting error, got {other:?}"),
    }
}

/// The deepest nesting of a few constructs compiles and runs, in a debug build too, and one more
/// level is an error. These constructs cost the compiler the most stack per level, so this test
/// checks a stack size for hosts: run it with `RUST_MIN_STACK` set to that size. Each expression, `let` pattern and type node is a level: the body block of
/// `f` and the innermost `b` or `int` count, and an `if` or a `for` is a level and its block one.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn nesting_at_the_limit_compiles() {
    type Source = fn(usize) -> String;
    let shapes: [(usize, Source, isize); 4] = [
        (
            126,
            |n| {
                format!(
                    "fn f(b: int) -> int {{ {} }}\nf(3)",
                    nest(n, "-(", "b", ")")
                )
            },
            3,
        ),
        (
            63,
            |n| {
                let body = nest(n, "if b > 0 { ", "b", " } else { 0 }");
                format!("fn f(b: int) -> int {{ {body} }}\nf(3)")
            },
            3,
        ),
        (
            62,
            |n| {
                format!(
                    "fn f(b: int) -> int {{ let mut s = b; {} s = s + 1; {} s }}\nf(3)",
                    "for i in 0..1 { ".repeat(n),
                    "}; ".repeat(n)
                )
            },
            4,
        ),
        (
            127,
            |n| {
                format!(
                    "fn f() -> int {{ let b: {} = []; 1 }}\nf()",
                    nest(n, "[", "int", "]")
                )
            },
            1,
        ),
    ];
    for (deepest, source, value) in shapes {
        let mut session = TestSession::new();
        let src = source(deepest);
        assert_val_eq!(session.run(&src), int(value), "{src}");
        assert_too_deep(session.fail_compilation(&source(deepest + 1)));
    }
}

/// The error points at the part beyond the limit, not at the whole function.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn nesting_error_points_beyond_the_limit() {
    let prefix = "fn f(b: int) -> int { ";
    let src = format!("{prefix}{} }}", nest(127, "-(", "b", ")"));
    let start = assert_too_deep(TestSession::new().fail_compilation(&src));
    assert!(start >= prefix.len() + 2 * 126, "{start}");

    // The node beyond the limit is the unit value of the innermost block, which the parser
    // synthesizes, so the error points at that block.
    let prefix = "fn f() ";
    let src = format!("{prefix}{}", nest(NESTING_LIMIT, "{ ", "", " }"));
    let start = assert_too_deep(TestSession::new().fail_compilation(&src));
    assert_eq!(start, prefix.len() + 2 * (NESTING_LIMIT - 1));
}

/// A `let` pattern and a type count on their own, not as part of the expression holding them.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn let_patterns_and_types_nest_on_their_own() {
    let ty = nest(NESTING_LIMIT - 1, "(int, ", "int", ")");
    let source = |n| {
        let pattern = nest(n, "(_, ", "a", ")");
        format!("fn f() -> int {{ let x: {ty} = {ANY}; let {pattern} = x; a }}\n1")
    };
    let mut session = TestSession::new();
    assert_val_eq!(session.run(&source(NESTING_LIMIT - 1)), int(1));
    assert_too_deep(session.fail_compilation(&source(NESTING_LIMIT)));
}

/// Literal patterns in `match` and `use` trees nest up to the limit too.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn match_literals_and_use_trees_nest_up_to_the_limit() {
    let ty = nest(NESTING_LIMIT - 1, "(int, ", "int", ")");
    let matching = |n| {
        let literal = nest(n, "(1, ", "1", ")");
        format!("fn f() -> int {{ let x: {ty} = {ANY}; match x {{ {literal} => 0, _ => 1 }} }}\n1")
    };
    let using = |n| format!("use {};\n1", nest(n, "{ ", "std::*", " }"));
    let mut session = TestSession::new();
    assert_val_eq!(session.run(&matching(NESTING_LIMIT - 1)), int(1));
    assert_too_deep(session.fail_compilation(&matching(NESTING_LIMIT)));
    assert_val_eq!(session.run(&using(NESTING_LIMIT - 1)), int(1));
    assert_too_deep(session.fail_compilation(&using(NESTING_LIMIT)));
}

/// Nesting far beyond the limit is an error, not a stack overflow: the parser builds no type,
/// pattern or `use` tree beyond the limit, and the check of expressions does not recurse.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn nesting_far_beyond_the_limit_is_an_error() {
    const N: usize = 100_000;
    let sources = [
        format!("fn f(b: int) -> int {{ {} }}", nest(N, "-(", "b", ")")),
        format!("fn f(b: int) -> int {{ b{} }}", " + 1".repeat(N)),
        format!("fn f(b: {}) -> int {{ 1 }}", nest(N, "[", "int", "]")),
        format!("fn f(b: {}int) -> int {{ 1 }}", "() -> ".repeat(N)),
        format!(
            "fn f(b: int) -> int {{ let {} = 0; 1 }}",
            nest(N, "(b, ", "a", ")")
        ),
        format!(
            "fn f(b: int) -> int {{ match b {{ {} => 0, _ => 1 }} }}",
            nest(N, "(1, ", "1", ")")
        ),
        format!("use {};", nest(N, "{ ", "std::*", " }")),
    ];
    let mut session = TestSession::new();
    for src in sources {
        assert_too_deep(session.fail_compilation(&src));
    }
}

/// A type that a host parses alone has the same limit.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn nesting_limits_types_parsed_alone() {
    let mut session = TestSession::new();
    let ty = |n| nest(n, "[", "int", "]");
    assert!(session.resolve_defined_type(&ty(NESTING_LIMIT - 1)).is_ok());
    assert_too_deep(
        session
            .resolve_defined_type(&ty(NESTING_LIMIT))
            .unwrap_err(),
    );
    assert_too_deep(session.resolve_holed_type(&ty(100_000)).unwrap_err());
}
