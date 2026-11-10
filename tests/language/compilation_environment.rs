// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use crate::harness::{TestSession, int};
use ferlium::{
    Location, ModuleStatus,
    compiler::test_support::{
        module_compilation_revision, module_has_compiled_version, module_is_stale,
    },
    module::{Module, ModuleId, Path},
};
use test_log::test;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

fn compile_module(session: &mut TestSession, name: &str, source: &str) -> ModuleId {
    session
        .try_compile_module(name, source)
        .unwrap_or_else(|error| panic!("{name}: {error:?}"))
        .module_id
}

fn assert_fresh(session: &TestSession, id: ModuleId, label: &str) {
    assert_eq!(
        module_is_stale(session.session(), id),
        Some(false),
        "{label}"
    );
}

fn assert_stale(session: &TestSession, id: ModuleId, label: &str) {
    assert_eq!(
        module_is_stale(session.session(), id),
        Some(true),
        "{label}"
    );
}

fn status(session: &TestSession, id: ModuleId) -> ModuleStatus<'_> {
    session.session().modules().info(id).unwrap().status()
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn module_status_explains_failures_and_waiting_until_recovery() {
    let mut session = TestSession::new();
    for name in ["a", "b"] {
        assert!(session.try_compile_module(name, "pub fn (").is_err());
    }
    let registry = session.session().modules();
    let a = registry.id_by_path(&Path::single_str("a")).unwrap();
    let b = registry.id_by_path(&Path::single_str("b")).unwrap();
    for id in [a, b] {
        let ModuleStatus::Failed { error } = status(&session, id) else {
            panic!("expected a failed compilation");
        };
        assert!(error.as_parsing_failed().is_some());
    }
    let consumer = compile_module(
        &mut session,
        "consumer",
        "pub fn value() -> int { a::value() + b::value() }",
    );
    assert!(matches!(status(&session, consumer),
        ModuleStatus::WaitingForDependency { dependency } if dependency == a));
    compile_module(&mut session, "a", "pub fn value() -> int { 3 }");
    assert!(matches!(status(&session, a), ModuleStatus::Fresh));
    assert!(matches!(status(&session, consumer),
        ModuleStatus::WaitingForDependency { dependency } if dependency == b));
    compile_module(&mut session, "b", "pub fn value() -> int { 4 }");
    assert!(
        session
            .session()
            .modules()
            .iter_entries()
            .all(|(_, _, info)| matches!(info.status(), ModuleStatus::Fresh))
    );
    assert_val_eq!(session.run("consumer::value()"), int(7));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn module_status_reports_native_modules_that_need_rebuilding() {
    let mut session = TestSession::new();
    let owner = compile_module(&mut session, "owner", "pub fn value() -> int { 1 }");
    let bridge = session.session().modules().next_id();
    let path = Path::single_str("bridge");
    let mut native = Module::new(bridge, path.clone());
    native.add_wildcard_use(Path::single_str("owner"), Location::new_synthesized());
    session.session_mut().register_module(path, native);
    assert!(matches!(status(&session, bridge), ModuleStatus::Fresh));
    let consumer = compile_module(
        &mut session,
        "consumer",
        "use bridge::*; pub fn f() -> int { 7 }",
    );
    compile_module(&mut session, "owner", "pub fn value() -> int { 2 }");
    assert!(matches!(status(&session, owner), ModuleStatus::Fresh));
    assert!(matches!(
        status(&session, bridge),
        ModuleStatus::NeedsRebuild
    ));
    assert!(matches!(status(&session, consumer),
        ModuleStatus::WaitingForDependency { dependency } if dependency == bridge));
}

/// Provider compilation must not inspect impls belonging to its reverse dependencies.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn provider_recompilation_uses_only_its_compilation_environment() {
    for public_type in [false, true] {
        for load_dependent in [false, true] {
            let mut session = TestSession::new();
            let c = compile_module(
                &mut session,
                "c",
                "pub trait Conv<A, B> { fn conv(a: A, b: B) -> int; }",
            );
            let a = load_dependent.then(|| compile_module(&mut session, "a", &format!(
                "use c::Conv; {} struct X; impl Conv for <X, int> {{ fn conv(a, b) {{ 1 }} }} pub fn get() -> int {{ c::Conv::conv(X, 0) }}",
                if public_type { "pub" } else { "" },
            )));
            compile_module(
                &mut session,
                "c",
                "pub trait Conv<A, B> { fn conv(a: A, b: B) -> int; } impl<A, B> Conv for <A, B> { fn conv(a, b) { 2 } }",
            );
            assert_fresh(&session, c, "provider with a new blanket impl");
            if let Some(a) = a {
                assert_stale(&session, a, "dependent with an overlapping impl");
            }
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn provider_trait_reordering_does_not_read_stale_dependent_impls() {
    let mut session = TestSession::new();
    let c = compile_module(
        &mut session,
        "c",
        "pub trait Conv<A, B> { fn conv(a: A, b: B) -> int; }",
    );
    let a = compile_module(
        &mut session,
        "a",
        "use c::Conv; pub struct X; impl Conv for <X, int> { fn conv(a, b) { 1 } } pub fn get() -> int { c::Conv::conv(X, 0) }",
    );
    compile_module(
        &mut session,
        "c",
        "pub trait Other<A, B> { fn other(a: A, b: B) -> int; } impl<A, B> Other for <A, B> { fn other(a, b) { 2 } } pub trait Conv<A, B> { fn conv(a: A, b: B) -> int; }",
    );
    assert_fresh(&session, c, "provider with reordered traits");
    assert_fresh(&session, a, "dependent rebuilt against reordered traits");
    assert_val_eq!(session.run("a::get()"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn stale_dependencies_are_deferred_before_their_trait_ids_are_read() {
    let mut session = TestSession::new();
    let provider = "pub trait Conv<Self> { fn conv(x: Self) -> int; }";
    compile_module(&mut session, "c", provider);
    let a = compile_module(
        &mut session,
        "a",
        "pub fn get<T>(x: T) -> int where T: c::Conv { c::Conv::conv(x) }",
    );
    let e = compile_module(
        &mut session,
        "e",
        "pub fn get<T>(x: T) -> int where T: c::Conv { a::get(x) }",
    );
    compile_module(&mut session, "c", "pub fn unrelated() -> int { 0 }");
    assert_stale(&session, a, "a refers to a removed trait");
    // `a` still has a last-good signature containing the now out-of-range trait index.
    let source = "pub fn get(x) { a::get(x) }";
    let output = session.try_compile_module("new_user", source).unwrap();
    assert!(output.expr.is_none());
    assert_stale(&session, output.module_id, "new user waits for a");
    assert_eq!(
        module_has_compiled_version(session.session(), output.module_id),
        Some(false)
    );
    compile_module(&mut session, "e", source);
    assert_stale(&session, e, "existing user waits for a");

    compile_module(
        &mut session,
        "c",
        "pub trait Other<Self> { fn other(x: Self) -> int; } pub trait Conv<Self> { fn conv(x: Self) -> int; } impl Conv for int { fn conv(x: int) -> int { x + 1 } }",
    );
    for id in [a, e, output.module_id] {
        assert_fresh(&session, id, "rebuilt with new trait identities");
    }
    assert_val_eq!(session.run("new_user::get(4) + e::get(4)"), int(10));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unrelated_impls_cannot_specialize_a_functions_inferred_inputs() {
    let mut session = TestSession::new();
    compile_module(
        &mut session,
        "base",
        "pub trait Pick<Self> { fn pick(x: Self) -> int; }",
    );
    let source = "pub fn f(x) -> int { base::Pick::pick(x) }";
    let before = compile_module(&mut session, "before", source);
    compile_module(
        &mut session,
        "extension",
        "use base::Pick; pub struct X; impl Pick for X { fn pick(x: X) -> int { 7 } }",
    );
    let after = compile_module(&mut session, "after", source);
    for id in [before, after] {
        let function = session
            .session()
            .expect_fresh_module(id)
            .get_function("f".into())
            .unwrap();
        assert_eq!(function.definition.ty_scheme.ty_quantifiers.len(), 1);
    }
    assert_val_eq!(
        session.run("before::f(extension::X) + after::f(extension::X)"),
        int(14)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn the_final_expression_contributes_to_the_whole_compilation_environment() {
    let mut session = TestSession::new();
    compile_module(
        &mut session,
        "base",
        "pub trait Pick<Self> { fn pick(x: Self) -> int; }",
    );
    compile_module(
        &mut session,
        "extension",
        "use base::Pick; pub struct X; impl Pick for X { fn pick(x: X) -> int { 7 } }",
    );
    assert_val_eq!(
        session.run("fn f(x) -> int { base::Pick::pick(x) } f(extension::X)"),
        int(7)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unused_imports_still_invalidate_compilation_decisions() {
    let mut session = TestSession::new();
    compile_module(&mut session, "extension", "pub fn marker() -> int { 1 }");
    let user = compile_module(
        &mut session,
        "user",
        "use extension::*; pub fn f() -> int { 2 }",
    );
    let before = module_compilation_revision(session.session(), user);
    compile_module(&mut session, "extension", "pub fn marker() -> int { 3 }");
    assert_ne!(module_compilation_revision(session.session(), user), before);
    assert_fresh(&session, user, "unused imported module was rebuilt");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn failed_inference_retains_dependencies_for_cascade_recompilation() {
    let mut session = TestSession::new();
    compile_module(
        &mut session,
        "provider",
        "pub trait Pick<Self> { fn pick(x: Self) -> int; }",
    );
    assert!(
        session
            .try_compile_module("user", "pub fn f() -> int { provider::Pick::pick(3) }")
            .is_err()
    );
    compile_module(
        &mut session,
        "provider",
        "pub trait Pick<Self> { fn pick(x: Self) -> int; } impl Pick for int { fn pick(x: int) -> int { x + 1 } }",
    );
    assert_val_eq!(session.run("user::f()"), int(4));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_qualified_type_does_not_depend_on_a_separate_parent_module() {
    let mut session = TestSession::new();
    let child_path = Path::new(vec!["parent".into(), "child".into()]);
    session
        .session_mut()
        .compile(
            "pub struct X; pub fn marker() -> int { 1 }",
            "child",
            child_path.clone(),
        )
        .unwrap();
    let parent = compile_module(
        &mut session,
        "parent",
        "pub fn get() -> int { parent::child::marker() }",
    );
    session
        .session_mut()
        .compile("pub struct X;", "child", child_path)
        .unwrap();
    assert_stale(&session, parent, "parent calls the removed function");

    let consumer = compile_module(
        &mut session,
        "consumer",
        "pub fn f(x: parent::child::X) -> int { 7 }",
    );
    assert_fresh(&session, consumer, "the type belongs to child, not parent");
}
