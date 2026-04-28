// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;

use ferlium::{
    CompilerSession, Path,
    eval::ValOrMut,
    hir::value::Value,
    module::{ModuleId, id::Id},
    types::r#type::Type,
};

use crate::harness::{TestSession, int};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

// ── Helpers ──────────────────────────────────────────────────────────────────

/// Compile `code` as a module named `name` (single-segment path) and return
/// its [`ModuleId`]. Panics only if the compiler returns `Err`; a stale result
/// (e.g. due to stale dependencies) is still considered a success.
fn compile_module(session: &mut TestSession, name: &str, code: &str) -> ModuleId {
    session
        .try_compile_module(name, code)
        .unwrap_or_else(|e| panic!("compile_module({name:?}) failed unexpectedly: {e:?}"))
        .module_id
}

/// Assert that the module `id` is fresh (not stale).
#[track_caller]
fn assert_fresh(session: &TestSession, id: ModuleId, label: &str) {
    assert!(
        !session
            .session()
            .get_module_entry_by_id(id)
            .unwrap()
            .is_stale(),
        "{label} should be fresh"
    );
}

/// Assert that the module `id` is stale.
#[track_caller]
fn assert_stale(session: &TestSession, id: ModuleId, label: &str) {
    assert!(
        session
            .session()
            .get_module_entry_by_id(id)
            .unwrap()
            .is_stale(),
        "{label} should be stale"
    );
}

/// Recompile `name` with syntactically invalid code, asserting the call returns
/// `Err` so the test fails loudly if the language ever accepts the garbage.
fn break_module(session: &mut TestSession, name: &str) {
    assert!(
        session
            .try_compile_module(name, "this is not valid ferlium !!!")
            .is_err(),
        "breaking module {name:?} should produce a compilation error"
    );
}

// ── Tests ─────────────────────────────────────────────────────────────────────

/// When a dependency fails to (re)compile, the failing module *and* every
/// module that (directly or transitively) depends on it must be marked stale.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn stale_propagates_on_dep_failure() {
    let mut session = TestSession::new();

    let base_id = compile_module(&mut session, "base", "fn val() -> int { 1 }");
    let user_id = compile_module(&mut session, "user", "fn result() -> int { base::val() }");

    assert_fresh(&session, base_id, "base (initial)");
    assert_fresh(&session, user_id, "user (initial)");

    break_module(&mut session, "base");

    assert_stale(&session, base_id, "base after breakage");
    assert_stale(&session, user_id, "user after base breakage (transitive)");
}

/// After a broken dependency is fixed, its direct stale dependent must be
/// automatically cascade-recompiled and become fresh again.
/// The recompiled dependent must also produce the correct value at run-time.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn cascade_recompile_direct_dep() {
    let mut session = TestSession::new();

    let base_id = compile_module(&mut session, "base", "fn val() -> int { 1 }");
    let user_id = compile_module(&mut session, "user", "fn result() -> int { base::val() }");

    break_module(&mut session, "base");
    assert_stale(&session, base_id, "base");
    assert_stale(&session, user_id, "user");

    // Fix base — user must be cascade-recompiled automatically.
    session
        .try_compile_module("base", "fn val() -> int { 1 }")
        .expect("fixing base should succeed");

    assert_fresh(&session, base_id, "base after fix");
    assert_fresh(&session, user_id, "user after cascade recompile");

    // Verify the module is really compiled (not a phantom fresh entry).
    assert!(
        session
            .session()
            .get_module_entry_by_id(user_id)
            .unwrap()
            .module()
            .is_some(),
        "user must have a compiled module after cascade recompile"
    );

    // Verify run-time correctness.
    assert_val_eq!(session.run("user::result()"), int(1));
}

/// Cascade recompilation propagates transitively through a linear chain
/// A → B → C: fixing A must ultimately make C fresh too.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn cascade_recompile_chain() {
    let mut session = TestSession::new();

    let a_id = compile_module(&mut session, "a", "fn val() -> int { 1 }");
    let b_id = compile_module(&mut session, "b", "fn val() -> int { a::val() + 1 }");
    let c_id = compile_module(&mut session, "c", "fn val() -> int { b::val() + 1 }");

    assert_fresh(&session, a_id, "a (initial)");
    assert_fresh(&session, b_id, "b (initial)");
    assert_fresh(&session, c_id, "c (initial)");

    break_module(&mut session, "a");
    assert_stale(&session, a_id, "a");
    assert_stale(&session, b_id, "b");
    assert_stale(&session, c_id, "c");

    // Fix a — b is recompiled (a is fresh), which then recompiles c.
    session
        .try_compile_module("a", "fn val() -> int { 1 }")
        .expect("fixing a should succeed");

    assert_fresh(&session, a_id, "a after fix");
    assert_fresh(&session, b_id, "b after cascade");
    assert_fresh(&session, c_id, "c after transitive cascade");

    // Verify run-time correctness end-to-end.
    assert_val_eq!(session.run("c::val()"), int(3));
}

/// Diamond dependency: base → {b, c} → d.
/// After base is broken and fixed all four modules must end up fresh.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn cascade_recompile_diamond() {
    let mut session = TestSession::new();

    let base_id = compile_module(&mut session, "base", "fn val() -> int { 1 }");
    let b_id = compile_module(&mut session, "b", "fn val() -> int { base::val() }");
    let c_id = compile_module(&mut session, "c", "fn val() -> int { base::val() }");
    let d_id = compile_module(&mut session, "d", "fn val() -> int { b::val() + c::val() }");

    assert_fresh(&session, base_id, "base (initial)");
    assert_fresh(&session, b_id, "b (initial)");
    assert_fresh(&session, c_id, "c (initial)");
    assert_fresh(&session, d_id, "d (initial)");

    break_module(&mut session, "base");
    assert_stale(&session, base_id, "base");
    assert_stale(&session, b_id, "b");
    assert_stale(&session, c_id, "c");
    assert_stale(&session, d_id, "d");

    session
        .try_compile_module("base", "fn val() -> int { 1 }")
        .expect("fixing base should succeed");

    assert_fresh(&session, base_id, "base after fix");
    assert_fresh(&session, b_id, "b after cascade");
    assert_fresh(&session, c_id, "c after cascade");
    assert_fresh(&session, d_id, "d after diamond cascade");

    assert_val_eq!(session.run("d::val()"), int(2));
}

/// A module compiled for the *first time* while one of its dependencies is
/// already stale must have its source info recorded so that it can be
/// cascade-recompiled automatically once the dependency is fixed.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn cascade_recompile_first_compile_with_stale_dep() {
    let mut session = TestSession::new();

    let base_id = compile_module(&mut session, "base", "fn val() -> int { 42 }");

    // Break base (old module is preserved inside the entry, so user can still
    // be compiled against it — but will be marked stale due to stale dep).
    break_module(&mut session, "base");
    assert_stale(&session, base_id, "base");

    // Compile user for the first time while base is stale.
    let user_id = compile_module(&mut session, "user", "fn result() -> int { base::val() }");
    assert_stale(&session, user_id, "user (first compile with stale dep)");

    // Fix base — user should be cascade-recompiled.
    session
        .try_compile_module("base", "fn val() -> int { 42 }")
        .expect("fixing base should succeed");

    assert_fresh(&session, base_id, "base after fix");
    assert_fresh(&session, user_id, "user after cascade recompile");

    assert_val_eq!(session.run("user::result()"), int(42));
}

/// When a module is *re*compiled and its new version introduces a dependency
/// on a *stale* module, the module's own existing dependents must be marked
/// stale as well — not just the module itself.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn stale_propagates_when_new_dep_introduced() {
    let mut session = TestSession::new();

    let base_id = compile_module(&mut session, "base", "fn val() -> int { 1 }");
    // mid initially has NO dependency on base.
    let mid_id = compile_module(&mut session, "mid", "fn val() -> int { 2 }");
    // top depends on mid.
    let top_id = compile_module(&mut session, "top", "fn val() -> int { mid::val() }");

    assert_fresh(&session, base_id, "base (initial)");
    assert_fresh(&session, mid_id, "mid (initial)");
    assert_fresh(&session, top_id, "top (initial)");

    // Break base; only base becomes stale — mid/top don't depend on it yet.
    break_module(&mut session, "base");
    assert_stale(&session, base_id, "base");
    assert_fresh(&session, mid_id, "mid (no base dep yet)");
    assert_fresh(&session, top_id, "top (no base dep yet)");

    // Re-compile mid so it NOW depends on the stale base.
    compile_module(&mut session, "mid", "fn val() -> int { base::val() }");

    // mid is stale because base is stale; top must also be stale because it
    // depends on mid which just became stale.
    assert_stale(&session, mid_id, "mid after gaining stale dep");
    assert_stale(&session, top_id, "top after mid gained stale dep");

    // Fix base — mid and top should both be cascade-recompiled.
    session
        .try_compile_module("base", "fn val() -> int { 1 }")
        .expect("fixing base should succeed");

    assert_fresh(&session, base_id, "base after fix");
    assert_fresh(&session, mid_id, "mid after cascade");
    assert_fresh(&session, top_id, "top after cascade");

    assert_val_eq!(session.run("top::val()"), int(1));
}

/// Attempting to introduce a circular dependency during *re*compilation must be
/// rejected with a [`CircularImportDependency`] error and must **not** cause
/// infinite recursion in the cascade recompilation pipeline.
///
/// The cycle detection guard (`find_module_deps_cycle` in `lib.rs`) acts as the
/// firewall: it fires before any cascade recompile is scheduled, so the pipeline
/// can never enter a cycle. This test ensures that guard is functional.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn no_infinite_recursion_on_circular_dep() {
    let mut session = TestSession::new();

    // Establish a linear chain: b depends on a.
    let a_id = compile_module(&mut session, "a", "fn val() -> int { 1 }");
    let b_id = compile_module(&mut session, "b", "fn val() -> int { a::val() + 1 }");

    assert_fresh(&session, a_id, "a (initial)");
    assert_fresh(&session, b_id, "b (initial)");

    // Attempting to recompile `a` so it now depends on `b` would create the
    // cycle a → b → a.  The compiler must reject this with a
    // CircularImportDependency error rather than entering infinite recursion.
    let err = session
        .try_compile_module("a", "fn val() -> int { b::val() }")
        .unwrap_err();

    // The error must be the cycle-detection variant.
    err.as_circular_import_dependency()
        .expect("expected a CircularImportDependency error for a → b → a cycle");

    // After the rejected recompile, both modules must be stale:
    //   • a — compilation failed, so update_with_compilation_error marks it stale.
    //   • b — mark_stale_transitively propagates staleness from a to b.
    assert_stale(&session, a_id, "a after rejected circular recompile");
    assert_stale(&session, b_id, "b after a became stale");

    // The session must still be in a consistent state: both entries must still
    // exist and be query-able (no panic, no missing entries).
    assert!(
        session.session().get_module_entry_by_id(a_id).is_some(),
        "a's entry must still exist after rejected circular recompile"
    );
    assert!(
        session.session().get_module_entry_by_id(b_id).is_some(),
        "b's entry must still exist after rejected circular recompile"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn module_source_versions_and_compilation_revisions_are_tracked() {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            "fn val() -> int { 1 }",
            "tracked",
            Path::single_str("tracked"),
        )
        .expect("initial compile should succeed")
        .module_id;

    let entry = session.get_module_entry_by_id(module_id).unwrap();
    assert_eq!(entry.source_version().unwrap().as_index(), 0);
    assert_eq!(entry.compilation_revision().as_index(), 0);

    let changed = session
        .update_module_source(module_id, "fn val() -> int { 2 }")
        .expect("source update should be accepted");
    assert_eq!(changed.source_version.as_index(), 1);
    assert_eq!(changed.compilation_revision.as_index(), 1);
    assert!(changed.diagnostics.is_empty());
    assert_eq!(
        session.get_module_source(module_id).unwrap().source,
        "fn val() -> int { 2 }"
    );

    let unchanged = session
        .update_module_source(module_id, "fn val() -> int { 2 }")
        .expect("same-source update should still compile");
    assert_eq!(unchanged.source_version.as_index(), 1);
    assert_eq!(unchanged.compilation_revision.as_index(), 2);
    assert!(unchanged.diagnostics.is_empty());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn failed_module_source_update_records_diagnostics_and_keeps_last_good_module() {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            "fn val() -> int { 1 }",
            "broken",
            Path::single_str("broken"),
        )
        .expect("initial compile should succeed")
        .module_id;

    let update = session
        .update_module_source(module_id, "this is not valid ferlium !!!")
        .expect("source update should be accepted even when compilation fails");

    assert_eq!(update.source_version.as_index(), 1);
    assert_eq!(update.compilation_revision.as_index(), 1);
    assert!(!update.diagnostics.is_empty());
    assert_eq!(
        session
            .get_module_entry_by_id(module_id)
            .unwrap()
            .diagnostics()
            .len(),
        update.diagnostics.len()
    );
    assert!(
        session
            .get_module_entry_by_id(module_id)
            .unwrap()
            .is_stale()
    );
    assert!(
        session
            .expect_compiled_module(module_id)
            .get_function(ferlium::ustr("val"))
            .is_some(),
        "last good module should remain available after failed update"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn dependency_query_apis_report_direct_reverse_and_affected_modules() {
    let mut session = CompilerSession::new();
    let base_id = session
        .compile("fn val() -> int { 1 }", "base", Path::single_str("base"))
        .expect("base should compile")
        .module_id;
    let mid_id = session
        .compile(
            "fn val() -> int { base::val() }",
            "mid",
            Path::single_str("mid"),
        )
        .expect("mid should compile")
        .module_id;
    let top_id = session
        .compile(
            "fn val() -> int { mid::val() }",
            "top",
            Path::single_str("top"),
        )
        .expect("top should compile")
        .module_id;

    assert!(
        session
            .get_module_entry_by_id(mid_id)
            .unwrap()
            .latest_deps()
            .contains(&base_id)
    );
    assert_eq!(session.get_module_reverse_deps(base_id), vec![mid_id]);

    let affected = session.get_modules_affected_by(base_id);
    assert!(affected.contains(&mid_id));
    assert!(affected.contains(&top_id));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn value_to_string_renders_int_correctly() {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile("", "<test>", Path::single_str("test"))
        .unwrap()
        .module_id;

    let rendered = session
        .value_to_string(
            module_id,
            Value::native(42isize),
            Type::primitive::<isize>(),
        )
        .unwrap();

    assert_eq!(rendered, "42");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn eval_expression_in_module_executes_inferred_single_arg_function() {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            "fn add_one(x) { x + 1 }",
            "<test>",
            Path::single_str("test"),
        )
        .unwrap()
        .module_id;

    let (value, ty) = session
        .eval_expression_in_module(
            module_id,
            "<test_expr>",
            "add_one((arg0: int))",
            vec![(
                "arg0",
                Type::primitive::<isize>(),
                ValOrMut::Val(Value::native(5isize)),
            )],
        )
        .unwrap();

    assert_eq!(value.as_primitive_ty::<isize>().copied(), Some(6));
    assert_eq!(ty, Type::primitive::<isize>());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn eval_expression_in_module_executes_inferred_multi_arg_function() {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            "fn mix(a, b) { a * 2 + b }",
            "<test>",
            Path::single_str("test"),
        )
        .unwrap()
        .module_id;

    let (value, ty) = session
        .eval_expression_in_module(
            module_id,
            "<test_expr>",
            "mix((arg0: int), (arg1: int))",
            vec![
                (
                    "arg0",
                    Type::primitive::<isize>(),
                    ValOrMut::Val(Value::native(20isize)),
                ),
                (
                    "arg1",
                    Type::primitive::<isize>(),
                    ValOrMut::Val(Value::native(2isize)),
                ),
            ],
        )
        .unwrap();

    assert_eq!(value.as_primitive_ty::<isize>().copied(), Some(42));
    assert_eq!(ty, Type::primitive::<isize>());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn eval_expression_in_module_does_not_change_module_source_version() {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            "fn add_one(x) { x + 1 }",
            "<test>",
            Path::single_str("test"),
        )
        .unwrap()
        .module_id;
    let source_version = session
        .get_module_entry_by_id(module_id)
        .unwrap()
        .source_version();

    session
        .eval_expression_in_module(
            module_id,
            "<test_expr>",
            "add_one((arg0: int))",
            vec![(
                "arg0",
                Type::primitive::<isize>(),
                ValOrMut::Val(Value::native(5isize)),
            )],
        )
        .unwrap();

    assert_eq!(
        session
            .get_module_entry_by_id(module_id)
            .unwrap()
            .source_version(),
        source_version
    );
}
