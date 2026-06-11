// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;

use crate::harness::{TestSession, int, string};
use ferlium::{
    compiler::error::{CompilationErrorImpl, RuntimeErrorKind},
    hir::{
        self, ENodeArena, ENodeId, NodeKind,
        function::{ResolvedArgPassing, ResolvedValueArgPassing},
        value::Value,
    },
    module::{
        LocalDeclId, LocalStorage, ResolvedLocalClone, ResolvedLocalDrop,
        ResolvedTakeLocalValueMode, id::Id,
    },
};
use ustr::ustr;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

fn tracked_probe_value_impl() -> &'static str {
    r#"
    struct Probe(int)

    impl Value for Probe {
        fn eq(left: Probe, right: Probe) -> bool {
            left.0 == right.0
        }

        fn to_string(value: Probe) -> string {
            to_string(value.0)
        }

        fn hash(value: Probe, state: &mut hasher) {
            hash(value.0, state)
        }

        fn clone(source: Probe, target: &mut Uninit<Probe>) {
            target = Probe(source.0);
        }

        fn drop(target: &mut Probe) {
            testing::record_tracked_drop(target.0);
        }
    }
    "#
}

fn incrementing_clone_probe_value_impl() -> &'static str {
    r#"
    struct Probe(int)

    impl Value for Probe {
        fn eq(left: Probe, right: Probe) -> bool {
            left.0 == right.0
        }

        fn to_string(value: Probe) -> string {
            to_string(value.0)
        }

        fn hash(value: Probe, state: &mut hasher) {
            hash(value.0, state)
        }

        fn clone(source: Probe, target: &mut Uninit<Probe>) {
            target = Probe(source.0 + 1);
        }

        fn drop(target: &mut Probe) {
            testing::record_tracked_drop(target.0);
        }
    }
    "#
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_clone_initializes_uninit_target_without_prior_drop() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        {{
            let original = [Probe(1), Probe(2)];
            let mut cloned = original;
            original[0].0 + cloned[0].0;
            ();
        }};
        testing::tracked_drop_log()
        "#,
        incrementing_clone_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(3221));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_generic_struct_auto_derives_value() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(
            r#"
            struct Wrapper<T>(T)

            fn clone_wrapper<T>(value: T) -> Wrapper<T>
            where
                T: Value
            {
                let mut wrapped = Wrapper(value);
                wrapped
            }

            clone_wrapper(41).0
            "#
        ),
        int(41)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn lexical_drop_runs_at_block_exit() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        {{
            let owned = Probe(4);
            ();
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(4));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn lexical_drops_run_in_reverse_order() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        {{
            let first = Probe(1);
            let second = Probe(2);
            ();
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(21));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn lexical_drop_runs_on_loop_break() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        loop {{
            let first = Probe(1);
            let second = Probe(2);
            break;
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(21));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn discarded_owned_temporary_is_dropped_before_break() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        loop {{
            Probe(1);
            break;
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn call_argument_temp_is_dropped_when_later_argument_breaks() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn combine(value: Probe, other: int) -> int {{
            value.0 + other
        }}

        testing::reset_tracked_drops();
        let observed = loop {{
            combine(Probe(6), break 8)
        }};
        observed * 10 + testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(86));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn lexical_drop_runs_on_loop_continue() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        let mut i = 0;
        loop {{
            let owned = Probe(i + 1);
            i += 1;
            if i < 3 {{ continue }};
            break;
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(123));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn lexical_drop_runs_on_outer_loop_break() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        'outer: loop {{
            let outer = Probe(1);
            loop {{
                let inner = Probe(2);
                break 'outer;
            }}
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(21));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn lexical_drop_runs_on_outer_loop_continue() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        let mut i = 0;
        'outer: loop {{
            let outer = Probe(i + 1);
            i += 1;
            loop {{
                let inner = Probe(i + 4);
                if i < 3 {{ continue 'outer }};
                break 'outer;
            }}
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(516273));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn closure_drop_drops_captured_values() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        {{
            let captured = Probe(7);
            let f = || captured.0;
            ();
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(77));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_value_dictionary_for_function_type_is_compiler_provided() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(
            r#"
            fn render<T>(value: T) -> string
            where
                T: Value
            {
                to_string(value)
            }

            let f: (int) -> int = |x| x + 1;
            render(f)
            "#
        ),
        string("<function>")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generated_value_to_string_materializes_string_pieces_as_cleanup_locals() {
    let mut session = TestSession::new();
    let module = session.compile_and_get_module(
        r#"
        struct Pair(int, int)
        to_string(Pair(1, 2))
        "#,
    );

    let mut saw_shared_ref_piece_local = false;
    let mut saw_shared_ref_piece_immediate = false;
    let mut saw_cleanup_block = false;
    for (_, node) in module.hir_arena.iter() {
        if let NodeKind::Block(block) = &node.kind
            && !block.cleanup.is_empty()
        {
            saw_cleanup_block = true;
        }
        let NodeKind::StaticApply(app) = &node.kind else {
            continue;
        };
        let Some(argument) = app.arguments.get(1) else {
            continue;
        };
        if !matches!(
            argument.passing,
            ResolvedArgPassing::Value(ResolvedValueArgPassing::SharedRef)
        ) {
            continue;
        }
        match module.hir_arena[argument.value].kind {
            NodeKind::LoadLocal(_) => saw_shared_ref_piece_local = true,
            NodeKind::Immediate(_) => saw_shared_ref_piece_immediate = true,
            _ => {}
        }
    }

    assert!(
        saw_shared_ref_piece_local,
        "generated shared-ref string pieces should be loaded from explicit temporaries"
    );
    assert!(
        saw_cleanup_block,
        "generated shared-ref string piece temporaries should use ordinary block cleanup"
    );
    assert!(
        !saw_shared_ref_piece_immediate,
        "generated shared-ref string pieces should not remain immediate call arguments"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn non_place_shared_ref_call_argument_uses_explicit_temp_cleanup() {
    let mut session = TestSession::new();
    let compiled = session.compile(
        r#"
        fn id(value: string) -> string { value }
        id("hello")
        "#,
    );
    let expr = compiled.expr.expect("expected expression");
    let module = session.session().expect_fresh_module(compiled.module_id);
    let arg_local_index = expr
        .locals
        .iter()
        .position(|local| local.name.0 == ustr("$arg"))
        .expect("expected an explicit argument temporary local");
    assert!(matches!(
        expr.locals[arg_local_index].storage,
        LocalStorage::Owned { .. }
    ));
    let arg_local = LocalDeclId::from_index(arg_local_index);
    assert!(
        module.hir_arena.iter().any(|(_, node)| {
            matches!(
                &node.kind,
                NodeKind::Block(block) if block.cleanup.contains(&arg_local)
            )
        }),
        "argument temporary should be cleaned by ordinary block cleanup"
    );
}

fn expression_cleanup_drop_modes(
    session: &mut TestSession,
    source: &str,
) -> Vec<ResolvedLocalDrop> {
    let module_and_expr = session.compile(source);
    let compiled_expr = module_and_expr
        .expr
        .expect("source should compile to a root expression");
    let module = session
        .session()
        .expect_fresh_module(module_and_expr.module_id);

    module
        .hir_arena
        .iter()
        .filter_map(|(_, node)| match &node.kind {
            NodeKind::Block(block) => Some(block),
            _ => None,
        })
        .flat_map(|block| &block.cleanup)
        .filter_map(|local_id| {
            compiled_expr
                .locals
                .get(local_id.as_index())?
                .local_drop()
                .copied()
        })
        .collect()
}

fn find_return_value(arena: &ENodeArena, node: ENodeId) -> Option<ENodeId> {
    match &arena[node].kind {
        NodeKind::Return(value) => Some(*value),
        NodeKind::Block(block) => block
            .body
            .iter()
            .find_map(|node| find_return_value(arena, *node)),
        NodeKind::Case(case) => case
            .alternatives
            .iter()
            .map(|(_, node)| *node)
            .chain(std::iter::once(case.default))
            .find_map(|node| find_return_value(arena, node)),
        NodeKind::Loop(node) => find_return_value(arena, node.body),
        _ => None,
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn discarded_array_literal_with_immediate_elements_uses_semantic_drop() {
    let mut session = TestSession::new();

    let drops = expression_cleanup_drop_modes(&mut session, r#"{ ["hello", "world"]; () }"#);

    assert!(
        drops
            .iter()
            .any(|drop| !matches!(drop, ResolvedLocalDrop::Skip)),
        "discarded array literals must run semantic Value::drop before storage release"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn discarded_tuple_literal_with_immediate_elements_still_skips_semantic_drop() {
    let mut session = TestSession::new();

    let drops = expression_cleanup_drop_modes(&mut session, r#"{ ("hello", "world"); () }"#);

    assert!(
        drops.is_empty()
            || drops
                .iter()
                .all(|drop| matches!(drop, ResolvedLocalDrop::Skip)),
        "tuple storage release recursively reclaims inline elements, so immediate-only tuples do not need semantic drop"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn indexed_array_literal_owned_temp_uses_semantic_drop() {
    let mut session = TestSession::new();

    let drops = expression_cleanup_drop_modes(&mut session, r#"["hello", "world"][0]"#);

    assert!(
        drops
            .iter()
            .any(|drop| !matches!(drop, ResolvedLocalDrop::Skip)),
        "owned temporaries synthesized for array literals must run semantic Value::drop"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn lexical_drops_run_before_early_return() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn run() -> int {{
            let first = Probe(1);
            let second = Probe(2);
            return 5;
        }}

        testing::reset_tracked_drops();
        run() * 100 + testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(521));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn block_result_moves_owned_local_without_dropping_it() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn run() -> Probe {{
            let other = Probe(1);
            let result = Probe(2);
            result
        }}

        testing::reset_tracked_drops();
        let moved = run();
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn return_moves_owned_local_without_dropping_it() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn run() -> Probe {{
            let other = Probe(3);
            let result = Probe(4);
            return result;
        }}

        testing::reset_tracked_drops();
        let moved = run();
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn return_value_is_not_wrapped_in_cleanup_block() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn run() -> Probe {{
            let other = Probe(3);
            let result = Probe(4);
            return result;
        }}
        "#,
        tracked_probe_value_impl()
    );
    let module_id = session.compile(&source).module_id;
    let module = session.session().expect_fresh_module(module_id);
    let run = module.get_function(ustr("run")).unwrap();
    let entry = run.get_code_entry().unwrap();
    let return_value = find_return_value(&module.hir_arena, entry).unwrap();

    assert!(
        matches!(
            module.hir_arena[return_value].kind,
            NodeKind::TakeLocalValue(_)
        ),
        "return should carry the prepared value directly, not a cleanup wrapper block"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn break_moves_owned_loop_local_without_dropping_it() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        let moved = loop {{
            let other = Probe(5);
            let result = Probe(6);
            break result;
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(5));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn labeled_break_moves_target_loop_local_and_drops_intervening_locals() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        let moved = 'outer: loop {{
            let outer_other = Probe(5);
            let result = Probe(6);
            loop {{
                let inner = Probe(4);
                break 'outer result;
            }}
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(45));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn break_clones_owned_outer_local_when_loop_does_not_exit_its_scope() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        let source = Probe(7);
        let moved = loop {{
            break source;
        }};
        moved.0 * 100 + source.0 * 10 + testing::tracked_drop_log()
        "#,
        incrementing_clone_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(870));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_mut_let_drop_uses_value_dictionary() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn scoped<T>(value: T)
        where
            T: Value
        {{
            let mut owned = value;
            ();
        }}

        testing::reset_tracked_drops();
        scoped(Probe(8));
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(88));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment_overwrite_drops_old_value() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        {{
            let mut value = Probe(1);
            value = Probe(2);
            ();
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(12));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn field_assignment_overwrite_drops_old_value() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        struct Wrapper<T>(T)

        testing::reset_tracked_drops();
        {{
            let mut wrapper = Wrapper(Probe(3));
            wrapper.0 = Probe(4);
            ();
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(34));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn owned_function_argument_is_dropped_at_function_exit() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn consume(value: Probe) {{
            ();
        }}

        testing::reset_tracked_drops();
        consume(Probe(5));
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(5));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn alias_bindings_are_not_dropped_separately() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        {{
            let original = Probe(3);
            let alias = original;
            ();
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn let_binding_from_mutable_generic_place_owns_snapshot() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn swap<T>(a: &mut T, b: &mut T)
        where
            T: Value
        {{
            let temp = b;
            b = a;
            a = temp;
        }}

        let mut values = [Probe(0), Probe(1)];
        swap(values[0], values[1]);
        values[0].0 * 10 + values[1].0
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(10));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_let_from_mutable_place_uses_value_clone_and_owns_snapshot() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn snapshot<T>(slot: &mut T) -> T
        where
            T: Value
        {{
            let owned = slot;
            owned
        }}

        testing::reset_tracked_drops();
        let observed = {{
            let mut source = Probe(2);
            let copy = snapshot(source);
            source = Probe(5);
            copy.0 * 10 + source.0
        }};
        observed * 1000 + testing::tracked_drop_log()
        "#,
        incrementing_clone_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(35235));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_owned_argument_from_mutable_place_uses_value_clone_and_owns_snapshot() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        struct Wrapper<T>(T)

        fn wrap<T>(value: T) -> Wrapper<T>
        where
            T: Value
        {{
            Wrapper(value)
        }}

        testing::reset_tracked_drops();
        let observed = {{
            let mut source = Probe(2);
            let wrapped = wrap(source);
            source = Probe(5);
            wrapped.0.0 * 10 + source.0
        }};
        observed * 1000 + testing::tracked_drop_log()
        "#,
        incrementing_clone_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(35235));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn concrete_trivial_copy_call_argument_uses_trivial_copy_passing() {
    let mut session = TestSession::new();
    let module = session.compile_and_get_module(
        r#"
        fn id(value: int) -> int {
            value
        }

        id(1)
        "#,
    );

    assert!(
        module.hir_arena.iter().any(|(_, node)| {
            let NodeKind::StaticApply(app) = &node.kind else {
                return false;
            };
            app.arguments.iter().any(|argument| {
                matches!(
                    argument.passing,
                    ResolvedArgPassing::Value(ResolvedValueArgPassing::TrivialCopy)
                )
            })
        }),
        "expected concrete int call argument to use trivial-copy passing"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mutable_concrete_trivial_copy_place_lowers_to_snapshot_copy() {
    let source = r#"
        fn snapshot(slot: &mut int) -> int {
            let copy = slot;
            copy
        }

        let mut source = 1;
        let copy = snapshot(source);
        source = 2;
        copy * 10 + source
    "#;

    let mut compile_session = TestSession::new();
    let module = compile_session.compile_and_get_module(source);
    assert!(
        module.hir_arena.iter().any(|(_, node)| matches!(
            node.kind,
            NodeKind::CloneValue(hir::CloneValue {
                clone: ResolvedLocalClone::TrivialCopy,
                ..
            })
        )),
        "expected mutable int place materialization to lower through trivial-copy CloneValue"
    );
    assert!(
        !module.hir_arena.iter().any(|(_, node)| matches!(
            node.kind,
            NodeKind::CloneValue(hir::CloneValue {
                clone: ResolvedLocalClone::Static(_) | ResolvedLocalClone::Dictionary(_),
                ..
            })
        )),
        "expected no non-trivial clone for trivial-copy materialization"
    );

    let mut run_session = TestSession::new();
    assert_val_eq!(run_session.run(source), int(12));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn inferred_mutable_let_clone_resolves_to_trivial_copy_after_unification() {
    let source = r#"
        fn snapshot(slot) -> int {
            let copy = slot;
            copy
        }

        let mut source = 1;
        let copy = snapshot(source);
        source = 2;
        copy * 10 + source
    "#;

    let mut compile_session = TestSession::new();
    let module = compile_session.compile_and_get_module(source);
    assert!(
        module.hir_arena.iter().any(|(_, node)| matches!(
            node.kind,
            NodeKind::TakeLocalValue(hir::TakeLocalValue {
                mode: ResolvedTakeLocalValueMode::CloneBorrowed(ResolvedLocalClone::TrivialCopy),
                ..
            })
        )),
        "expected inferred owned materialization to resolve to trivial copy"
    );

    let mut run_session = TestSession::new();
    assert_val_eq!(run_session.run(source), int(12));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn inferred_projection_materialization_resolves_to_trivial_copy_after_unification() {
    let source = r#"
        fn first(pair: &mut (int, int)) -> int {
            pair.0
        }

        let mut pair = (1, 2);
        first(pair)
    "#;

    let mut compile_session = TestSession::new();
    let module = compile_session.compile_and_get_module(source);
    assert!(
        module.hir_arena.iter().any(|(_, node)| matches!(
            node.kind,
            NodeKind::CloneValue(hir::CloneValue {
                clone: ResolvedLocalClone::TrivialCopy,
                ..
            })
        )),
        "expected projected int place materialization to resolve to trivial-copy CloneValue"
    );
    assert!(
        !module.hir_arena.iter().any(|(_, node)| matches!(
            node.kind,
            NodeKind::CloneValue(hir::CloneValue {
                clone: ResolvedLocalClone::Static(_) | ResolvedLocalClone::Dictionary(_),
                ..
            })
        )),
        "expected no non-trivial clone for trivial-copy projected materialization"
    );

    let mut run_session = TestSession::new();
    assert_val_eq!(run_session.run(source), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unused_owned_temporary_is_dropped() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        testing::reset_tracked_drops();
        {{
            Probe(9);
            ();
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(9));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn temporary_array_index_shared_ref_base_is_dropped() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn payload(value: Probe) -> int {{
            value.0
        }}

        testing::reset_tracked_drops();
        let observed = payload([Probe(3)][0]);
        observed * 10 + testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(33));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn temporary_tuple_projection_shared_ref_base_is_dropped() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn payload(value: Probe) -> int {{
            value.0
        }}

        testing::reset_tracked_drops();
        let observed = payload((Probe(4),).0);
        observed * 10 + testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(44));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn temporary_record_projection_shared_ref_base_is_dropped() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn payload(value: Probe) -> int {{
            value.0
        }}

        testing::reset_tracked_drops();
        let observed = payload({{item: Probe(5)}}.item);
        observed * 10 + testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(55));
}

// A temporary used as a place base (here an indexed array literal) is dropped when a sibling
// argument returns before the call.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_index_base_temp_is_dropped_when_later_argument_returns() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn combine(value: Probe, other: int) -> int {{
            value.0 + other
        }}

        fn run() -> int {{
            combine([Probe(6)][0], {{ return 8 }})
        }}

        testing::reset_tracked_drops();
        run() * 10 + testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(86));
}

// A discarded owned temporary is dropped when a later statement returns out of the block.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn discarded_owned_temporary_is_dropped_before_early_return() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn run() -> int {{
            Probe(6);
            return 8;
        }}

        testing::reset_tracked_drops();
        run() * 10 + testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(86));
}

// An owned temporary passed as a call argument is dropped when a later argument returns out of
// the block before the call runs.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn call_argument_temp_is_dropped_when_later_argument_returns() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn combine(value: Probe, other: int) -> int {{
            value.0 + other
        }}

        fn run() -> int {{
            combine(Probe(6), {{ return 8 }})
        }}

        testing::reset_tracked_drops();
        run() * 10 + testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(86));
}

// As above, but the later argument returns at *run time* (a conditional return on a runtime value),
// so the call is not statically elided and reaches argument evaluation: the already-evaluated
// temporary must still be dropped when evaluation unwinds out of the call.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn call_argument_temp_is_dropped_when_later_argument_returns_at_runtime() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn combine(value: Probe, other: int) -> int {{
            value.0 + other
        }}

        fn run(c: bool) -> int {{
            combine(Probe(6), if c {{ return 8 }} else {{ 0 }})
        }}

        testing::reset_tracked_drops();
        run(true) * 10 + testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(86));
}

// As above, but the later argument *errors* at run time rather than returning. The error aborts
// the script before it can read the drop log, so the log is observed via a follow-up run (the
// tracked-drop counter is process-global and nextest isolates each test in its own process).
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn call_argument_temp_is_dropped_when_later_argument_errors_at_runtime() {
    let mut session = TestSession::new();
    let erroring = format!(
        r#"
        {}
        fn combine(value: Probe, other: int) -> int {{
            value.0 + other
        }}

        testing::reset_tracked_drops();
        combine(Probe(6), [0][1])
        "#,
        tracked_probe_value_impl()
    );
    assert!(
        session.try_run(&erroring).is_err(),
        "expected a runtime out-of-bounds error"
    );
    assert_val_eq!(session.run("testing::tracked_drop_log()"), int(6));
}

// An owned temporary used as an aggregate element is dropped when a later element returns out of
// the block before the aggregate is built.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn tuple_element_temp_is_dropped_when_later_element_returns() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn run() -> int {{
            let pair = (Probe(6), {{ return 8 }});
            pair.1
        }}

        testing::reset_tracked_drops();
        run() * 10 + testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(86));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn lexical_drop_runs_on_runtime_error() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn run() -> int {{
            let owned = Probe(5);
            [1][1]
        }}
        testing::reset_tracked_drops();
        run()
        "#,
        tracked_probe_value_impl()
    );
    assert_eq!(
        session.fail_run(&source),
        RuntimeErrorKind::Aborted(Some(
            "Array access out of bounds: index 1 for length 1".to_string()
        ))
    );
    assert_val_eq!(session.run("testing::tracked_drop_log()"), int(5));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_value_drop_runs_on_runtime_error() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        fn fail_with_owned<T>(value: T) -> int
        where
            T: Value
        {{
            let mut owned = value;
            [1][1]
        }}

        testing::reset_tracked_drops();
        fail_with_owned(Probe(6))
        "#,
        tracked_probe_value_impl()
    );
    assert_eq!(
        session.fail_run(&source),
        RuntimeErrorKind::Aborted(Some(
            "Array access out of bounds: index 1 for length 1".to_string()
        ))
    );
    assert_val_eq!(session.run("testing::tracked_drop_log()"), int(66));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn auto_derived_struct_value_clone_uses_field_clone() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(
            r#"
            struct Probe(int)
            struct Wrapper<T>(T)

            impl Value for Probe {
                fn eq(left: Probe, right: Probe) -> bool {
                    left.0 == right.0
                }

                fn to_string(value: Probe) -> string {
                    to_string(value.0)
                }

                fn hash(value: Probe, state: &mut hasher) {
                    hash(value.0, state)
                }

                fn clone(source: Probe, target: &mut Uninit<Probe>) {
                    target = Probe(source.0 + 10);
                }

                fn drop(target: &mut Probe) {}
            }

            let original = Wrapper(Probe(5));
            let mut cloned = original;
            (original.0.0, cloned.0.0)
            "#
        ),
        tuple!(int(5), int(15))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_generic_enum_auto_derives_value() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(
            r#"
            struct Probe(int)

            enum Boxed<T> {
                Empty,
                Item(T),
            }

            impl Value for Probe {
                fn eq(left: Probe, right: Probe) -> bool {
                    left.0 == right.0
                }

                fn to_string(value: Probe) -> string {
                    to_string(value.0)
                }

                fn hash(value: Probe, state: &mut hasher) {
                    hash(value.0, state)
                }

                fn clone(source: Probe, target: &mut Uninit<Probe>) {
                    target = Probe(source.0 + 10);
                }

                fn drop(target: &mut Probe) {}
            }

            fn clone_boxed<T>(value: Boxed<T>) -> Boxed<T>
            where
                T: Value
            {
                let mut boxed = value;
                boxed
            }

            match clone_boxed(Boxed::Item(Probe(7))) {
                Item(value) => value.0,
                Empty => 0,
            }
            "#
        ),
        int(17)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn auto_derived_nested_value_drop_uses_member_drop() {
    let mut session = TestSession::new();
    let source = format!(
        r#"
        {}
        struct Wrapper<T>(T)

        enum Boxed<T> {{
            Empty,
            Item(Wrapper<T>),
        }}

        testing::reset_tracked_drops();
        {{
            let boxed = Boxed::Item(Wrapper(Probe(6)));
            ();
        }};
        testing::tracked_drop_log()
        "#,
        tracked_probe_value_impl()
    );
    assert_val_eq!(session.run(&source), int(6));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn explicit_concrete_value_impl_suppresses_auto_blanket_impl() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(
            r#"
            struct Wrapper<T>(T)

            impl Value for Wrapper<int> {
                fn eq(left: Wrapper<int>, right: Wrapper<int>) -> bool {
                    left.0 == right.0
                }

                fn to_string(value: Wrapper<int>) -> string {
                    "custom"
                }

                fn hash(value: Wrapper<int>, state: &mut hasher) {
                    hash(value.0, state)
                }

                fn clone(source: Wrapper<int>, target: &mut Uninit<Wrapper<int>>) {
                    target = Wrapper(source.0 + 10);
                }

                fn drop(target: &mut Wrapper<int>) {}
            }

            let original = Wrapper(1);
            let mut cloned = original;
            cloned.0
            "#
        ),
        int(11)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn value_impl_for_foreign_named_adt_is_rejected() {
    let mut session = TestSession::new();
    session
        .try_compile_module("a", "pub struct Foreign(int)")
        .unwrap();
    let err = session
        .try_compile_module(
            "b",
            r#"
            impl Value for a::Foreign {
                fn eq(left: a::Foreign, right: a::Foreign) -> bool {
                    left.0 == right.0
                }

                fn to_string(value: a::Foreign) -> string {
                    to_string(value.0)
                }

                fn hash(value: a::Foreign, state: &mut hasher) {
                    hash(value.0, state)
                }

                fn clone(source: a::Foreign, target: &mut Uninit<a::Foreign>) {
                    target = source;
                }

                fn drop(target: &mut a::Foreign) {}
            }
            "#,
        )
        .expect_err("expected foreign Value impl to be rejected");
    match err.into_inner() {
        CompilationErrorImpl::TraitImplOrphanRuleViolation { .. } => {}
        other => panic!("expected TraitImplOrphanRuleViolation, got {other:?}"),
    }
}

// Testing the callee-side parameter passing metadata used by SSA lowering,
// as described in `doc/hir-ownership.md` ("Call Argument Passing").

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn concrete_trivial_copy_parameter_resolves_to_trivial_copy() {
    let mut session = TestSession::new();
    let module = session.compile_and_get_module("fn id(value: int) -> int { value } id(1)");
    assert_eq!(
        module
            .get_function(ustr("id"))
            .unwrap()
            .parameter_passing
            .as_slice(),
        &[ResolvedArgPassing::Value(
            ResolvedValueArgPassing::TrivialCopy,
        )][..],
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn non_trivial_copy_value_parameter_resolves_to_shared_ref() {
    let mut session = TestSession::new();
    let module = session.compile_and_get_module(
        r#"
        fn identity(value: string) -> string { value }
        identity("hello")
        "#,
    );
    assert_eq!(
        module
            .get_function(ustr("identity"))
            .unwrap()
            .parameter_passing
            .as_slice(),
        &[ResolvedArgPassing::Value(
            ResolvedValueArgPassing::SharedRef
        )][..]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mutable_parameter_resolves_to_mutable_ref() {
    let mut session = TestSession::new();
    let module = session.compile_and_get_module(
        r#"
        fn store(slot: &mut int) { slot = 1; }
        let mut value = 0;
        store(value)
        "#,
    );
    assert_eq!(
        module
            .get_function(ustr("store"))
            .unwrap()
            .parameter_passing
            .as_slice(),
        &[ResolvedArgPassing::MutableRef][..]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_value_parameter_resolves_to_shared_ref() {
    // A generic parameter is not treated as `TrivialCopy` even under a `Value` constraint.
    let mut session = TestSession::new();
    let module = session.compile_and_get_module(
        r#"
        fn identity<T>(value: T) -> T where T: Value { value }
        identity("hello")
        "#,
    );
    assert_eq!(
        module
            .get_function(ustr("identity"))
            .unwrap()
            .parameter_passing
            .as_slice(),
        &[ResolvedArgPassing::Value(
            ResolvedValueArgPassing::SharedRef
        )][..]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn multiple_parameters_preserve_declaration_order() {
    let mut session = TestSession::new();
    let module = session.compile_and_get_module(
        r#"
        fn mix(a: int, b: string, c: &mut int) -> int { c = a; a }
        let mut value = 0;
        mix(1, "hello", value)
        "#,
    );
    assert_eq!(
        module
            .get_function(ustr("mix"))
            .unwrap()
            .parameter_passing
            .as_slice(),
        &[
            ResolvedArgPassing::Value(ResolvedValueArgPassing::TrivialCopy),
            ResolvedArgPassing::Value(ResolvedValueArgPassing::SharedRef),
            ResolvedArgPassing::MutableRef,
        ][..],
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn context_native_parameter_passing_excludes_hidden_dictionary_args() {
    let session = TestSession::new();
    let function = session
        .session()
        .std_module()
        .get_function(ustr("buffer_drop_at"))
        .unwrap();
    assert_eq!(
        function.parameter_passing.as_slice(),
        &[
            ResolvedArgPassing::MutableRef,
            ResolvedArgPassing::Value(ResolvedValueArgPassing::TrivialCopy),
        ][..],
    );
    assert_eq!(
        function.code.runtime_argument_passing().unwrap(),
        &[
            ResolvedArgPassing::Value(ResolvedValueArgPassing::SharedRef),
            ResolvedArgPassing::MutableRef,
            ResolvedArgPassing::Value(ResolvedValueArgPassing::TrivialCopy),
        ][..],
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn discarded_empty_struct_temporary_runs_semantic_drop() {
    let mut session = TestSession::new();
    let source = r#"
        struct Empty {}

        impl Value for Empty {
            fn eq(left: Empty, right: Empty) -> bool { true }
            fn to_string(value: Empty) -> string { "" }
            fn hash(value: Empty, state: &mut hasher) { }
            fn clone(source: Empty, target: &mut Uninit<Empty>) { target = Empty{}; }
            fn drop(target: &mut Empty) {
                testing::record_tracked_drop(1);
            }
        }

        testing::reset_tracked_drops();
        if true {
          Empty{};
        };
        testing::tracked_drop_log()
    "#;
    assert_val_eq!(session.run(source), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn discarded_nonempty_struct_temporary_runs_semantic_drop() {
    let mut session = TestSession::new();
    let source = r#"
        struct NonEmpty { value: int }

        impl Value for NonEmpty {
            fn eq(left: NonEmpty, right: NonEmpty) -> bool { true }
            fn to_string(value: NonEmpty) -> string { "" }
            fn hash(value: NonEmpty, state: &mut hasher) { }
            fn clone(source: NonEmpty, target: &mut Uninit<NonEmpty>) { target = NonEmpty{value: 0}; }
            fn drop(target: &mut NonEmpty) {
                testing::record_tracked_drop(1);
            }
        }

        testing::reset_tracked_drops();
        if true {
          NonEmpty{value: 7};
        };
        testing::tracked_drop_log()
    "#;
    assert_val_eq!(session.run(source), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn discarded_bool_struct_temporary_runs_semantic_drop() {
    let mut session = TestSession::new();
    let source = r#"
        struct Wrap { value: bool }

        impl Value for Wrap {
            fn eq(left: Wrap, right: Wrap) -> bool { true }
            fn to_string(value: Wrap) -> string { "" }
            fn hash(value: Wrap, state: &mut hasher) { }
            fn clone(source: Wrap, target: &mut Uninit<Wrap>) { target = Wrap{value: false}; }
            fn drop(target: &mut Wrap) {
                testing::record_tracked_drop(1);
            }
        }

        testing::reset_tracked_drops();
        if true {
          Wrap{value: true};
        };
        testing::tracked_drop_log()
    "#;
    assert_val_eq!(session.run(source), int(1));
}
