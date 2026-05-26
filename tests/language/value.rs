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
        self, NodeKind,
        function::{ArgPassing, ResolvedValueArgPassing, SharedRefTempCleanup, ValueArgPassing},
        value::Value,
    },
    module::{LocalClone, ResolvedLocalClone, TakeLocalValueMode},
};

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

        fn clone(source: Probe, target: &mut Probe) {
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

        fn clone(source: Probe, target: &mut Probe) {
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
fn generated_value_to_string_calls_resolve_temp_cleanup_for_string_pieces() {
    let mut session = TestSession::new();
    let module = session.compile_and_get_module(
        r#"
        struct Pair(int, int)
        to_string(Pair(1, 2))
        "#,
    );

    assert!(
        module.ir_arena.iter().any(|(_, node)| {
            let NodeKind::StaticApply(app) = &node.kind else {
                return false;
            };
            matches!(
                (
                    app.arguments.get(1),
                    app.argument_passing.get(1),
                ),
                (
                    Some(argument),
                    Some(ArgPassing::Value(ValueArgPassing::Resolved(
                        ResolvedValueArgPassing::SharedRef {
                            temp_cleanup: SharedRefTempCleanup::Drop(_),
                        },
                    ))),
                ) if matches!(module.ir_arena[*argument].kind, NodeKind::Immediate(_))
            )
        }),
        "generated calls passing string literal pieces by shared reference should resolve temp cleanup"
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
        module.ir_arena.iter().any(|(_, node)| matches!(
            node.kind,
            NodeKind::CloneValue(hir::CloneValue {
                clone: LocalClone::Resolved(ResolvedLocalClone::TrivialCopy),
                ..
            })
        )),
        "expected mutable int place materialization to lower through trivial-copy CloneValue"
    );
    assert!(
        !module.ir_arena.iter().any(|(_, node)| matches!(
            node.kind,
            NodeKind::CloneValue(hir::CloneValue {
                clone: LocalClone::Unknown,
                ..
            })
        )),
        "LocalClone::Unknown should not remain after dictionary elaboration"
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
        module.ir_arena.iter().any(|(_, node)| matches!(
            node.kind,
            NodeKind::TakeLocalValue(hir::TakeLocalValue {
                mode: TakeLocalValueMode::CloneBorrowed(ResolvedLocalClone::TrivialCopy),
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
        module.ir_arena.iter().any(|(_, node)| matches!(
            node.kind,
            NodeKind::CloneValue(hir::CloneValue {
                clone: LocalClone::Resolved(ResolvedLocalClone::TrivialCopy),
                ..
            })
        )),
        "expected projected int place materialization to resolve to trivial-copy CloneValue"
    );
    assert!(
        !module.ir_arena.iter().any(|(_, node)| matches!(
            node.kind,
            NodeKind::CloneValue(hir::CloneValue {
                clone: LocalClone::Unknown,
                ..
            })
        )),
        "LocalClone::Unknown should not remain after dictionary elaboration"
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

                fn clone(source: Probe, target: &mut Probe) {
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

                fn clone(source: Probe, target: &mut Probe) {
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

                fn clone(source: Wrapper<int>, target: &mut Wrapper<int>) {
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

                fn clone(source: a::Foreign, target: &mut a::Foreign) {
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
