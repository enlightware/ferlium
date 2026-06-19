// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use super::harness::{TestSession, expected_tuple, int, string};
use ferlium::{
    SourceId,
    ast::{PExprKind, SubscriptMemberMode},
    compiler::error::RuntimeErrorKind,
    module::id::Id,
    parse_module_and_expr,
};
use indoc::indoc;
use test_log::test;
use ustr::ustr;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parses_subscript_bundle_members() {
    let (module, _, _arena) = parse_module_and_expr(
        indoc! { r#"
            subscript pixel(texture: int, index: int) -> int {
                ref {
                    yield texture
                }

                mut {
                    yield texture
                }
            }
        "# },
        SourceId::from_index(1),
        true,
    )
    .expect("subscript module should parse");

    assert_eq!(module.subscripts.len(), 1);
    let subscript = &module.subscripts[0];
    assert_eq!(subscript.name.0, ustr("pixel"));
    assert_eq!(subscript.members.len(), 2);
    assert_eq!(subscript.members[0].mode, SubscriptMemberMode::ref_());
    assert_eq!(subscript.members[1].mode, SubscriptMemberMode::mut_());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parses_shared_subscript_bundle_member() {
    let (module, _, _arena) = parse_module_and_expr(
        indoc! { r#"
            subscript pixel(texture: int, index: int) -> int {
                ref mut {
                    yield texture
                }
            }
        "# },
        SourceId::from_index(1),
        true,
    )
    .expect("subscript module should parse");

    assert_eq!(module.subscripts.len(), 1);
    let subscript = &module.subscripts[0];
    assert_eq!(subscript.name.0, ustr("pixel"));
    assert_eq!(subscript.members.len(), 1);
    assert_eq!(subscript.members[0].mode, SubscriptMemberMode::ref_mut());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parses_unary_named_subscript_access() {
    let (_module, expr, arena) =
        parse_module_and_expr("value->[cell]", SourceId::from_index(1), true)
            .expect("named subscript expression should parse");

    let expr = single_top_level_expr(expr.expect("expected expression"), &arena);
    let PExprKind::NamedSubscript(data) = &arena[expr].kind else {
        panic!(
            "expected named subscript expression, got {:?}",
            arena[expr].kind
        );
    };
    assert_eq!(data.name.0, ustr("cell"));
    assert_eq!(data.args.len(), 0);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parses_named_subscript_access_with_arguments() {
    let (_module, expr, arena) =
        parse_module_and_expr("value->[pixel](1, 2)", SourceId::from_index(1), true)
            .expect("named subscript expression should parse");

    let expr = single_top_level_expr(expr.expect("expected expression"), &arena);
    let PExprKind::NamedSubscript(data) = &arena[expr].kind else {
        panic!(
            "expected named subscript expression, got {:?}",
            arena[expr].kind
        );
    };
    assert_eq!(data.name.0, ustr("pixel"));
    assert_eq!(data.args.len(), 2);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parses_chained_named_subscript_access() {
    let (_module, expr, arena) =
        parse_module_and_expr("value->[outer]->[inner]", SourceId::from_index(1), true)
            .expect("chained named subscript expression should parse");

    let expr = single_top_level_expr(expr.expect("expected expression"), &arena);
    let PExprKind::NamedSubscript(inner) = &arena[expr].kind else {
        panic!(
            "expected outer expression to be named subscript, got {:?}",
            arena[expr].kind
        );
    };
    assert_eq!(inner.name.0, ustr("inner"));
    let PExprKind::NamedSubscript(outer) = &arena[inner.receiver].kind else {
        panic!(
            "expected chained receiver to be named subscript, got {:?}",
            arena[inner.receiver].kind
        );
    };
    assert_eq!(outer.name.0, ustr("outer"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_has_lower_precedence_than_ordinary_suffixes() {
    let (_module, expr, arena) =
        parse_module_and_expr("value.field(1)->[cell]", SourceId::from_index(1), true)
            .expect("named subscript expression should parse");

    let expr = single_top_level_expr(expr.expect("expected expression"), &arena);
    let PExprKind::NamedSubscript(data) = &arena[expr].kind else {
        panic!(
            "expected named subscript expression, got {:?}",
            arena[expr].kind
        );
    };
    assert_eq!(data.name.0, ustr("cell"));
    assert!(matches!(arena[data.receiver].kind, PExprKind::Apply(_)));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_has_higher_precedence_than_unary_operators() {
    let (_module, expr, arena) =
        parse_module_and_expr("-value->[cell]", SourceId::from_index(1), true)
            .expect("named subscript expression should parse");

    let expr = single_top_level_expr(expr.expect("expected expression"), &arena);
    let PExprKind::Apply(data) = &arena[expr].kind else {
        panic!(
            "expected unary operator application, got {:?}",
            arena[expr].kind
        );
    };
    assert_eq!(data.args.len(), 1);
    assert!(matches!(
        arena[data.args[0]].kind,
        PExprKind::NamedSubscript(_)
    ));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_empty_named_subscript_argument_list() {
    assert!(parse_module_and_expr("value->[cell]()", SourceId::from_index(1), true).is_err());
}

fn single_top_level_expr(
    expr: ferlium::ast::PExprId,
    arena: &ferlium::ast::PExprArena,
) -> ferlium::ast::PExprId {
    match &arena[expr].kind {
        PExprKind::Block(exprs) if exprs.len() == 1 => exprs[0],
        _ => expr,
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_named_subscript_access_in_user_code_for_now() {
    let mut session = TestSession::new();
    assert!(session.try_compile("1->[cell]").is_err());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn compiles_subscript_member_yielding_a_place() {
    let mut session = TestSession::new();
    session.compile(indoc! { r#"
        subscript cell(value: int) -> int {
            ref {
                let local = value;
                yield local
            }
        }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn compiled_module_exposes_subscript_by_name() {
    let mut session = TestSession::new();
    let module = session.compile_and_get_module(indoc! { r#"
        subscript cell(value: int) -> int {
            ref {
                let local = value;
                yield local
            }
        }
    "# });

    let subscript = module
        .get_subscript(ustr("cell"))
        .expect("subscript should be available by source name");
    assert!(subscript.ref_member.is_some());
    assert!(subscript.mut_member.is_none());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_empty_subscript_bundle() {
    assert_experimental_compile_error(indoc! { r#"
        subscript cell(value: int) -> int {
        }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_duplicate_ref_subscript_members() {
    assert_experimental_compile_error(indoc! { r#"
        subscript cell(value: int) -> int {
            ref {
                let local = value;
                yield local
            }

            ref {
                let local = value;
                yield local
            }
        }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_duplicate_mut_subscript_members() {
    assert_experimental_compile_error(indoc! { r#"
        subscript cell(value: int) -> int {
            mut {
                let mut local = value;
                yield local
            }

            mut {
                let mut local = value;
                yield local
            }
        }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mut_subscript_member_requires_mutable_yielded_place() {
    let mut session = TestSession::new();
    assert!(
        session
            .try_compile(indoc! { r#"
                subscript cell(value: int) -> int {
                    mut {
                        yield value
                    }
                }
            "# })
            .is_err()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn compiles_mut_subscript_member_yielding_a_mutable_place() {
    let mut session = TestSession::new();
    session.compile(indoc! { r#"
        subscript cell(value: int) -> int {
            mut {
                let mut local = value;
                yield local
            }
        }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_ref_mut_subscript_member_combined_with_separate_members() {
    assert_experimental_compile_error(indoc! { r#"
        subscript cell(value: int) -> int {
            ref {
                let local = value;
                yield local
            }

            mut {
                let mut local = value;
                yield local
            }

            ref mut {
                let mut local = value;
                yield local
            }
        }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_yield_of_non_place() {
    let mut session = TestSession::new();
    assert!(
        session
            .try_compile(indoc! { r#"
                subscript cell(value: int) -> int {
                    ref {
                        yield 3
                    }
                }
            "# })
            .is_err()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_yield_rooted_in_parameter_storage() {
    let mut session = TestSession::new();
    assert!(
        session
            .try_compile(indoc! { r#"
                subscript cell(value: int) -> int {
                    ref {
                        yield value
                    }
                }
            "# })
            .is_err()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_yield_outside_subscript_member() {
    let mut session = TestSession::new();
    assert!(
        session
            .try_compile(indoc! { r#"
                fn bad(value: int) {
                    yield value
                }
            "# })
            .is_err()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_multiple_reachable_yields() {
    let mut session = TestSession::new();
    assert!(
        session
            .try_compile(indoc! { r#"
                subscript cell(value: int) -> int {
                    ref {
                        if true {
                            yield value
                        } else {
                            yield value
                        }
                    }
                }
            "# })
            .is_err()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_yield_inside_loop() {
    assert_experimental_compile_error(indoc! { r#"
        subscript cell(value: int) -> int {
            ref {
                let local = value;
                loop {
                    yield local
                }
            }
        }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_named_subscript_rvalue_when_ref_member_is_missing() {
    assert_experimental_compile_error(indoc! { r#"
        subscript cell(value: int) -> int {
            mut {
                let mut local = value;
                yield local
            }
        }

        let value = 1->[cell];
        value
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_named_subscript_assignment_when_mut_member_is_missing() {
    assert_experimental_compile_error(indoc! { r#"
        subscript cell(value: int) -> int {
            ref {
                let local = value;
                yield local
            }
        }

        let mut value = 1;
        value->[cell] = 2
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_named_subscript_arity_mismatch() {
    assert_experimental_compile_error(indoc! { r#"
        subscript cell(value: int, index: int) -> int {
            ref {
                let local = value;
                yield local
            }
        }

        1->[cell]
    "# });
}

fn experimental_session() -> TestSession {
    let mut session = TestSession::new();
    session.allow_experimental();
    session
}

fn assert_experimental_compile_error(src: &str) {
    assert!(experimental_session().try_compile(src).is_err());
}

fn run_experimental_subscript_source(src: &str) -> ferlium::hir::value::Value {
    let mut session = experimental_session();
    session.run(src)
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_rvalue_uses_ref_member_and_runs_epilogue() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript probe(slot: &mut int, log: &mut int) -> int {
            ref {
                log = log + 10;
                let local = slot;
                yield local;
                log = log + 100
            }

            mut {
                log = log + 1;
                let mut local = slot;
                yield local;
                slot = local;
                log = log + 1000
            }
        }

        let mut slot = 5;
        let mut log = 0;
        let value = slot->[probe](log);
        (value, slot, log)
    "# });

    assert_val_eq!(value, expected_tuple([int(5), int(5), int(110)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_assignment_uses_mut_member_and_commits() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript probe(slot: &mut int, log: &mut int) -> int {
            ref {
                log = log + 10;
                let local = slot;
                yield local;
                log = log + 100
            }

            mut {
                log = log + 1;
                let mut local = slot;
                yield local;
                slot = local;
                log = log + 1000
            }
        }

        let mut slot = 5;
        let mut log = 0;
        slot->[probe](log) = 7;
        (slot, log)
    "# });

    assert_val_eq!(value, expected_tuple([int(7), int(1001)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_compound_assignment_uses_single_mut_projection() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript probe(slot: &mut int, log: &mut int) -> int {
            ref {
                log = log + 10;
                let local = slot;
                yield local;
                log = log + 100
            }

            mut {
                log = log + 1;
                let mut local = slot;
                yield local;
                slot = local;
                log = log + 1000
            }
        }

        let mut slot = 5;
        let mut log = 0;
        slot->[probe](log) += 2;
        (slot, log)
    "# });

    assert_val_eq!(value, expected_tuple([int(7), int(1001)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn nested_named_subscript_assignment_unwinds_lifo() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript outer(slot: &mut int, log: &mut int) -> int {
            mut {
                log = log * 10 + 1;
                let mut local = slot;
                yield local;
                slot = local;
                log = log * 10 + 2
            }
        }

        subscript inner(slot: &mut int, log: &mut int) -> int {
            mut {
                log = log * 10 + 3;
                let mut local = slot;
                yield local;
                slot = local;
                log = log * 10 + 4
            }
        }

        let mut slot = 5;
        let mut log = 0;
        slot->[outer](log)->[inner](log) = 7;
        (slot, log)
    "# });

    assert_val_eq!(value, expected_tuple([int(7), int(1342)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn nested_named_subscript_compound_assignment_uses_single_projection_per_level() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript outer(slot: &mut int, log: &mut int) -> int {
            mut {
                log = log * 10 + 1;
                let mut local = slot;
                yield local;
                slot = local;
                log = log * 10 + 2
            }
        }

        subscript inner(slot: &mut int, log: &mut int) -> int {
            mut {
                log = log * 10 + 3;
                let mut local = slot;
                yield local;
                slot = local;
                log = log * 10 + 4
            }
        }

        let mut slot = 5;
        let mut log = 0;
        slot->[outer](log)->[inner](log) += 2;
        (slot, log)
    "# });

    assert_val_eq!(value, expected_tuple([int(7), int(1342)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_rvalue_uses_ref_member_effects() {
    experimental_session().compile(indoc! { r#"
        subscript probe(slot: &mut int) -> int {
            ref {
                effects::read();
                let local = slot;
                yield local
            }

            mut {
                effects::write();
                let mut local = slot;
                yield local;
                slot = local
            }
        }

        effects::take_read(|| {
            let mut slot = 5;
            let value = slot->[probe];
            ()
        })
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_assignment_uses_mut_member_effects() {
    assert_experimental_compile_error(indoc! { r#"
        subscript probe(slot: &mut int) -> int {
            ref {
                effects::read();
                let local = slot;
                yield local
            }

            mut {
                effects::write();
                let mut local = slot;
                yield local;
                slot = local
            }
        }

        effects::take_read(|| {
            let mut slot = 5;
            slot->[probe] = 7
        })
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn shared_ref_mut_subscript_member_serves_reads_and_writes() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell(slot: &mut int, log: &mut int) -> int {
            ref mut {
                log = log + 1;
                let mut local = slot;
                yield local;
                slot = local;
                log = log + 10
            }
        }

        let mut slot = 5;
        let mut log = 0;
        let read = slot->[cell](log);
        slot->[cell](log) = 7;
        (read, slot, log)
    "# });

    assert_val_eq!(value, expected_tuple([int(5), int(7), int(22)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parameterized_named_subscript_instantiates_at_use_sites() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell<T>(slot: &mut T) -> T
        where
            T: Value
        {
            ref {
                let local = slot;
                yield local
            }

            mut {
                let mut local = slot;
                yield local;
                slot = local
            }
        }

        let mut number = 5;
        let mut text = "old";
        let before = number->[cell];
        text->[cell] = "new";
        (before, text)
    "# });

    assert_val_eq!(value, expected_tuple([int(5), string("new")]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_body_error_runs_epilogue_before_propagating() {
    let mut session = experimental_session();
    let source = indoc! { r#"
        subscript cell(slot: &mut int) -> int {
            mut {
                let mut local = slot;
                yield local;
                slot = local;
                testing::record_tracked_drop(7)
            }
        }

        testing::reset_tracked_drops();
        let mut slot = 5;
        slot->[cell] = [0][1]
    "# };

    assert_eq!(
        session.fail_run(source),
        RuntimeErrorKind::Aborted(Some(
            "Array access out of bounds: index 1 for length 1".to_string()
        ))
    );
    assert_val_eq!(session.run("testing::tracked_drop_log()"), int(7));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_prologue_error_skips_epilogue() {
    let mut session = experimental_session();
    let source = indoc! { r#"
        subscript cell(slot: &mut int) -> int {
            mut {
                testing::record_tracked_drop(1);
                let ignored = [0][1];
                let mut local = slot;
                yield local;
                slot = local;
                testing::record_tracked_drop(9)
            }
        }

        testing::reset_tracked_drops();
        let mut slot = 5;
        slot->[cell] = 7
    "# };

    assert_eq!(
        session.fail_run(source),
        RuntimeErrorKind::Aborted(Some(
            "Array access out of bounds: index 1 for length 1".to_string()
        ))
    );
    assert_val_eq!(session.run("testing::tracked_drop_log()"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn subscript_yield_inside_nested_block_keeps_outer_epilogue() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript probe(slot: &mut int, log: &mut int) -> int {
            ref {
                log = log + 1;
                {
                    let local = slot;
                    yield local
                };
                log = log + 10
            }
        }

        let mut slot = 5;
        let mut log = 0;
        let value = slot->[probe](log);
        (value, log)
    "# });

    assert_val_eq!(value, expected_tuple([int(5), int(11)]));
}
