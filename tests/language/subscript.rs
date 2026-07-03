// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use super::harness::{TestSession, expected_array_infer, expected_tuple, int, string};
use ferlium::{
    SourceId,
    ast::{PExprKind, SubscriptMemberMode},
    compiler::error::{
        CompilationErrorImpl, InvalidRecordFieldContext, InvalidSubscriptDefinitionKind,
        InvalidYieldKind, MutabilityMustBeWhat, RuntimeErrorKind, SubscriptDefinitionSubject,
        UnsupportedSubscriptFeatureKind,
    },
    hir::{ENodeArena, ENodeId, NodeKind},
    module::{YieldProvenance, id::Id},
    parse_module_and_expr,
    std::math::int_type,
    types::effects::{PrimitiveEffect, effect},
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
fn parses_projection_subscript_definition() {
    let (module, _, _arena) = parse_module_and_expr(
        indoc! { r#"
            subscript Vec2.x(self) -> int {
                ref mut {
                    self.x
                }
            }
        "# },
        SourceId::from_index(1),
        true,
    )
    .expect("projection subscript module should parse");

    assert_eq!(module.subscripts.len(), 1);
    let subscript = &module.subscripts[0];
    assert_eq!(subscript.name.0, ustr("x"));
    assert!(subscript.projection_receiver.is_some());
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
fn named_subscript_allows_following_ordinary_suffixes() {
    let (_module, expr, arena) =
        parse_module_and_expr("value->[row](0)[1]", SourceId::from_index(1), true)
            .expect("named subscript followed by index should parse");

    let expr = single_top_level_expr(expr.expect("expected expression"), &arena);
    let PExprKind::Index(index) = &arena[expr].kind else {
        panic!("expected index expression, got {:?}", arena[expr].kind);
    };
    let PExprKind::NamedSubscript(data) = &arena[index.array].kind else {
        panic!(
            "expected indexed receiver to be named subscript, got {:?}",
            arena[index.array].kind
        );
    };
    assert_eq!(data.name.0, ustr("row"));
    assert_eq!(data.args.len(), 1);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_result_call_requires_parentheses() {
    let (_module, expr, arena) =
        parse_module_and_expr("(value->[cell])(1)", SourceId::from_index(1), true)
            .expect("parenthesized named subscript result call should parse");

    let expr = single_top_level_expr(expr.expect("expected expression"), &arena);
    let PExprKind::Apply(data) = &arena[expr].kind else {
        panic!(
            "expected application expression, got {:?}",
            arena[expr].kind
        );
    };
    assert_eq!(data.args.len(), 1);
    assert!(matches!(
        arena[data.func].kind,
        PExprKind::NamedSubscript(_)
    ));
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
    let signature = subscript.expect_resolved_signature();
    assert_eq!(signature.arg_names, vec![ustr("value")]);
    assert_eq!(signature.args.len(), 1);
    assert_eq!(signature.args[0].ty, int_type());
    assert_eq!(signature.ret, int_type());
    assert!(subscript.ref_member.is_some());
    assert!(subscript.mut_member.is_none());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn subscript_member_without_yield_is_addressor_place() {
    let mut session = experimental_session();
    let module = session.compile_and_get_module(indoc! { r#"
        subscript first(values: &mut [int]) -> int {
            ref mut {
                values[0]
            }
        }
    "# });

    let subscript = module
        .get_subscript(ustr("first"))
        .expect("subscript should be available by source name");
    let ref_member = subscript.ref_member.as_ref().unwrap();
    let mut_member = subscript.mut_member.as_ref().unwrap();
    assert_eq!(ref_member.function, mut_member.function);
    assert_eq!(ref_member.provenance, YieldProvenance::AddressorPlace);
    assert_eq!(mut_member.provenance, YieldProvenance::AddressorPlace);
    let function = module
        .get_function_by_id(ref_member.function)
        .expect("subscript member function should exist");
    assert!(function.definition.returns_place());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn addressor_subscript_rejects_direct_by_value_parameter_root() {
    assert_experimental_compile_error(indoc! { r#"
        subscript cell(value: int) -> int {
            ref {
                value
            }
        }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn addressor_subscript_rejects_owned_local_return_root() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            subscript cell(value: int) -> int {
                ref {
                    let local = value;
                    local
                }
            }
        "# },
        SubscriptDefinitionSubject::SubscriptMember(ustr("cell")),
        InvalidSubscriptDefinitionKind::AddressorReturnMustBeRootedInBaseParameter,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn addressor_subscript_rejects_addressor_rooted_in_owned_local() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            subscript first(values: &mut [int]) -> int {
                ref {
                    let local = values;
                    local[0]
                }
            }
        "# },
        SubscriptDefinitionSubject::SubscriptMember(ustr("first")),
        InvalidSubscriptDefinitionKind::AddressorReturnMustBeRootedInBaseParameter,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn addressor_subscript_rejects_addressor_rooted_in_non_base_parameter() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            subscript first(first_values: &mut [int], values: &mut [int]) -> int {
                ref {
                    values[0]
                }
            }
        "# },
        SubscriptDefinitionSubject::SubscriptMember(ustr("first")),
        InvalidSubscriptDefinitionKind::AddressorReturnMustBeRootedInBaseParameter,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn addressor_subscript_rejects_generic_parameter_return_root() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            subscript cell<A>(value: A) -> A {
                ref {
                    value
                }
            }
        "# },
        SubscriptDefinitionSubject::SubscriptMember(ustr("cell")),
        InvalidSubscriptDefinitionKind::AddressorReturnMustBeRootedInBaseParameter,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn addressor_subscript_accepts_implicit_tail_place() {
    let value = experimental_session().run(indoc! { r#"
        subscript first(values: &mut [int]) -> int {
            ref mut {
                values[0]
            }
        }

        let mut values = [1, 2];
        values->[first] = 42;
        values[0]
    "# });

    assert_val_eq!(value, int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn addressor_subscript_accepts_explicit_return_place() {
    let value = experimental_session().run(indoc! { r#"
        subscript first(values: &mut [int]) -> int {
            ref mut {
                return values[0]
            }
        }

        let mut values = [1, 2];
        values->[first] = 42;
        values[0]
    "# });

    assert_val_eq!(value, int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn addressor_subscript_rejects_implicit_tail_value() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            subscript cell() -> int {
                ref {
                    1
                }
            }
        "# },
        SubscriptDefinitionSubject::SubscriptMember(ustr("cell")),
        InvalidSubscriptDefinitionKind::AddressorReturnMustBePlace,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn addressor_subscript_rejects_empty_member_body() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            subscript cell() -> () {
                ref {
                }
            }
        "# },
        SubscriptDefinitionSubject::SubscriptMember(ustr("cell")),
        InvalidSubscriptDefinitionKind::AddressorReturnMustBePlace,
    );
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
fn rejects_yield_inside_user_closure() {
    let mut session = TestSession::new();
    match session
        .fail_compilation(indoc! { r#"
            let f = || { yield 1 };
            ()
        "# })
        .into_inner()
    {
        CompilationErrorImpl::InvalidYield { kind, .. } => {
            assert_eq!(kind, InvalidYieldKind::OutsideSubscriptMember);
        }
        other => panic!("expected invalid yield error, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_yield_inside_closure_nested_in_subscript_member() {
    assert_invalid_yield(
        indoc! { r#"
            subscript cell(value: int) -> int {
                ref {
                    let f = || { yield value };
                    value
                }
            }
        "# },
        InvalidYieldKind::OutsideSubscriptMember,
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
fn rejects_single_yield_nested_in_if() {
    assert_experimental_compile_error(indoc! { r#"
        subscript cell(value: int) -> int {
            ref {
                let local = value;
                if true {
                    yield local
                }
            }
        }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_single_yield_nested_in_match() {
    assert_experimental_compile_error(indoc! { r#"
        subscript cell(value: int) -> int {
            ref {
                let local = value;
                match true {
                    true => yield local,
                    _ => ()
                }
            }
        }
    "# });
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

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn explicit_private_repr_projection_reads_and_writes() {
    let value = run_experimental_subscript_source(indoc! { r#"
        #[private_repr]
        struct Secret {
            items: [int],
        }

        subscript Secret.value(self) -> int {
            ref mut {
                self.items[0]
            }
        }

        let mut secret = Secret { items: [4] };
        let before = secret.value;
        secret.value = 9;
        before + secret.value
    "# });

    assert_val_eq!(value, int(13));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn explicit_projection_can_share_field_name_across_receiver_types() {
    let value = run_experimental_subscript_source(indoc! { r#"
        #[private_repr]
        struct A {
            value: int,
        }

        #[private_repr]
        struct B {
            value: int,
        }

        subscript A.x(self) -> int {
            ref mut {
                self.value
            }
        }

        subscript B.x(self) -> int {
            ref mut {
                self.value
            }
        }

        let a = A { value: 2 };
        let b = B { value: 5 };
        a.x + b.x
    "# });

    assert_val_eq!(value, int(7));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_and_projection_can_share_source_name() {
    let value = run_experimental_subscript_source(indoc! { r#"
        #[private_repr]
        struct Secret {
            value: int,
        }

        subscript value(slot: &mut int) -> int {
            ref mut {
                slot
            }
        }

        subscript Secret.value(self) -> int {
            ref mut {
                self.value
            }
        }

        let mut slot = 3;
        let secret = Secret { value: 8 };
        slot->[value] + secret.value
    "# });

    assert_val_eq!(value, int(11));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn explicit_projection_can_be_passed_as_mutable_place() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn bump(slot: &mut int) {
            slot = slot + 1
        }

        #[private_repr]
        struct Secret {
            items: [int],
        }

        subscript Secret.value(self) -> int {
            ref mut {
                self.items[0]
            }
        }

        let mut secret = Secret { items: [4] };
        bump(secret.value);
        secret.value
    "# });

    assert_val_eq!(value, int(5));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_projection_receiver_reads_and_writes() {
    let value = run_experimental_subscript_source(indoc! { r#"
        #[private_repr]
        struct Pair<A, B> {
            left: A,
            right: B,
        }

        subscript Pair<A, B>.left(self) -> A {
            ref mut {
                self.left
            }
        }

        let mut pair = Pair { left: 2, right: "ignored" };
        pair.left = 9;
        pair.left
    "# });

    assert_val_eq!(value, int(9));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_projection_receiver_resolves_after_concrete_return_annotation() {
    let value = run_experimental_subscript_source(indoc! { r#"
        #[private_repr]
        struct Pair<A, B> {
            left: A,
            right: B,
        }

        subscript Pair<A, B>.fake(self) -> int {
            ref {
                let mut local = 99;
                yield local
            }
        }

        fn make() -> Pair<int, string> {
            Pair { left: 1, right: "ignored" }
        }

        let pair = make();
        pair.fake
    "# });

    assert_val_eq!(value, int(99));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_projection_receiver_substitutes_result_type() {
    let value = run_experimental_subscript_source(indoc! { r#"
        #[private_repr]
        struct Pair<A, B> {
            left: A,
            right: B,
        }

        subscript Pair<A, B>.left_value(self) -> A {
            ref mut {
                self.left
            }
        }

        fn make() -> Pair<int, string> {
            Pair { left: 41, right: "ignored" }
        }

        let mut pair = make();
        pair.left_value + 1
    "# });

    assert_val_eq!(value, int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn yielded_projection_assignment_runs_prologue_and_epilogue() {
    let value = run_experimental_subscript_source(indoc! { r#"
        #[private_repr]
        struct Secret {
            items: [int],
        }

        subscript Secret.value(self) -> int {
            mut {
                let mut local = self.items[0];
                self.items[1] = self.items[1] + 1;
                yield local;
                self.items[0] = local;
                self.items[1] = self.items[1] + 10
            }
        }

        let mut secret = Secret { items: [2, 0] };
        secret.value = 7;
        secret.items[0] * 100 + secret.items[1]
    "# });

    assert_val_eq!(value, int(711));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn yielded_projection_mutable_argument_wraps_call_in_driver() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn bump(slot: &mut int) {
            slot = slot + 1
        }

        #[private_repr]
        struct Secret {
            items: [int],
        }

        subscript Secret.value(self) -> int {
            mut {
                let mut local = self.items[0];
                self.items[1] = self.items[1] + 1;
                yield local;
                self.items[0] = local;
                self.items[1] = self.items[1] + 10
            }
        }

        let mut secret = Secret { items: [4, 0] };
        bump(secret.value);
        secret.items[0] * 100 + secret.items[1]
    "# });

    assert_val_eq!(value, int(511));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn yielded_projection_mutable_argument_with_inferred_callee_mutability_commits() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn bump(slot) {
            slot = slot + 1
        }

        fn bump_value<T>(value: &mut T) {
            bump(value.value)
        }

        #[private_repr]
        struct Secret {
            items: [int],
        }

        subscript Secret.value(self) -> int {
            mut {
                let mut local = self.items[0];
                self.items[1] = self.items[1] + 1;
                yield local;
                self.items[0] = local;
                self.items[1] = self.items[1] + 10
            }
        }

        let mut secret = Secret { items: [4, 0] };
        bump_value(secret);
        secret.items[0] * 100 + secret.items[1]
    "# });

    assert_val_eq!(value, int(511));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn module_function_can_use_later_projection_subscript() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn read_secret(secret: &mut Secret) -> int {
            secret.value
        }

        #[private_repr]
        struct Secret {
            raw: int,
        }

        subscript Secret.value(self) -> int {
            ref {
                self.raw
            }
        }

        let mut secret = Secret { raw: 12 };
        read_secret(secret)
    "# });

    assert_val_eq!(value, int(12));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn projection_subscript_self_access_inside_lambda_is_rejected() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            #[private_repr]
            struct Secret {
                raw: int,
            }

            subscript Secret.value(self) -> int {
                ref {
                    let read = || self.value;
                    read()
                }
            }
        "# },
        SubscriptDefinitionSubject::SubscriptMember(ustr("value")),
        InvalidSubscriptDefinitionKind::AddressorReturnMustBePlace,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ref_only_addressor_projection_can_return_direct_field_place() {
    let value = run_experimental_subscript_source(indoc! { r#"
        #[private_repr]
        struct Secret {
            raw: int,
        }

        subscript Secret.value(self) -> int {
            ref {
                self.raw
            }
        }

        let secret = Secret { raw: 5 };
        secret.value
    "# });

    assert_val_eq!(value, int(5));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_repr_missing_projection_field_reports_field_error() {
    assert_invalid_record_field(
        indoc! { r#"
            #[private_repr]
            struct Secret {
                raw: int,
            }

            fn read(secret: Secret) -> int {
                secret.missing
            }
        "# },
        InvalidRecordFieldContext::StructuralField,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn projection_fallback_on_missing_record_field_reports_projection_context() {
    assert_invalid_record_field(
        indoc! { r#"
            #[private_repr]
            struct Secret {
                raw: int,
            }

            fn read(value) -> int {
                value.missing
            }

            read(Secret { raw: 1 })
        "# },
        InvalidRecordFieldContext::ProjectionFallback,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn projection_fallback_on_tuple_newtype_reports_projection_context() {
    assert_invalid_record_field(
        indoc! { r#"
            #[private_repr]
            struct Secret(int)

            fn read(value) -> int {
                value.missing
            }

            read(Secret(1))
        "# },
        InvalidRecordFieldContext::ProjectionFallback,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn projection_subscript_rejects_effect_parameterized_receiver_for_now() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            #[private_repr]
            struct EffectBox<! E> {
                run: () -> () ! E,
            }

            subscript EffectBox.value(self) -> int {
                ref {
                    1
                }
            }
        "# },
        SubscriptDefinitionSubject::Subscript(ustr("value")),
        InvalidSubscriptDefinitionKind::ProjectionReceiverGenericParametersMismatch,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn explicit_projection_read_does_not_require_mutable_receiver() {
    let value = run_experimental_subscript_source(indoc! { r#"
        #[private_repr]
        struct Secret {
            items: [int],
        }

        subscript Secret.value(self) -> int {
            ref mut {
                self.items[0]
            }
        }

        let secret = Secret { items: [4] };
        secret.value
    "# });

    assert_val_eq!(value, int(4));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn explicit_projection_write_requires_mutable_receiver() {
    let mut session = experimental_session();
    session
        .fail_compilation(indoc! { r#"
            #[private_repr]
            struct Secret {
                items: [int],
            }

            subscript Secret.value(self) -> int {
                ref mut {
                    self.items[0]
                }
            }

            let secret = Secret { items: [4] };
            secret.value = 9
        "# })
        .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_projection_uses_explicit_private_repr_projection_evidence() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn read_value<T>(value: &mut T) -> int {
            value.value
        }

        #[private_repr]
        struct Secret {
            items: [int],
        }

        subscript Secret.value(self) -> int {
            ref mut {
                self.items[0]
            }
        }

        let mut secret = Secret { items: [7] };
        read_value(secret)
    "# });

    assert_val_eq!(value, int(7));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_projection_read_uses_ref_member_effects_from_evidence() {
    experimental_session().compile(indoc! { r#"
        fn read_value<T>(value: &mut T) -> int {
            value.value
        }

        #[private_repr]
        struct Secret {
            raw: int,
        }

        subscript Secret.value(self) -> int {
            ref {
                effects::read();
                let local = self.raw;
                yield local
            }

            mut {
                effects::write();
                let mut local = self.raw;
                yield local;
                self.raw = local
            }
        }

        effects::take_read(|| {
            let mut secret = Secret { raw: 7 };
            read_value(secret);
            ()
        })
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_projection_write_uses_mut_member_effects_from_evidence() {
    experimental_session()
        .fail_compilation(indoc! { r#"
            fn set_value<T>(value: &mut T, new_value: int) {
                value.value = new_value
            }

            #[private_repr]
            struct Secret {
                raw: int,
            }

            subscript Secret.value(self) -> int {
                ref {
                    effects::read();
                    let local = self.raw;
                    yield local
                }

                mut {
                    effects::write();
                    let mut local = self.raw;
                    yield local;
                    self.raw = local
                }
            }

            effects::take_read(|| {
                let mut secret = Secret { raw: 7 };
                set_value(secret, 9);
                ()
            })
        "# })
        .expect_invalid_effect_dependency(
            effect(PrimitiveEffect::Write),
            effect(PrimitiveEffect::Read),
        );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_projection_read_accepts_ref_only_projection_evidence() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn read_value<T>(value: &mut T) -> int {
            value.value
        }

        #[private_repr]
        struct Secret {
            items: [int],
        }

        subscript Secret.value(self) -> int {
            ref {
                self.items[0]
            }
        }

        let mut secret = Secret { items: [7] };
        read_value(secret)
    "# });

    assert_val_eq!(value, int(7));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_projection_read_runs_yielded_ref_driver() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn read_value<T>(value: &mut T) -> int {
            value.value
        }

        #[private_repr]
        struct Secret {
            items: [int],
        }

        subscript Secret.value(self) -> int {
            ref {
                let mut local = self.items[0] + 1;
                yield local;
            }
        }

        let mut secret = Secret { items: [7, 0] };
        read_value(secret)
    "# });

    assert_val_eq!(value, int(8));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_projection_write_runs_yielded_mut_driver() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn set_value<T>(value: &mut T, new_value: int) {
            value.value = new_value
        }

        #[private_repr]
        struct Secret {
            items: [int],
        }

        subscript Secret.value(self) -> int {
            mut {
                let mut local = self.items[0];
                self.items[1] = self.items[1] + 1;
                yield local;
                self.items[0] = local;
                self.items[1] = self.items[1] + 10
            }
        }

        let mut secret = Secret { items: [3, 0] };
        set_value(secret, 8);
        secret.items[0] * 100 + secret.items[1]
    "# });

    assert_val_eq!(value, int(811));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_projection_mutable_arg_runs_yielded_mut_driver() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn bump(slot: &mut int) {
            slot = slot + 1
        }

        fn bump_value<T>(value: &mut T) {
            bump(value.value)
        }

        #[private_repr]
        struct Secret {
            items: [int],
        }

        subscript Secret.value(self) -> int {
            mut {
                let mut local = self.items[0];
                self.items[1] = self.items[1] + 1;
                yield local;
                self.items[0] = local;
                self.items[1] = self.items[1] + 10
            }
        }

        let mut secret = Secret { items: [4, 0] };
        bump_value(secret);
        secret.items[0] * 100 + secret.items[1]
    "# });

    assert_val_eq!(value, int(511));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn projection_subscript_rejects_accessible_structural_field_conflict() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            struct Point {
                x: int,
            }

            subscript Point.x(self) -> int {
                ref mut {
                    self.x
                }
            }
        "# },
        SubscriptDefinitionSubject::Subscript(ustr("x")),
        InvalidSubscriptDefinitionKind::ProjectionConflictsWithStructuralField,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn projection_subscript_rejects_duplicate_receiver_field() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            #[private_repr]
            struct Secret {
                value: int,
            }

            subscript Secret.value(self) -> int {
                ref mut {
                    self.value
                }
            }

            subscript Secret.value(self) -> int {
                ref mut {
                    self.value
                }
            }
        "# },
        SubscriptDefinitionSubject::Subscript(ustr("value")),
        InvalidSubscriptDefinitionKind::DuplicateProjection,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn projection_subscript_rejects_receiver_generic_order_mismatch() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            #[private_repr]
            struct Pair<A, B> {
                left: A,
                right: B,
            }

            subscript Pair<B, A>.left(self) -> B {
                ref mut {
                    self.left
                }
            }
        "# },
        SubscriptDefinitionSubject::Subscript(ustr("left")),
        InvalidSubscriptDefinitionKind::ProjectionReceiverGenericParametersMismatch,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn projection_subscript_rejects_receiver_generic_arity_mismatch() {
    assert_experimental_compile_error(indoc! { r#"
            #[private_repr]
            struct Pair<A, B> {
                left: A,
                right: B,
            }

            subscript Pair<A>.left(self) -> A {
                ref mut {
                    self.left
                }
            }
        "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn projection_subscript_receiver_parameter_must_be_untyped() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            #[private_repr]
            struct Secret {
                value: int,
            }

            subscript Secret.value(self: int) -> int {
                ref mut {
                    self.value
                }
            }
        "# },
        SubscriptDefinitionSubject::Subscript(ustr("value")),
        InvalidSubscriptDefinitionKind::ProjectionReceiverParameterMustBeUntyped,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn projection_subscript_requires_receiver_parameter() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            #[private_repr]
            struct Secret {
                value: int,
            }

            subscript Secret.value() -> int {
                ref mut {
                    1
                }
            }
        "# },
        SubscriptDefinitionSubject::Subscript(ustr("value")),
        InvalidSubscriptDefinitionKind::ProjectionMissingReceiverParameter,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn projection_subscript_rejects_extra_parameters() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            #[private_repr]
            struct Secret {
                value: int,
            }

            subscript Secret.value(self, other) -> int {
                ref mut {
                    self.value
                }
            }
        "# },
        SubscriptDefinitionSubject::Subscript(ustr("value")),
        InvalidSubscriptDefinitionKind::ProjectionUnexpectedParameter,
    );
}

fn experimental_session() -> TestSession {
    let mut session = TestSession::new();
    session.allow_experimental();
    session
}

fn assert_experimental_compile_error(src: &str) {
    assert!(experimental_session().try_compile(src).is_err());
}

fn assert_invalid_record_field(src: &str, expected_ctx: InvalidRecordFieldContext) {
    match experimental_session().fail_compilation(src).into_inner() {
        CompilationErrorImpl::InvalidRecordField { ctx, .. } if ctx == expected_ctx => {}
        other => panic!("expected invalid record field error, got {other:?}"),
    }
}

fn assert_invalid_subscript_definition(
    src: &str,
    expected_subject: SubscriptDefinitionSubject,
    expected_kind: InvalidSubscriptDefinitionKind,
) {
    match experimental_session().fail_compilation(src).into_inner() {
        CompilationErrorImpl::InvalidSubscriptDefinition { subject, kind, .. } => {
            assert_eq!(subject, expected_subject);
            assert_eq!(kind, expected_kind);
        }
        other => panic!("expected invalid subscript definition error, got {other:?}"),
    }
}

fn assert_invalid_yield(src: &str, expected_kind: InvalidYieldKind) {
    match experimental_session().fail_compilation(src).into_inner() {
        CompilationErrorImpl::InvalidYield { kind, .. } => {
            assert_eq!(kind, expected_kind);
        }
        other => panic!("expected invalid yield error, got {other:?}"),
    }
}

fn assert_unsupported_subscript_feature(src: &str, expected_kind: UnsupportedSubscriptFeatureKind) {
    match experimental_session().fail_compilation(src).into_inner() {
        CompilationErrorImpl::UnsupportedSubscriptFeature { kind, .. } => {
            assert_eq!(kind, expected_kind);
        }
        other => panic!("expected unsupported subscript feature error, got {other:?}"),
    }
}

fn run_experimental_subscript_source(src: &str) -> ferlium::hir::value::Value {
    let mut session = experimental_session();
    session.run(src)
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn infers_addressor_subscript_argument_and_return_types() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell(slot) {
            ref mut {
                slot
            }
        }

        let mut slot = 41;
        slot->[cell] += 1;
        slot
    "# });

    assert_val_eq!(value, int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn infers_projection_subscript_return_type() {
    let value = run_experimental_subscript_source(indoc! { r#"
        #[private_repr]
        struct Secret {
            value: int,
        }

        subscript Secret.value(self) {
            ref mut {
                self.value
            }
        }

        let mut secret = Secret { value: 41 };
        secret.value += 1;
        secret.value
    "# });

    assert_val_eq!(value, int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn infers_yielded_subscript_argument_and_return_types() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell(value, log) {
            ref {
                let local = value + 0;
                yield local
            }
            mut {
                log = log + 1;
                let mut local = value + 0;
                yield local;
                log = log + 10
            }
        }

        let mut log = 0;
        let result = 40->[cell](log);
        (result, log)
    "# });

    assert_val_eq!(value, expected_tuple([int(40), int(0)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn subscript_signature_accepts_placeholder_annotations() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell(slot: &mut _) -> _ {
            ref mut {
                slot
            }
        }

        let mut slot = 41;
        slot->[cell] += 1;
        slot
    "# });

    assert_val_eq!(value, int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn subscript_signature_can_mix_inferred_concrete_and_placeholder_annotations() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell(slot, offsets: [_], scale: int) {
            ref {
                let local = slot + offsets[0] * scale;
                yield local
            }
            mut {
                let mut local = slot + offsets[0] * scale;
                yield local;
                slot = local
            }
        }

        let mut slot = 10;
        let read = slot->[cell]([2], 3);
        slot->[cell]([2], 3) = 20;
        (read, slot)
    "# });

    assert_val_eq!(value, expected_tuple([int(16), int(20)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mut_only_subscript_can_infer_shared_signature() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell(slot) {
            mut {
                slot
            }
        }

        let mut slot = 0;
        slot->[cell] = 42;
        slot
    "# });

    assert_val_eq!(value, int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn separate_members_share_inferred_generic_subscript_signature() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell<T>(slot: &mut T)
        where
            T: Value
        {
            ref {
                slot
            }
            mut {
                slot
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
fn omitted_generic_subscript_return_is_independent_of_first_type_param() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript wrap<T>(slot: T)
        where
            T: Value
        {
            ref {
                let local = [slot];
                yield local
            }
        }

        5->[wrap]
    "# });

    assert_val_eq!(value, expected_array_infer([int(5)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn placeholder_generic_subscript_return_is_independent_of_first_type_param() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript wrap<T>(slot: T) -> _
        where
            T: Value
        {
            ref {
                let local = [slot];
                yield local
            }
        }

        5->[wrap]
    "# });

    assert_val_eq!(value, expected_array_infer([int(5)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn explicit_generic_subscript_return_annotation_is_enforced() {
    // `-> T` names the first generic parameter and must be enforced, not mistaken
    // for an inferred placeholder: the body yields `[T]`, which conflicts with the
    // annotated element return type `T`.
    assert_experimental_compile_error(indoc! { r#"
        subscript wrap<T>(slot: T) -> T
        where
            T: Value
        {
            ref {
                let local = [slot];
                yield local
            }
        }

        5->[wrap]
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ref_and_mut_subscript_members_must_infer_same_return_type() {
    assert_experimental_compile_error(indoc! { r#"
        subscript bad(int_slot, bool_slot) {
            ref {
                int_slot
            }
            mut {
                bool_slot
            }
        }

        let mut int_slot = 1;
        let mut bool_slot = true;
        int_slot->[bad](bool_slot)
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn module_function_can_use_later_named_subscript() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn read(slot: &mut int) -> int {
            slot->[cell]
        }

        subscript cell(slot: &mut int) -> int {
            ref {
                let local = slot;
                yield local
            }
        }

        let mut slot = 8;
        read(slot)
    "# });

    assert_val_eq!(value, int(8));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_addressor_subscript_value_reads_and_writes() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript first(values: &mut [int]) -> int {
            ref mut {
                values[0]
            }
        }

        let first_slot = first;
        let mut values = [8];
        let before = values->[first_slot];
        values->[first_slot] = 13;
        before + values[0]
    "# });

    assert_val_eq!(value, int(21));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_yielded_subscript_value_runs_epilogue() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell(slot: &mut int, log: &mut int) -> int {
            mut {
                log = log + 1;
                let mut local = slot;
                yield local;
                slot = local;
                log = log * 10
            }
        }

        let cell_slot = cell;
        let mut slot = 5;
        let mut log = 0;
        slot->[cell_slot](log) += 7;
        slot + log
    "# });

    assert_val_eq!(value, int(22));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_addressor_subscript_parameter_is_inferred_and_adapted_to_yielded_interface() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript first(values: &mut [int]) -> int {
            ref mut {
                values[0]
            }
        }

        fn read(slot) -> int {
            let mut values = [9];
            values->[slot]
        }

        let first_slot = first;
        read(first_slot)
    "# });

    assert_val_eq!(value, int(9));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_yielded_subscript_parameter_is_inferred_and_runs_epilogue() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell(slot: &mut int) -> int {
            mut {
                let mut local = slot;
                yield local;
                slot = local
            }
        }

        fn bump(accessor) -> int {
            let mut slot = 5;
            slot->[accessor] += 7;
            slot
        }

        let accessor = cell;
        bump(accessor)
    "# });

    assert_val_eq!(value, int(12));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_addressor_subscript_parameter_assignment_is_inferred() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript first(values: &mut [int]) -> int {
            ref mut {
                values[0]
            }
        }

        fn set_first(slot) -> int {
            let mut values = [5];
            values->[slot] = 8;
            values[0]
        }

        let first_slot = first;
        set_first(first_slot)
    "# });

    assert_val_eq!(value, int(8));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_subscript_parameters_can_be_chosen_before_mutation() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript first(values: &mut [int]) -> int {
            ref mut {
                values[0]
            }
        }

        subscript second(values: &mut [int]) -> int {
            ref mut {
                values[1]
            }
        }

        fn bump_chosen(values: &mut [int], left, right, use_left) {
            if use_left {
                values->[left] += 1
            } else {
                values->[right] += 1
            }
        }

        let mut values = [5, 12];
        bump_chosen(values, first, second, false);
        values
    "# });

    assert_val_eq!(value, expected_array_infer([int(5), int(13)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_yielded_subscript_parameter_assignment_is_inferred() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell(slot: &mut int, log: &mut int) -> int {
            mut {
                log = log + 1;
                let mut local = slot;
                yield local;
                slot = local;
                log = log * 10
            }
        }

        fn set_cell(accessor, log: &mut int) -> int {
            let mut slot = 5;
            slot->[accessor](log) = 8;
            slot + log
        }

        let accessor = cell;
        let mut log = 0;
        set_cell(accessor, log)
    "# });

    assert_val_eq!(value, int(18));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_yielded_subscript_parameter_extra_mut_arg_is_inferred() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell(slot: &mut int, log: &mut int) -> int {
            mut {
                log = log + 1;
                let mut local = slot;
                yield local;
                slot = local;
                log = log * 10
            }
        }

        fn bump(accessor, log: &mut int) -> int {
            let mut slot = 5;
            slot->[accessor](log) += 7;
            slot + log
        }

        let accessor = cell;
        let mut log = 0;
        bump(accessor, log)
    "# });

    assert_val_eq!(value, int(22));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_non_receiver_closure_arg_uses_expected_type() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell(slot: &mut int, callback: (int) -> int) -> int {
            ref {
                let local = callback(slot);
                yield local
            }
        }

        let mut slot = 5;
        slot->[cell](|x| x + 1)
    "# });

    assert_val_eq!(value, int(6));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_subscript_value_is_not_a_function() {
    assert_experimental_compile_error(indoc! { r#"
        subscript cell(slot: &mut int) -> int {
            ref mut {
                slot
            }
        }

        let cell_slot = cell;
        let mut slot = 5;
        cell_slot(slot)
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_subscript_parameter_requires_selected_member() {
    assert_experimental_compile_error(indoc! { r#"
        subscript first(values: &mut [int]) -> int {
            ref {
                values[0]
            }
        }

        fn take(slot: &mut int) {}

        fn use_slot(slot) {
            let mut values = [5];
            take(values->[slot])
        }

        let first_slot = first;
        use_slot(first_slot)
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_local_shadow_must_be_subscript_value() {
    match experimental_session()
        .fail_compilation(indoc! { r#"
            subscript cell(values: &mut [int]) -> int {
                ref mut {
                    values[0]
                }
            }

            let cell = 0;
            let mut values = [5];
            values->[cell]
        "# })
        .into_inner()
    {
        CompilationErrorImpl::InvalidSubscriptUse { name, kind, .. } => {
            assert_eq!(name, ustr("cell"));
            assert_eq!(
                kind,
                ferlium::compiler::error::InvalidSubscriptUseKind::ValueIsNotSubscript
            );
        }
        other => panic!("expected invalid subscript use error, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_subscript_assignment_requires_mut_member() {
    match experimental_session()
        .fail_compilation(indoc! { r#"
            subscript cell(values: &mut [int]) -> int {
                ref {
                    values[0]
                }
            }

            let cell_slot = cell;
            let mut values = [5];
            values->[cell_slot] = 8
        "# })
        .into_inner()
    {
        CompilationErrorImpl::InvalidSubscriptUse { name, kind, .. } => {
            assert_eq!(name, ustr("cell_slot"));
            assert_eq!(
                kind,
                ferlium::compiler::error::InvalidSubscriptUseKind::MissingMember(
                    ferlium::module::SubscriptMemberKind::Mut,
                )
            );
        }
        other => panic!("expected invalid subscript use error, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn addressor_named_subscript_rvalue_reads_direct_place() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript first(values: &mut [int]) -> int {
            ref mut {
                values[0]
            }
        }

        let mut values = [8];
        values->[first]
    "# });

    assert_val_eq!(value, int(8));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn addressor_named_subscript_assignment_writes_direct_place() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript first(values: &mut [int]) -> int {
            ref mut {
                values[0]
            }
        }

        let mut values = [8];
        values->[first] = 13;
        values[0]
    "# });

    assert_val_eq!(value, int(13));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mut_addressor_return_selects_mut_member_of_nested_subscript() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript inner(values: &mut [int]) -> int {
            mut {
                values[0]
            }
        }

        subscript outer(values: &mut [int]) -> int {
            mut {
                values->[inner]
            }
        }

        let mut values = [8];
        values->[outer] = 13;
        values[0]
    "# });

    assert_val_eq!(value, int(13));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn addressor_named_subscript_compound_assignment_uses_single_place() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript first(values: &mut [int], log: &mut int) -> int {
            ref mut {
                log = log + 1;
                values[0]
            }
        }

        let mut values = [8];
        let mut log = 0;
        values->[first](log) += 5;
        (values[0], log)
    "# });

    assert_val_eq!(value, expected_tuple([int(13), int(1)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn nested_array_index_compound_assignment_composes_addressor_places() {
    let value = run_experimental_subscript_source(indoc! { r#"
        let mut values = [[1, 2], [3, 4]];
        values[0][1] += 10;
        (values[0][0], values[0][1], values[1][0], values[1][1])
    "# });

    assert_val_eq!(value, expected_tuple([int(1), int(12), int(3), int(4)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_index_receiver_can_drive_yielded_subscript() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript probe(slot: &mut int, log: &mut int) -> int {
            ref mut {
                log = log + 1;
                let mut local = slot;
                yield local;
                slot = local;
                log = log + 10
            }
        }

        let mut values = [5, 8];
        let mut log = 0;
        values[0]->[probe](log) += 2;
        (values[0], values[1], log)
    "# });

    assert_val_eq!(value, expected_tuple([int(7), int(8), int(11)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn yielded_subscript_result_can_be_indexed_by_mutable_consumer() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript row(rows: &mut [[int]], index: int, log: &mut int) -> [int] {
            ref mut {
                log = log + 1;
                let mut local = rows[index];
                yield local;
                rows[index] = local;
                log = log + 10
            }
        }

        let mut rows = [[1, 2], [3, 4]];
        let mut log = 0;
        rows->[row](0, log)[1] += 10;
        (rows[0][0], rows[0][1], rows[1][0], rows[1][1], log)
    "# });

    assert_val_eq!(
        value,
        expected_tuple([int(1), int(12), int(3), int(4), int(11)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn yielded_subscript_result_can_be_indexed_repeatedly_by_mutable_consumer() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript plane(cubes: &mut [[[int]]], index: int, log: &mut int) -> [[int]] {
            ref mut {
                log = log + 1;
                let mut local = cubes[index];
                yield local;
                cubes[index] = local;
                log = log + 10
            }
        }

        let mut cubes = [[[1, 2], [3, 4]], [[5, 6], [7, 8]]];
        let mut log = 0;
        cubes->[plane](0, log)[1][0] += 20;
        (cubes[0][0][0], cubes[0][1][0], cubes[0][1][1], cubes[1][0][0], log)
    "# });

    assert_val_eq!(
        value,
        expected_tuple([int(1), int(23), int(4), int(5), int(11)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_index_receiver_can_drive_addressor_subscript() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript first(values: &mut [int], log: &mut int) -> int {
            ref mut {
                log = log + 1;
                values[0]
            }
        }

        let mut values = [[5, 6], [8, 9]];
        let mut log = 0;
        values[0]->[first](log) += 2;
        (values[0][0], values[0][1], values[1][0], values[1][1], log)
    "# });

    assert_val_eq!(
        value,
        expected_tuple([int(7), int(6), int(8), int(9), int(1)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn yielded_subscript_result_field_can_be_assigned_by_mutable_consumer() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript first(items: &mut [{other: int, value: int}], log: &mut int) -> {other: int, value: int} {
            ref mut {
                log = log + 1;
                let mut local = items[0];
                yield local;
                items[0] = local;
                log = log + 10
            }
        }

        let mut items = [{value: 5, other: 8}];
        let mut log = 0;
        items->[first](log).value = 13;
        (items[0].value, items[0].other, log)
    "# });

    assert_val_eq!(value, expected_tuple([int(13), int(8), int(11)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn yielded_subscript_result_field_compound_assignment_uses_single_projection() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript first(items: &mut [{other: int, value: int}], log: &mut int) -> {other: int, value: int} {
            ref mut {
                log = log + 1;
                let mut local = items[0];
                yield local;
                items[0] = local;
                log = log + 10
            }
        }

        let mut items = [{value: 5, other: 8}];
        let mut log = 0;
        items->[first](log).value += 2;
        (items[0].value, items[0].other, log)
    "# });

    assert_val_eq!(value, expected_tuple([int(7), int(8), int(11)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn field_receiver_can_drive_yielded_subscript_and_index() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript row(rows: &mut [[int]], index: int, log: &mut int) -> [int] {
            ref mut {
                log = log + 1;
                let mut local = rows[index];
                yield local;
                rows[index] = local;
                log = log + 10
            }
        }

        let mut table = {rows: [[1, 2], [3, 4]], tag: 99};
        let mut log = 0;
        table.rows->[row](0, log)[1] += 10;
        (table.rows[0][0], table.rows[0][1], table.rows[1][0], table.tag, log)
    "# });

    assert_val_eq!(
        value,
        expected_tuple([int(1), int(12), int(3), int(99), int(11)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscripts_separated_by_field_unwind_lifo() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript outer(holder: &mut {other: int, slot: int}, log: &mut int) -> {other: int, slot: int} {
            mut {
                log = log * 10 + 1;
                let mut local = holder;
                yield local;
                holder = local;
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

        let mut holder = {slot: 5, other: 8};
        let mut log = 0;
        holder->[outer](log).slot->[inner](log) += 2;
        (holder.slot, holder.other, log)
    "# });

    assert_val_eq!(value, expected_tuple([int(7), int(8), int(1342)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_can_be_passed_as_mutable_function_argument() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn bump(slot: &mut int) {
            slot = slot + 1
        }

        subscript cell(slot: &mut int) -> int {
            ref mut {
                let mut local = slot;
                yield local;
                slot = local
            }
        }

        let mut slot = 5;
        bump(slot->[cell]);
        slot
    "# });

    assert_val_eq!(value, int(6));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_field_can_be_passed_as_mutable_function_argument() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn bump(slot: &mut int) {
            slot = slot + 1
        }

        subscript cell(holder: &mut {other: int, slot: int}, log: &mut int) -> {other: int, slot: int} {
            ref mut {
                log = log + 1;
                let mut local = holder;
                yield local;
                holder = local;
                log = log + 10
            }
        }

        let mut holder = {slot: 5, other: 8};
        let mut log = 0;
        bump(holder->[cell](log).slot);
        (holder.slot, holder.other, log)
    "# });

    assert_val_eq!(value, expected_tuple([int(6), int(8), int(11)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_multiple_named_subscripts_as_mutable_function_arguments() {
    assert_unsupported_subscript_feature(
        indoc! { r#"
            fn add_to_both(first: &mut int, second: &mut int) {
                first = first + 1;
                second = second + 1
            }

            subscript cell(slot: &mut int) -> int {
                ref mut {
                    let mut local = slot;
                    yield local;
                    slot = local
                }
            }

            let mut first = 1;
            let mut second = 2;
            add_to_both(first->[cell], second->[cell])
        "# },
        UnsupportedSubscriptFeatureKind::MultipleMutableSubscriptArguments,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn multiple_mutable_addressor_projections_are_allowed_as_arguments() {
    // Addressor-place projections lower to direct places, so several mutable ones can be driven
    // around a single call. This used to be rejected by a pre-inference approximation that could
    // not tell addressor projections from suspended ones.
    let value = run_experimental_subscript_source(indoc! { r#"
        fn add_to_both(first: &mut int, second: &mut int) {
            first = first + 1;
            second = second + 1
        }

        #[private_repr]
        struct Cell {
            v: int,
        }

        subscript Cell.value(self) -> int {
            ref mut {
                self.v
            }
        }

        let mut a = Cell { v: 1 };
        let mut b = Cell { v: 2 };
        add_to_both(a.value, b.value);
        (a.value, b.value)
    "# });

    assert_val_eq!(value, expected_tuple([int(2), int(3)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rejects_multiple_mutable_yielded_projections_as_arguments() {
    // Suspended (yield-based) projection accessors keep a call frame parked at their `yield`, and
    // only one such frame can be resumed per call, so two mutable ones must be rejected. This is
    // now detected from real accessor provenance rather than predicted before inference.
    assert_unsupported_subscript_feature(
        indoc! { r#"
            fn add_to_both(first: &mut int, second: &mut int) {
                first = first + 1;
                second = second + 1
            }

            #[private_repr]
            struct Secret {
                v: int,
            }

            subscript Secret.value(self) -> int {
                mut {
                    let mut local = self.v;
                    yield local;
                    self.v = local
                }
            }

            let mut a = Secret { v: 1 };
            let mut b = Secret { v: 2 };
            add_to_both(a.value, b.value)
        "# },
        UnsupportedSubscriptFeatureKind::MultipleMutableSubscriptArguments,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn materialized_yielded_projection_in_non_driven_argument_does_not_count_as_call_driver() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn add(first: &mut int, second: int) {
            first = first + second
        }

        #[private_repr]
        struct Secret {
            v: int,
        }

        subscript Secret.value(self) -> int {
            ref {
                let local = self.v;
                yield local
            }
            mut {
                let mut local = self.v;
                yield local;
                self.v = local
            }
        }

        let mut first = Secret { v: 1 };
        let mut second = Secret { v: 2 };
        add(first.value, { let x = second.value; x });
        first.value
    "# });

    assert_val_eq!(value, int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn materialized_yielded_projection_in_driver_accessor_argument_does_not_count_as_call_driver() {
    // The single driven argument `holder->[cell](s.value)` keeps one suspended accessor around the
    // call; the accessor's own argument `s.value` materializes a yielded projection that completes
    // before the call and must not be counted as a second suspended accessor.
    let value = run_experimental_subscript_source(indoc! { r#"
        fn bump(slot: &mut int) {
            slot = slot + 1
        }

        subscript cell(slot: &mut int, extra: int) -> int {
            mut {
                let mut local = slot;
                yield local;
                slot = local + extra
            }
        }

        #[private_repr]
        struct Secret {
            v: int,
        }

        subscript Secret.value(self) -> int {
            ref {
                let local = self.v;
                yield local
            }
        }

        let mut holder = 5;
        let mut s = Secret { v: 10 };
        bump(holder->[cell](s.value));
        holder
    "# });

    // bump increments the yielded slot 5 -> 6, then the epilogue writes back 6 + extra(10) = 16.
    assert_val_eq!(value, int(16));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn materialized_yielded_projection_in_driver_index_expression_does_not_count_as_call_driver() {
    // Two mutable driven arguments: `s.value` is a suspended yielded projection (one frame parked
    // around the call), while `values[idx.value]` is an addressor place that nests freely. The
    // index expression `idx.value` materializes a yielded projection that completes before the
    // call and must not be counted as a second suspended accessor.
    let value = run_experimental_subscript_source(indoc! { r#"
        fn add_to_both(first: &mut int, second: &mut int) {
            first = first + 1;
            second = second + 1
        }

        #[private_repr]
        struct Secret {
            v: int,
        }

        subscript Secret.value(self) -> int {
            ref {
                let local = self.v;
                yield local
            }
            mut {
                let mut local = self.v;
                yield local;
                self.v = local
            }
        }

        let mut s = Secret { v: 5 };
        let mut idx = Secret { v: 1 };
        let mut values = [10, 20, 30];
        add_to_both(s.value, values[idx.value]);
        (s.value, values[1])
    "# });

    // s.value: 5 -> 6; values[idx.value=1]: 20 -> 21.
    assert_val_eq!(value, expected_tuple([int(6), int(21)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn explicit_projection_passed_by_value_to_generic_is_materialized() {
    // A by-value argument never needs the projection place kept live, so an explicit projection
    // passed to a generic by-value parameter is materialized rather than driven as a place.
    let value = run_experimental_subscript_source(indoc! { r#"
        fn ident<T>(x: T) -> T { x }

        #[private_repr]
        struct Secret {
            items: [int],
        }

        subscript Secret.value(self) -> int {
            ref mut {
                self.items[0]
            }
        }

        let mut secret = Secret { items: [4] };
        ident(secret.value)
    "# });

    assert_val_eq!(value, int(4));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn module_function_and_subscript_member_can_be_mutually_recursive() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn read(slot: &mut int, depth: int) -> int {
            if depth == 0 {
                slot
            } else {
                slot->[cell](depth - 1)
            }
        }

        subscript cell(slot: &mut int, depth: int) -> int {
            ref {
                let local = read(slot, depth);
                yield local
            }
        }

        let mut slot = 13;
        read(slot, 1)
    "# });

    assert_val_eq!(value, int(13));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn module_function_and_projection_subscript_member_can_be_mutually_recursive() {
    let value = run_experimental_subscript_source(indoc! { r#"
        fn read(secret: Secret, depth: int) -> int {
            if depth == 0 {
                secret.raw
            } else {
                secret.value
            }
        }

        #[private_repr]
        struct Secret {
            raw: int,
        }

        subscript Secret.value(self) -> int {
            ref {
                let local = read(self, 0);
                yield local
            }
        }

        let secret = Secret { raw: 21 };
        read(secret, 1)
    "# });

    assert_val_eq!(value, int(21));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn subscript_member_can_depend_on_same_subscript_bundle() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell(slot: &mut int, depth: int) -> int {
            ref {
                let local = if depth == 0 {
                    slot
                } else {
                    slot->[cell](depth - 1)
                };
                yield local
            }
        }

        let mut slot = 21;
        slot->[cell](2)
    "# });

    assert_val_eq!(value, int(21));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn subscript_members_can_be_mutually_recursive_across_bundles() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript left(slot: &mut int, depth: int) -> int {
            ref {
                let local = if depth == 0 {
                    slot
                } else {
                    slot->[right](depth - 1)
                };
                yield local
            }
        }

        subscript right(slot: &mut int, depth: int) -> int {
            ref {
                let local = if depth == 0 {
                    slot
                } else {
                    slot->[left](depth - 1)
                };
                yield local
            }
        }

        let mut slot = 34;
        slot->[left](3)
    "# });

    assert_val_eq!(value, int(34));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_shared_ref_mut_subscript_member_attaches_for_reads_and_writes() {
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript cell(slot: &mut int, depth: int, log: &mut int) -> int {
            ref mut {
                log = log + 1;
                let mut local = if depth == 0 {
                    slot
                } else {
                    slot->[cell](depth - 1, log)
                };
                yield local;
                slot = local;
                log = log + 10
            }
        }

        let mut slot = 5;
        let mut log = 0;
        slot->[cell](2, log) += 1;
        (slot, log)
    "# });

    assert_val_eq!(value, expected_tuple([int(6), int(33)]));
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
fn named_subscript_instantiates_member_effect_variables_at_use_site() {
    let mut session = experimental_session();
    let compiled = session.compile(indoc! { r#"
        subscript cell<! E>(slot: &mut int, callback: () -> () ! E) -> int {
            ref {
                callback();
                let local = slot;
                yield local
            }
        }

        let mut slot = 1;
        slot->[cell](|| effects::read())
    "# });

    let module = session.session().expect_fresh_module(compiled.module_id);
    let expr = compiled
        .expr
        .expect("compiled source should have an expression");
    let effects = module.hir_arena[expr.expr].effects.clone();
    assert_eq!(effects, effect(PrimitiveEffect::Read));
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
fn first_class_subscript_value_captures_hidden_evidence() {
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

            let cell_slot = cell;
            let copied_cell_slot = cell_slot;
            let mut number = 5;
            let before = number->[cell_slot];
            number->[copied_cell_slot] = 7;
            (before, number)
        "# });

    assert_val_eq!(value, expected_tuple([int(5), int(7)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_subscript_value_passes_captured_hidden_evidence() {
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

            fn read_with(accessor) -> int {
                let mut number = 5;
                number->[accessor]
            }

            fn write_with(accessor) -> int {
                let mut number = 5;
                number->[accessor] = 8;
                number
            }

            let accessor = cell;
            (read_with(accessor), write_with(accessor))
        "# });

    assert_val_eq!(value, expected_tuple([int(5), int(8)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_subscript_value_hir_captures_hidden_evidence() {
    fn contains_build_subscript_value_with_evidence(arena: &ENodeArena, node: ENodeId) -> bool {
        match &arena[node].kind {
            NodeKind::BuildSubscriptValue(build) if !build.evidence_captures.is_empty() => true,
            _ => crate::harness::hir_child_nodes(arena, node)
                .into_iter()
                .any(|child| contains_build_subscript_value_with_evidence(arena, child)),
        }
    }

    let mut session = experimental_session();
    let module_id = session
        .compile(indoc! { r#"
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

            fn use_cell() {
                let cell_slot = cell;
                let mut number = 5;
                number->[cell_slot]
            }
        "# })
        .module_id;
    let module = session.session().expect_fresh_module(module_id);
    let function = module
        .get_function(ustr("use_cell"))
        .expect("use_cell should be compiled");
    let entry = function.get_code_entry().unwrap();

    assert!(
        contains_build_subscript_value_with_evidence(&module.hir_arena, entry),
        "capturing a constrained first-class subscript should build hidden evidence"
    );
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
