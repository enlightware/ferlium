// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use super::harness::{TestSession, expected_array_infer, expected_tuple, int, string};
use ferlium::{
    SourceId,
    ast::{ModuleDisplay, PExprKind, SubscriptMemberMode},
    compiler::error::{
        CompilationErrorImpl, InvalidRecordFieldContext, InvalidSubscriptDefinitionKind,
        InvalidYieldKind, MutabilityMustBeWhat, SourceFailureKind, SubscriptDefinitionSubject,
        UnsupportedSubscriptFeatureKind,
    },
    format::FormatWith,
    hir::{ENodeArena, ENodeId, NodeKind},
    module::{ShowModuleWithOptions, YieldProvenance, id::Id},
    parse_module_and_expr,
    std::{array::int_array_type, math::int_type},
    types::{
        effects::{PrimitiveEffect, effect, no_effects},
        r#type::TypeKind,
    },
};
use indoc::{formatdoc, indoc};
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
fn formats_subscript_member_body_with_nested_indentation() {
    let (module, _, arena) = parse_module_and_expr(
        indoc! { r#"
            subscript Pixel.x(self) -> int {
                ref mut {
                    self.coords[0]
                }
            }
        "# },
        SourceId::from_index(1),
        true,
    )
    .expect("projection subscript module should parse");
    let session = TestSession::new();

    let rendered = ModuleDisplay::new(&module, &arena)
        .format_with(&session.std_module_env())
        .to_string();

    assert_eq!(
        rendered,
        indoc! { r#"
            Subscripts:
                subscript Pixel.x(self) -> int {
                  ref mut
                  self
                    .coords
                  [
                    0
                  ]
                }
        "# }
    );
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
fn native_addressor_rooted_in_a_scalar_receiver() {
    let value = experimental_session().run(indoc! { r#"
        fn read(x: int) -> int { testing::int_self(x) }
        let y: int = 5;
        read(41) * 10 + testing::int_self(y) + 3
    "# });
    assert_val_eq!(value, int(418));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn native_member_addressor_forwarding_and_pattern_matching() {
    let value = experimental_session().run(indoc! { r#"
        subscript forward<T>(value: &mut T) -> T {
            ref mut { value }
        }
        let mut owner = testing::make_clone_tracked();
        let before = match owner.readonly { 7 => 700, _ => 0 };
        owner.self_member->[forward] = testing::make_clone_tracked();
        owner.payload->[forward] = 13;
        match owner.payload->[forward] {
            13 => before + owner.self_member.payload,
            _ => 0,
        }
    "# });
    assert_val_eq!(value, int(713));
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
            raw: int,
        }

        subscript value(slot: &mut int) -> int {
            ref mut {
                slot
            }
        }

        subscript Secret.value(self) -> int {
            ref mut {
                self.raw
            }
        }

        let mut slot = 3;
        let secret = Secret { raw: 8 };
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
            first: A,
            second: B,
        }

        subscript Pair<A, B>.left(self) -> A {
            ref mut {
                self.first
            }
        }

        let mut pair = Pair { first: 2, second: "ignored" };
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
fn resolved_projection_subscripts_lower_to_static_apply() {
    fn contains_subscript_apply(arena: &ENodeArena, node: ENodeId) -> bool {
        match &arena[node].kind {
            NodeKind::SubscriptApply(_) => true,
            _ => crate::harness::hir_child_nodes(arena, node)
                .into_iter()
                .any(|child| contains_subscript_apply(arena, child)),
        }
    }

    fn count_static_projection_member_calls(arena: &ENodeArena, node: ENodeId) -> usize {
        let here = match &arena[node].kind {
            NodeKind::StaticApply(app) => app.ty.result_convention.returns_borrow() as usize,
            _ => 0,
        };
        here + crate::harness::hir_child_nodes(arena, node)
            .into_iter()
            .map(|child| count_static_projection_member_calls(arena, child))
            .sum::<usize>()
    }

    let mut session = experimental_session();
    let module = session.compile_and_get_module(indoc! { r#"
        struct Pixel {
            coords: [int],
        }

        subscript Pixel.x(self) -> int {
            ref mut {
                self.coords[0]
            }
        }

        subscript Pixel.y(self) -> int {
            ref mut {
                self.coords[1]
            }
        }

        pub fn dist2(p: Pixel) {
            p.x * p.x + p.y * p.y
        }

        #[private_repr]
        struct Secret {
            raw: int,
        }

        subscript Secret.value(self) -> int {
            ref {
                let local = self.raw;
                yield local
            }
        }

        pub fn read_secret(secret: Secret) {
            secret.value + secret.value
        }
    "# });
    let dist2 = module
        .get_function(ustr("dist2"))
        .expect("dist2 should be compiled");
    let dist2_entry = dist2.get_code_entry().unwrap();
    let read_secret = module
        .get_function(ustr("read_secret"))
        .expect("read_secret should be compiled");
    let read_secret_entry = read_secret.get_code_entry().unwrap();

    assert!(
        !contains_subscript_apply(&module.hir_arena, dist2_entry),
        "resolved projection subscripts should not materialize first-class subscript applications"
    );
    assert_eq!(
        count_static_projection_member_calls(&module.hir_arena, dist2_entry),
        4,
        "each addressor p.x/p.y projection should statically call the selected subscript member"
    );
    assert!(
        !contains_subscript_apply(&module.hir_arena, read_secret_entry),
        "resolved yielded projection subscripts should not materialize first-class subscript applications"
    );
    assert_eq!(
        count_static_projection_member_calls(&module.hir_arena, read_secret_entry),
        2,
        "each yielded secret.value projection should statically call the selected subscript member"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn subscript_member_function_names_are_generated() {
    let mut session = experimental_session();
    let module_id = session
        .compile(indoc! { r#"
            struct Pixel {
                coords: [int],
            }

            subscript Pixel.x(self) -> int {
                ref mut {
                    self.coords[0]
                }
            }

            #[private_repr]
            struct Secret {
                raw: int,
            }

            subscript Secret.value(self) -> int {
                ref {
                    let local = self.raw;
                    yield local
                }
            }

            subscript cell(slot: &mut int) -> int {
                ref mut {
                    slot
                }
            }

            pub fn use_all(pixel: Pixel, secret: Secret, slot: &mut int) -> int {
                pixel.x + secret.value + slot->[cell]
            }
        "# })
        .module_id;
    let compiler_session = session.session();
    let module = compiler_session.expect_fresh_module(module_id);
    let rendered = module
        .format_with(&ShowModuleWithOptions::new(
            compiler_session.modules(),
            true,
            true,
        ))
        .to_string();
    let module_name = module.path().to_string();

    assert!(
        rendered.contains("Pixel.x::ref_mut#subscript:"),
        "expected generated addressor projection subscript member name:\n{rendered}"
    );
    assert!(
        rendered.contains("Secret.value::ref#subscript:"),
        "expected generated yielded projection subscript member name:\n{rendered}"
    );
    assert!(
        rendered.contains("cell::ref_mut#subscript:"),
        "expected generated named subscript member name:\n{rendered}"
    );
    assert!(
        !rendered.contains(&format!("{module_name}::{module_name}::")),
        "generated subscript member names should not duplicate module qualification:\n{rendered}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generated_structural_projection_subscript_member_functions_are_named() {
    let mut session = experimental_session();
    let module_id = session
        .compile(indoc! { r#"
            fn read_value(container) -> int {
                container.value
            }

            pub fn run() -> int {
                read_value({ value: 41 }) + 1
            }
        "# })
        .module_id;
    let compiler_session = session.session();
    let module = compiler_session.expect_fresh_module(module_id);
    let rendered = module
        .format_with(&ShowModuleWithOptions::new(
            compiler_session.modules(),
            true,
            true,
        ))
        .to_string();

    assert!(
        rendered.contains(".value::ref_mut#subscript:"),
        "expected generated structural projection subscript member name:\n{rendered}"
    );
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
        .expect_invalid_effect_inclusion(
            effect(PrimitiveEffect::Write),
            effect(PrimitiveEffect::Read),
        );
}

/// A blanket impl of a pure method may only use projection evidence whose effects are pure.
///
/// `before_read` runs in the method body before it reads `x`, and `field_value` is the value
/// `Ratio`'s projection yields.
fn pure_method_over_projection_source(before_read: &str, field_value: &str) -> String {
    format!(
        indoc! { r#"
            trait ReadX<Self> {{
                fn read_x(value: Self) -> int;
            }}

            impl<T> ReadX for T {{
                fn read_x(value: T) -> int {{
                    {};
                    value.x
                }}
            }}

            #[private_repr]
            struct Ratio {{
                divisor: int,
            }}

            subscript Ratio.x(self) -> int {{
                ref {{
                    let local = {};
                    yield local
                }}
            }}

            read_x(Ratio {{ divisor: 0 }})
        "# },
        before_read, field_value
    )
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn blanket_impl_of_pure_method_accepts_pure_projection_evidence() {
    for before_read in ["()", "value.x"] {
        let value = run_experimental_subscript_source(&pure_method_over_projection_source(
            before_read,
            "self.divisor",
        ));
        assert_val_eq!(value, int(0));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn blanket_impl_of_pure_method_rejects_fallible_projection_evidence() {
    // Read once, the method's effect is the evidence's; read twice, it is a union of variables.
    for before_read in ["()", "value.x"] {
        experimental_session()
            .fail_compilation(&pure_method_over_projection_source(
                before_read,
                "idiv(1, self.divisor)",
            ))
            .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
    }
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
fn projection_subscript_rejects_the_name_of_a_stored_field() {
    // A field name of a type means one thing, also where its representation is private and
    // the stored field is seen by its module only, and for a type with arguments.
    for (attribute, generics, field_ty) in [
        ("", "", "int"),
        ("#[private_repr]", "", "int"),
        ("", "<T>", "T"),
        ("#[private_repr]", "<T>", "T"),
    ] {
        assert_invalid_subscript_definition(
            &formatdoc! { r#"
                {attribute}
                struct Point{generics} {{
                    x: {field_ty},
                    y: int,
                }}

                subscript Point{generics}.x(self) -> {field_ty} {{
                    ref mut {{
                        self.x
                    }}
                }}
            "# },
            SubscriptDefinitionSubject::Subscript(ustr("x")),
            InvalidSubscriptDefinitionKind::ProjectionConflictsWithStructuralField,
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn projection_subscript_rejects_duplicate_receiver_field() {
    assert_invalid_subscript_definition(
        indoc! { r#"
            #[private_repr]
            struct Secret {
                raw: int,
            }

            subscript Secret.value(self) -> int {
                ref mut {
                    self.raw
                }
            }

            subscript Secret.value(self) -> int {
                ref mut {
                    self.raw
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

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn custom_addressor_indices_do_not_prove_disjoint_mutable_arguments() {
    // Include a name matching std: only the resolved std member identity carries the law.
    for name in ["slot", "array_index"] {
        let source = format!(
            r#"
                subscript {name}(values: &mut [int], index: int) -> int {{
                    ref mut {{ return values[0] }}
                }}
                fn write(left: &mut int, right: &mut int) {{ left = 1; right = 2 }}
                let mut values = [0, 0];
                write(values->[{name}](0), values->[{name}](1));
                values
            "#
        );
        experimental_session()
            .fail_compilation(&source)
            .expect_mutable_paths_overlap();
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn custom_addressor_overlaps_direct_array_index() {
    experimental_session()
        .fail_compilation(
            r#"
            subscript slot(values: &mut [int], index: int) -> int {
                ref mut { return values[0] }
            }
            fn write(left: &mut int, right: &mut int) { left = 1; right = 2 }
            let mut values = [0, 0];
            write(values->[slot](1), values[0]);
            values
        "#,
        )
        .expect_mutable_paths_overlap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn custom_addressor_boolean_selectors_remain_opaque() {
    experimental_session()
        .fail_compilation(
            r#"
            subscript slot(values: &mut [int], index: bool) -> int {
                ref mut { return values[0] }
            }
            fn write(left: &mut int, right: &mut int) { left = 1; right = 2 }
            let mut values = [0];
            write(values->[slot](false), values->[slot](true));
            values
        "#,
        )
        .expect_mutable_paths_overlap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn custom_addressor_shared_argument_is_snapshotted_before_mutation() {
    let value = run_experimental_subscript_source(
        r#"
        subscript slot(values: &mut [int], index: int) -> int {
            ref mut { return values[0] }
        }
        fn update(observed: int, target: &mut int) -> int {
            target = 9;
            observed
        }
        let mut values = [3, 4];
        update(values->[slot](0), values->[slot](1))
    "#,
    );
    assert_val_eq!(value, int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn custom_addressor_managed_shared_argument_owns_its_snapshot() {
    let value = run_experimental_subscript_source(
        r#"
        subscript slot(values: &mut [string], index: int) -> string {
            ref mut { return values[0] }
        }
        fn update(observed: string, target: &mut string) -> string {
            target = "new";
            observed
        }
        let mut values = ["old"];
        update(values->[slot](0), values->[slot](1))
    "#,
    );
    assert_val_eq!(value, string("old"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn custom_addressor_shared_argument_is_snapshotted_before_later_argument_write() {
    let value = run_experimental_subscript_source(
        r#"
        subscript slot(values: &mut [int], index: int) -> int {
            ref mut { return values[0] }
        }
        fn first(observed: int, ignored: int) -> int { observed }
        let mut values = [3];
        first(values->[slot](0), { values->[slot](1) = 9; 0 })
    "#,
    );
    assert_val_eq!(value, int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_addressor_shared_argument_is_snapshotted_before_later_argument_write() {
    // Array address calculation borrows its receiver immutably: the write footprint must come
    // from the assignment through the scoped binding, not from the accessor's arguments.
    let value = run_experimental_subscript_source(
        r#"
        fn first(observed: int, ignored: int) -> int { observed }
        let mut values = [3];
        first(values[0], { values[0] = 9; 0 })
    "#,
    );
    assert_val_eq!(value, int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn custom_addressors_on_disjoint_structural_receivers_remain_usable() {
    let value = run_experimental_subscript_source(
        r#"
        subscript slot(values: &mut [int], index: int) -> int {
            ref mut { return values[0] }
        }
        fn write(left: &mut int, right: &mut int) { left = 1; right = 2 }
        let mut values = ([0], [0]);
        write(values.0->[slot](0), values.1->[slot](1));
        (values.0[0], values.1[0])
    "#,
    );
    assert_val_eq!(value, expected_tuple(vec![int(1), int(2)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_array_indices_preserve_disjoint_mutable_access() {
    let value = run_experimental_subscript_source(
        r#"
        fn swap<A>(left: &mut A, right: &mut A) {
            let old = left;
            left = right;
            right = old
        }
        fn swap_first_two<A>(values: &mut [A]) { swap(values[0], values[1]) }
        let mut values = [1, 2];
        swap_first_two(values);
        values
    "#,
    );
    assert_val_eq!(value, expected_array_infer([int(2), int(1)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn disjoint_named_structural_fields_do_not_snapshot_managed_arguments() {
    let source = r#"
        struct Pair<A> { a: A, b: int }
        fn observe(a: string, b: &mut int) -> int { b = 9; len(a) }
        fn access(value: &mut Pair<string>) -> int { observe(value.a, value.b) }
        fn access_record(value: &mut { a: string, b: int }) -> int { observe(value.a, value.b) }
        fn inferred() -> int {
            let mut value = Pair { a: "hello", b: 0 };
            observe(value.a, value.b)
        }
        let mut value = Pair { a: "hello", b: 0 };
        (access(value) + inferred(), value.b)
    "#;
    let mir = experimental_session().emit_mir(source);
    for name in ["access", "access_record", "inferred"] {
        let header = format!("fn {name}(");
        let body = mir
            .split(&header)
            .nth(1)
            .expect("access body")
            .split("\nfn ")
            .next()
            .unwrap();
        assert!(
            !body.contains("clone "),
            "disjoint fields must be borrowed directly:\n{body}"
        );
    }
    assert_val_eq!(
        run_experimental_subscript_source(source),
        expected_tuple([int(10), int(9)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn custom_addressor_nested_fields_do_not_restore_disjointness() {
    experimental_session()
        .fail_compilation(
            r#"
            subscript slot(values: &mut [(int, int)], index: int) -> (int, int) {
                ref mut { return values[0] }
            }
            fn write(left: &mut int, right: &mut int) { left = 1; right = 2 }
            let mut values = [(0, 0)];
            write(values->[slot](0).0, values->[slot](1).1);
            values
        "#,
        )
        .expect_mutable_paths_overlap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn custom_addressor_first_class_subscript_keeps_receiver_aliasing() {
    experimental_session()
        .fail_compilation(
            r#"
            subscript slot(values: &mut [int], index: int) -> int {
                ref mut { return values[0] }
            }
            fn write(left: &mut int, right: &mut int) { left = 1; right = 2 }
            let accessor = slot;
            let mut values = [0, 0];
            write(values->[accessor](0), values->[accessor](1));
            values
        "#,
        )
        .expect_mutable_paths_overlap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn custom_addressor_field_names_do_not_prove_disjointness() {
    experimental_session()
        .fail_compilation(
            r#"
            fn write(left: &mut int, right: &mut int) { left = 1; right = 2 }
            fn update(value: &mut Pair) { write(value.left, value.right) }

            #[private_repr]
            struct Pair { item: int }
            subscript Pair.left(self) -> int { ref mut { self.item } }
            subscript Pair.right(self) -> int { ref mut { self.item } }
            let mut value = Pair { item: 0 };
            update(value);
            value.item
        "#,
        )
        .expect_mutable_paths_overlap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn custom_addressor_shared_field_is_snapshotted() {
    let value = run_experimental_subscript_source(
        r#"
        fn update(observed: int, target: &mut int) -> int { target = 9; observed }
        fn observe(value: &mut Pair) -> int { update(value.left, value.right) }

        #[private_repr]
        struct Pair { item: int }
        subscript Pair.left(self) -> int { ref mut { self.item } }
        subscript Pair.right(self) -> int { ref mut { self.item } }
        let mut value = Pair { item: 3 };
        observe(value)
    "#,
    );
    assert_val_eq!(value, int(3));
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
fn scoped_subscript_scalar_arguments_reach_the_accessor() {
    // Scalar arguments reach a scoped accessor as values: a parameter, a computed value, a literal,
    // and a generic argument that specialization makes an `int`.
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript at(slot: &mut [int], k: int) -> int {
            ref mut { let mut local = slot[k] + k; yield local; slot[k] = local - k }
        }
        subscript tagged<A, B>(slot: &mut [A], k: B) -> A {
            ref mut { let i = if k == k { 1 } else { 0 }; let mut local = slot[i]; yield local; slot[i] = local }
        }
        fn bump(a: &mut [int], k: int) { a->[at](k) += 10; a->[at](k + 1) += 100; a->[at](0) += 1000 }
        fn swap_second<A, B>(a: &mut [A], k: B, v: A) { a->[tagged](k) = v }
        let mut a = [1, 2, 3];
        bump(a, 1);
        swap_second(a, 7, 5);
        a[0] * 10000 + a[1] * 100 + a[2]
    "# });

    assert_val_eq!(value, int(10010000 + 500 + 103));
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
            raw: int,
        }

        subscript Secret.value(self) {
            ref mut {
                self.raw
            }
        }

        let mut secret = Secret { raw: 41 };
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
fn first_class_yielded_subscript_parameter_takes_a_scalar_argument() {
    // A first-class subscript takes every argument through a pointer, so the scalar index, a value
    // at the call site, is passed through a cell.
    let value = run_experimental_subscript_source(indoc! { r#"
        subscript at(slot: &mut [int], k: int) -> int {
            mut {
                let mut local = slot[k] + k;
                yield local;
                slot[k] = local
            }
        }

        #[inline(never)]
        fn bump(accessor, k: int) -> int {
            let mut values = [5, 6];
            values->[accessor](k) += 7;
            values->[accessor](k * 0) += 100;
            values[0] * 1000 + values[1]
        }

        let accessor = at;
        bump(accessor, 1)
    "# });

    assert_val_eq!(value, int(105014));
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
fn ordinary_assignment_captures_array_index_before_rhs() {
    assert_val_eq!(
        run_experimental_subscript_source(
            "let mut values = [1, 2]; let mut index = 0; \
             values[index] = { index = 1; 9 }; values",
        ),
        expected_array_infer([int(9), int(2)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ordinary_indirect_assignment_resolves_current_storage_after_rhs() {
    for source in [
        "let mut values = [1]; values[0] = { values = [1, 2]; 9 }; values",
        "let mut values = [1, 2]; values[0] = { values[0] = 4; 9 }; values",
        "let mut nested = [[1]]; nested[0][0] = { nested = [[1, 2]]; 9 }; nested[0]",
        r#"
            subscript first(values: &mut [int]) -> int { ref mut { values[0] } }
            let mut values = [1];
            values->[first] = { values = [1, 2]; 9 };
            values
        "#,
    ] {
        assert_val_eq!(
            run_experimental_subscript_source(source),
            expected_array_infer([int(9), int(2)])
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ordinary_indirect_assignment_allows_rhs_reads_and_disjoint_writes() {
    assert_val_eq!(
        run_experimental_subscript_source(
            "let mut values = [1, 2]; values[0] = { values[1] = 9; values[0] + 2 }; values",
        ),
        expected_array_infer([int(3), int(9)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ordinary_assignment_opens_addressor_after_rhs_once() {
    let value = run_experimental_subscript_source(
        r#"
        subscript cell(slot: &mut int, log: &mut int) -> int {
            ref mut {
                log = log * 10 + 2;
                slot
            }
        }
        let mut slot = 0;
        let mut log = 0;
        slot->[cell](log) = { log = log * 10 + 1; 9 };
        (slot, log)
    "#,
    );
    assert_val_eq!(value, expected_tuple([int(9), int(12)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ordinary_assignment_opens_yielded_accessor_after_rhs() {
    let value = run_experimental_subscript_source(
        r#"
        subscript cell(slot: &mut int, log: &mut int) -> int {
            mut {
                log = log * 10 + 2;
                let mut local = slot;
                yield local;
                slot = local;
                log = log * 10 + 3
            }
        }
        let mut slot = 0;
        let mut log = 0;
        slot->[cell](log) = { log = log * 10 + 1; 9 };
        (slot, log)
    "#,
    );
    assert_val_eq!(value, expected_tuple([int(9), int(123)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ordinary_assignment_captures_rhs_before_destination_mutation() {
    let value = run_experimental_subscript_source(
        r#"
        struct Pair { first: string, second: string }
        subscript Pair.target(self) -> string {
            mut {
                self.first = "changed";
                self.second
            }
        }
        let mut pair = Pair { first: "original", second: "old" };
        pair.target = pair.first;
        (pair.first, pair.second)
    "#,
    );
    assert_val_eq!(
        value,
        expected_tuple([string("changed"), string("original")])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ordinary_assignment_rhs_failure_precedes_destination_failure() {
    let error = experimental_session().fail_run(
        r#"
        let mut values: [int] = [];
        values[0] = idiv(1, 0)
    "#,
    );
    assert_eq!(error, SourceFailureKind::DivisionByZero);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ordinary_assignment_rhs_return_skips_destination_access() {
    assert_val_eq!(
        run_experimental_subscript_source(
            r#"
        fn run() -> int {
            let mut values: [int] = [];
            values[0] = { return 7 };
            0
        }
        run()
    "#
        ),
        int(7)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn compound_assignment_freezes_array_destination_once() {
    assert_val_eq!(
        run_experimental_subscript_source(
            "let mut values = [1, 2]; let mut index = -1; \
             values[{ index += 1; index }] += 1; (values, index)",
        ),
        expected_tuple([expected_array_infer([int(2), int(2)]), int(0)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn compound_and_expanded_assignment_capture_selectors_in_the_same_order() {
    let source = r#"
        let mut compound = [1, 2];
        let mut expanded = [1, 2];
        let mut compound_index = 0;
        let mut expanded_index = 0;
        compound[compound_index] += { compound_index += 1; 1 };
        expanded[expanded_index] = expanded[expanded_index] + {
            expanded_index += 1;
            1
        };
        (compound, expanded, compound_index, expanded_index)
    "#;
    assert_val_eq!(
        run_experimental_subscript_source(source),
        expected_tuple([
            expected_array_infer([int(2), int(2)]),
            expected_array_infer([int(2), int(2)]),
            int(1),
            int(1),
        ])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn compound_assignment_allows_proven_disjoint_literal_indices() {
    assert_val_eq!(
        run_experimental_subscript_source(
            "let mut values = [1, 2]; values[0] += values[1]; values"
        ),
        expected_array_infer([int(3), int(2)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ordinary_assignment_allows_proven_disjoint_literal_indices() {
    assert_val_eq!(
        run_experimental_subscript_source("let mut values = [1, 2]; values[0] = values[1]; values"),
        expected_array_infer([int(2), int(2)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn compound_assignment_allows_access_through_fresh_temporary() {
    assert_val_eq!(
        run_experimental_subscript_source(
            "fn get_values() { [1, 2] } let mut total = 0; total += get_values()[0]; total",
        ),
        int(1)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn compound_assignment_reads_destination_after_rhs() {
    for source in [
        "let mut values = [1, 2]; values[0] += { values[0] += 10; 1 }; values[0]",
        "let mut values = [1]; values[0] += { values = [10]; 2 }; values[0]",
        "let mut value = 1; value += { value = 10; 2 }; value",
    ] {
        assert_val_eq!(run_experimental_subscript_source(source), int(12));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn compound_assignment_allows_rhs_read_of_whole_container() {
    assert_val_eq!(
        run_experimental_subscript_source(
            "fn first(values) { values[0] } let mut values = [1, 2]; \
         values[0] += first(values); values"
        ),
        expected_array_infer([int(2), int(2)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn compound_assignment_captures_dynamic_rhs_access() {
    assert_val_eq!(
        run_experimental_subscript_source(
            "let mut values = [1, 2]; let i = 0; let j = 1; \
         values[i] += values[j]; values"
        ),
        expected_array_infer([int(3), int(2)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment_prepares_mutable_argument_places_but_captures_value_arguments() {
    for operator in ["=", "+="] {
        let source = format!(
            r#"
            subscript cell(slot: &mut int, log: &mut int, captured: int) -> int {{
                ref mut {{ log = log * 10 + captured; slot }}
            }}
            let mut slot = 0;
            let mut logs = [0, 0];
            let mut index = 0;
            let mut digit = 2;
            slot->[cell](logs[index], digit) {operator} {{
                index = 1;
                digit = 7;
                logs = [1, 9];
                5
            }};
            (slot, logs)
        "#
        );
        assert_val_eq!(
            run_experimental_subscript_source(&source),
            expected_tuple([int(5), expected_array_infer([int(12), int(9)])])
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment_prepares_late_inferred_mutable_arguments_as_places() {
    assert_val_eq!(
        run_experimental_subscript_source(
            r#"
        subscript cell(slot: &mut int, log: &mut int) -> int {
            ref mut { log += 1; slot }
        }
        fn update(accessor, log) {
            let mut slot = 0;
            slot->[accessor](log) = { log = 10; 5 };
            slot
        }
        let mut log = 0;
        let result = update(cell, log);
        (result, log)
    "#
        ),
        expected_tuple([int(5), int(11)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment_prepares_late_inferred_indexed_mutable_arguments() {
    for operator in ["=", "+="] {
        let source = format!(
            r#"
            subscript cell(slot: &mut int, log: &mut int) -> int {{
                ref mut {{ log += 1; slot }}
            }}
            fn update(accessor, logs, index) {{
                let mut slot = 0;
                slot->[accessor](logs[index]) {operator} {{
                    index = 1;
                    logs = [10, 20];
                    5
                }};
                slot
            }}
            // The captured index is only valid after the RHS replaces the array.
            let mut logs = [];
            let mut index = 0;
            let result = update(cell, logs, index);
            (result, logs, index)
        "#
        );
        assert_val_eq!(
            run_experimental_subscript_source(&source),
            expected_tuple([int(5), expected_array_infer([int(11), int(20)]), int(1),])
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment_captures_generic_value_arguments_before_rhs() {
    let source = r#"
        subscript cell<T>(slot: &mut T, value: T, seen: &mut T) -> T {
            ref mut { seen = value; slot }
        }
        fn update<T>(slot: &mut T, input: &mut T, seen: &mut T, replacement: T) {
            slot->[cell](input, seen) = { input = replacement; input };
        }
        let mut slot = "old";
        let mut input = "before";
        let mut seen = "";
        update(slot, input, seen, "after");
        (slot, input, seen)
    "#;
    assert_val_eq!(
        run_experimental_subscript_source(source),
        expected_tuple([string("after"), string("after"), string("before")])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment_capture_evidence_depends_on_argument_passing() {
    for (passing, needs_value) in [("", true), ("&mut ", false)] {
        let source = format!(
            r#"
            subscript cell<T>(slot: &mut int, unused: {passing}T) -> int {{
                ref mut {{ slot }}
            }}
            fn update<T>(slot: &mut int, input: &mut T) {{
                slot->[cell](input) = 5;
            }}
        "#
        );
        let definition = experimental_session().compile_and_get_fn_def(&source, "update");
        assert_eq!(!definition.ty_scheme.constraints.is_empty(), needs_value);
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment_checks_late_inferred_mutable_argument_overlap() {
    experimental_session()
        .fail_compilation(
            r#"
        subscript cell(slot: &mut int, a: &mut int, b: &mut int) -> int {
            ref mut { a += 1; b += 1; slot }
        }
        fn update(accessor, log) {
            let mut slot = 0;
            slot->[accessor](log, log) = { log = 10; 5 };
        }
        let mut log = 0;
        update(cell, log);
    "#,
        )
        .expect_mutable_paths_overlap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment_resolves_negative_index_against_post_rhs_length() {
    assert_val_eq!(
        run_experimental_subscript_source(
            "let mut values = [1]; values[-1] += { values = [10, 20]; 2 }; values"
        ),
        expected_array_infer([int(10), int(22)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment_cannot_reborrow_another_suspended_accessor_argument() {
    experimental_session()
        .fail_compilation(
            r#"
        subscript outer(slot: &mut int, log: &mut int) -> int {
            mut { let mut local = slot; yield local; slot = local; log += 1 }
        }
        subscript inner(slot: &mut int, log: &mut int) -> int {
            ref mut { log += 1; slot }
        }
        let mut slot = 0;
        let mut log = 0;
        slot->[outer](log)->[inner](log) = 7;
    "#,
        )
        .expect_exclusive_access_overlap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn read_cannot_reborrow_another_suspended_accessor_argument() {
    experimental_session()
        .fail_compilation(
            r#"
        subscript outer(slot: &mut int, log: &mut int) -> int {
            ref { let local = slot; yield local; log += 1 }
        }
        subscript inner(slot: int, log: &mut int) -> int {
            ref { let local = slot; log += 1; yield local }
        }
        let mut slot = 7;
        let mut log = 0;
        slot->[outer](log)->[inner](log)
    "#,
        )
        .expect_exclusive_access_overlap();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment_prepares_nested_selectors_before_any_accessor_opens() {
    assert_val_eq!(
        run_experimental_subscript_source(
            r#"
        subscript rows(values: &mut [[int]], log: &mut int) -> [int] {
            mut { log = log * 10 + 3; values[0] }
        }
        let mut values = [[1]];
        let mut log = 0;
        values->[rows](log)[{ log = log * 10 + 1; 0 }] += {
            log = log * 10 + 2; values = [[10]]; 2
        };
        (values[0][0], log)
    "#
        ),
        expected_tuple([int(12), int(123)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment_captures_first_class_accessor_before_rhs() {
    assert_val_eq!(
        run_experimental_subscript_source(
            r#"
        subscript first(values: &mut [int]) -> int { ref mut { values[0] } }
        subscript last(values: &mut [int]) -> int { ref mut { values[-1] } }
        let mut accessor = first;
        let mut values = [1, 2];
        values->[accessor] = { accessor = last; values = [3, 4]; 9 };
        values
    "#
        ),
        expected_array_infer([int(9), int(4)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment_selector_failure_precedes_rhs_and_destination_access() {
    let error = experimental_session().fail_run(
        r#"
        subscript rows(values: &mut [[int]]) -> [int] { mut { panic("opened"); values[0] } }
        let mut values = [[1]];
        values->[rows][idiv(1, 0)] = { panic("rhs"); 2 }
    "#,
    );
    assert_eq!(error, SourceFailureKind::DivisionByZero);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn assignment_selector_return_skips_accessor_opening() {
    for destination in [
        "values->[rows][{ return 7 }]",
        "values[0][{ return 7 }]",
        "values->[rows]->[cell]({ return 7 })",
        "values[0]->[cell]({ return 7 })",
    ] {
        let source = format!(
            r#"
            subscript rows(values: &mut [[int]]) -> [int] {{
                mut {{ panic("opened"); values[0] }}
            }}
            subscript cell(values: &mut [int], index: int) -> int {{ ref mut {{ values[index] }} }}
            fn run() -> int {{
                let mut values: [[int]] = [];
                {destination} = 2;
                0
            }}
            run()
        "#
        );
        assert_val_eq!(run_experimental_subscript_source(&source), int(7));
    }
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
fn named_subscript_read_chain_keeps_intermediate_array_as_place() {
    fn contains_int_array_clone(arena: &ENodeArena, node: ENodeId) -> bool {
        (matches!(arena[node].kind, NodeKind::CloneValue(_)) && arena[node].ty == int_array_type())
            || crate::harness::hir_child_nodes(arena, node)
                .into_iter()
                .any(|child| contains_int_array_clone(arena, child))
    }

    let mut session = experimental_session();
    let module = session.compile_and_get_module(indoc! { r#"
        subscript row(rows: &mut [[int]], index: int) -> [int] {
            ref mut {
                rows[index]
            }
        }

        struct Table { rows: [[int]] }

        fn read(table: &mut Table, row_index: int, column_index: int) -> int {
            table.rows->[row](row_index)[column_index]
        }
    "# });
    let read = module
        .get_function(ustr("read"))
        .expect("read function should be compiled");
    let entry = read.get_code_entry().unwrap();

    assert!(
        !contains_int_array_clone(&module.hir_arena, entry),
        "a mixed field/named-subscript/index read should clone only its final element"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn addressor_subscript_callee_remains_a_borrowed_place() {
    fn contains_function_clone(arena: &ENodeArena, node: ENodeId) -> bool {
        (matches!(arena[node].kind, NodeKind::CloneValue(_))
            && matches!(&*arena[node].ty.data(), TypeKind::Function(_)))
            || crate::harness::hir_child_nodes(arena, node)
                .into_iter()
                .any(|child| contains_function_clone(arena, child))
    }

    let source = indoc! { r#"
        #[private_repr]
        struct Holder { mapper: (int) -> int }

        subscript Holder.callable(self) -> (int) -> int {
            ref mut { self.mapper }
        }

        fn apply(holder: &mut Holder, value: int) -> int {
            holder.callable(value)
        }
    "# };
    let mut session = experimental_session();
    let module = session.compile_and_get_module(source);
    let apply = module
        .get_function(ustr("apply"))
        .expect("apply function should be compiled");
    assert!(
        !contains_function_clone(&module.hir_arena, apply.get_code_entry().unwrap()),
        "an addressor-place function callee should be borrowed directly"
    );

    let execution_source = format!(
        "{source}\n{}",
        "let mut holder = Holder { mapper: |x| x + 1 }; apply(holder, 41)"
    );
    assert_val_eq!(
        run_experimental_subscript_source(&execution_source),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn yielded_subscript_callee_finishes_before_argument_evaluation() {
    let value = run_experimental_subscript_source(indoc! { r#"
        struct Holder { mapper: (int) -> int }

        subscript callable(holder: Holder, log: &mut int) -> (int) -> int {
            ref {
                log = log * 10 + 1;
                let mapper = holder.mapper;
                yield mapper;
                log = log * 10 + 2
            }
        }

        fn argument(log: &mut int) -> int {
            log = log * 10 + 3;
            41
        }

        let holder = Holder { mapper: |x| x + 1 };
        let mut log = 0;
        let result = (holder->[callable](log))(argument(log));
        (result, log)
    "# });

    // The accessor prologue (1), epilogue (2), then call argument (3) must run in that order.
    assert_val_eq!(value, expected_tuple([int(42), int(123)]));
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
        let mut outer_log = 0;
        let mut inner_log = 0;
        holder->[outer](outer_log).slot->[inner](inner_log) += 2;
        (holder.slot, holder.other, outer_log, inner_log)
    "# });

    assert_val_eq!(value, expected_tuple([int(7), int(8), int(12), int(34)]));
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
        let mut outer_log = 0;
        let mut inner_log = 0;
        slot->[outer](outer_log)->[inner](inner_log) = 7;
        (slot, outer_log, inner_log)
    "# });

    assert_val_eq!(value, expected_tuple([int(7), int(12), int(34)]));
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
        let mut outer_log = 0;
        let mut inner_log = 0;
        slot->[outer](outer_log)->[inner](inner_log) += 2;
        (slot, outer_log, inner_log)
    "# });

    assert_val_eq!(value, expected_tuple([int(7), int(12), int(34)]));
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
    let effects = module
        .get_function_by_id(expr)
        .unwrap()
        .definition
        .ty_scheme
        .ty
        .effects
        .clone();
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
fn yielded_generic_frame_keeps_evidence_across_module_calls() {
    let mut session = experimental_session();
    session
        .try_compile_module(
            "access",
            "pub fn relay<T>(value: T) -> T where T: Value { value }",
        )
        .unwrap();
    assert_val_eq!(
        session.run(indoc! { r#"
            subscript cell<T>(slot: &mut T) -> T where T: Value {
                mut {
                    let mut local = slot;
                    yield local;
                    slot = local
                }
            }
            fn replace<T>(slot: &mut T, value: T) where T: Value {
                let unrelated = access::relay((42, true));
                slot = value
            }
            let mut slot = "before";
            replace(slot->[cell], "after");
            slot
        "# }),
        string("after")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn members_of_a_subscript_have_one_signature() {
    // The members are bodies of one signature, also when neither names the other: an argument
    // that the signature leaves to infer has one type for both.
    experimental_session()
        .fail_compilation(indoc! { r#"
            subscript cell(slot: &mut int, key) -> int {
                ref {
                    let offset: int = key;
                    let local = slot + offset;
                    yield local
                }

                mut {
                    let name: string = key;
                    let mut local = slot;
                    yield local;
                    slot = local
                }
            }

            let mut slot = 1;
            slot->[cell](5)
        "# })
        .expect_type_mismatch("int", "string");
}

/// A subscript whose `ref` member needs trait `A` and whose `mut` member needs trait `B`, each
/// performing the output effect of its trait, with `A` fallible and `B` pure for `string`,
/// followed by `uses`.
fn subscript_of_members_with_different_requirements(uses: &str) -> String {
    let declarations = indoc! { r#"
        trait A<Self |-> ! E> { fn run_a(x: Self) -> int ! E; }
        trait B<Self |-> ! E> { fn run_b(x: Self) -> int ! E; }
        impl A for <Self = string |-> ! E = fallible> {
            fn run_a(x) { idiv(6, string_len(x)) }
        }
        impl B for <Self = string |-> ! E = ()> {
            fn run_b(x) { string_len(x) }
        }

        subscript cell<T>(slot: &mut int, key: T) -> int {
            ref {
                let local = slot + run_a(key);
                yield local
            }

            mut {
                let mut local = slot + run_b(key);
                yield local;
                slot = local
            }
        }

        fn read() -> int {
            let accessor = cell;
            let mut slot = 1;
            slot->[accessor]("ab")
        }

        fn write() -> int {
            let accessor = cell;
            let mut slot = 1;
            slot->[accessor]("ab") += 10;
            slot
        }

        fn pure_only(f: () -> int ! ()) -> int { f() }
    "# };
    format!("{declarations}{uses}")
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_subscript_value_gives_each_member_its_evidence_and_its_effect() {
    // The value holds the evidence of the one signature, which both members take.
    let source = subscript_of_members_with_different_requirements("(read(), pure_only(write))");
    assert_val_eq!(
        run_experimental_subscript_source(&source),
        expected_tuple([int(4), int(13)])
    );

    let source = subscript_of_members_with_different_requirements("pure_only(read)");
    experimental_session()
        .fail_compilation(&source)
        .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_use_of_a_subscript_inside_its_group_has_the_types_of_the_group() {
    // While the bodies of a subscript are inferred, a use of the subscript by them, or by a
    // function that they name, has their types: an argument left to infer is one type.
    experimental_session()
        .fail_compilation(indoc! { r#"
            subscript cell(slot: &mut int, key, depth: int) -> int {
                ref {
                    let local = if depth == 0 {
                        let offset: int = key;
                        slot + offset
                    } else {
                        let accessor = cell;
                        slot->[accessor]("text", depth - 1)
                    };
                    yield local
                }
            }

            let mut slot = 21;
            slot->[cell](2, 1)
        "# })
        .expect_type_mismatch("string", "int");

    experimental_session()
        .fail_compilation(indoc! { r#"
            fn read(slot: &mut int) -> int {
                let accessor = cell;
                slot->[accessor]("text", 0)
            }

            subscript cell(slot: &mut int, key, depth: int) -> int {
                ref {
                    let local = if depth == 0 {
                        let offset: int = key;
                        slot + offset
                    } else {
                        read(slot)
                    };
                    yield local
                }
            }

            let mut slot = 21;
            slot->[cell](2, 1)
        "# })
        .expect_type_mismatch("string", "int");

    // The same for a subscript named as a field, whose result is left to infer.
    experimental_session()
        .fail_compilation(indoc! { r#"
            fn read(secret: Secret) -> int {
                string_len(secret.value)
            }

            #[private_repr]
            struct Secret {
                raw: int,
                depth: int,
            }

            subscript Secret.value(self) {
                ref {
                    let local = if self.depth == 0 {
                        self.raw
                    } else {
                        read(Secret { raw: self.raw, depth: 0 })
                    };
                    yield local
                }
            }

            let secret = Secret { raw: 21, depth: 1 };
            secret.value
        "# })
        .expect_type_mismatch("int", "string");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_subscript_value_inside_its_group_holds_the_evidence_of_its_members() {
    // The value of a subscript taken by its own bodies, or by a function that they name, holds
    // what the bodies require, found once the group is final.
    let traits = indoc! { r#"
        trait A<Self |-> ! E> { fn run_a(x: Self) -> int ! E; }
        impl A for <Self = string |-> ! E = fallible> {
            fn run_a(x) { idiv(6, string_len(x)) }
        }
        impl A for <Self = int |-> ! E = ()> {
            fn run_a(x) { x }
        }
        fn pure_only(f: () -> int ! ()) -> int { f() }
    "# };
    let by_itself = indoc! { r#"
        subscript cell<T>(slot: &mut int, key: T, depth: int) -> int {
            ref {
                let local = if depth == 0 {
                    slot + run_a(key)
                } else {
                    let accessor = cell;
                    slot->[accessor](key, depth - 1)
                };
                yield local
            }

            mut {
                let mut local = if depth == 0 {
                    slot + run_a(key)
                } else {
                    let accessor = cell;
                    slot->[accessor](key, depth - 1)
                };
                yield local;
                slot = local
            }
        }

        fn read_string() -> int {
            let mut slot = 1;
            slot->[cell]("ab", 2)
        }

        fn read_int() -> int {
            let mut slot = 1;
            slot->[cell](5, 2)
        }

        fn write_int() -> int {
            let mut slot = 1;
            slot->[cell](5, 2) += 10;
            slot
        }
    "# };
    let source = format!("{traits}{by_itself}(read_string(), pure_only(read_int), write_int())");
    assert_val_eq!(
        run_experimental_subscript_source(&source),
        expected_tuple([int(4), int(6), int(16)])
    );
    experimental_session()
        .fail_compilation(&format!("{traits}{by_itself}pure_only(read_string)"))
        .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());

    let through_two_functions = indoc! { r#"
        fn take<T>(slot: &mut int, key: T, depth: int) -> int {
            let accessor = cell;
            slot->[accessor](key, depth)
        }

        fn step<T>(slot: &mut int, key: T, depth: int) -> int {
            if depth == 0 {
                slot + run_a(key)
            } else {
                take(slot, key, depth - 1)
            }
        }

        subscript cell<T>(slot: &mut int, key: T, depth: int) -> int {
            ref {
                let local = step(slot, key, depth);
                yield local
            }
        }

        fn read_string() -> int {
            let mut slot = 1;
            slot->[cell]("ab", 2)
        }

        fn read_int() -> int {
            let mut slot = 1;
            take(slot, 5, 2)
        }
    "# };
    let source = format!("{traits}{through_two_functions}(read_string(), pure_only(read_int))");
    assert_val_eq!(
        run_experimental_subscript_source(&source),
        expected_tuple([int(4), int(6)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_use_of_a_subscript_inside_its_group_has_effects_of_its_own() {
    // A recursive subscript behaves, for effects, as its unrolling, as a recursive function:
    // the pure callback that a body gives to the subscript does not make the callback of the
    // subscript pure, whichever body does it, in whichever order, by name or through a value.
    let pure_only = "fn pure_only(f: () -> int ! ()) -> int { f() }\n";
    let uses = indoc! { r#"
        fn read_fallible() -> int {
            let mut slot = 1;
            slot->[cell](|| idiv(6, 2), 2)
        }

        fn write_fallible() -> int {
            let mut slot = 1;
            slot->[cell](|| idiv(6, 2), 2) += 10;
            slot
        }

        fn read_pure() -> int {
            let mut slot = 1;
            slot->[cell](|| 4, 2)
        }
    "# };
    let by_name = "slot->[cell](|| 1, depth - 1)";
    let by_value = "let accessor = cell; slot->[accessor](callback, depth - 1)";
    let plain = "slot + callback()";
    let recursive = |step: &str| format!("if depth == 0 {{ slot + callback() }} else {{ {step} }}");
    for (reading, writing, expected) in [
        (recursive(by_name), plain.to_string(), [2, 14, 2]),
        (plain.to_string(), recursive(by_name), [4, 12, 5]),
        (recursive(by_name), recursive(by_value), [2, 12, 2]),
        (recursive(by_value), recursive(by_name), [4, 12, 5]),
    ] {
        let ref_body = format!("ref {{ let local = {reading}; yield local }}");
        let mut_body = format!("mut {{ let mut local = {writing}; yield local; slot = local }}");
        for bodies in [
            format!("{ref_body}\n{mut_body}"),
            format!("{mut_body}\n{ref_body}"),
        ] {
            let subscript = format!(
                "subscript cell(slot: &mut int, callback, depth: int) -> int {{\n{bodies}\n}}\n"
            );
            let source = format!(
                "{pure_only}{subscript}{uses}(read_fallible(), write_fallible(), pure_only(read_pure))"
            );
            assert_val_eq!(
                run_experimental_subscript_source(&source),
                expected_tuple(expected.map(int))
            );
            experimental_session()
                .fail_compilation(&format!(
                    "{pure_only}{subscript}{uses}pure_only(read_fallible)"
                ))
                .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
        }
    }

    // A callback that a body needs pure is pure for the subscript.
    experimental_session()
        .fail_compilation(&format!(
            "{pure_only}{}{uses}read_fallible()",
            indoc! { r#"
                subscript cell(slot: &mut int, callback, depth: int) -> int {
                    ref {
                        let local = if depth == 0 {
                            slot + pure_only(callback)
                        } else {
                            slot->[cell](|| 1, depth - 1)
                        };
                        yield local
                    }

                    mut {
                        let mut local = slot + callback();
                        yield local;
                        slot = local
                    }
                }
            "# }
        ))
        .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn the_bodies_of_a_recursive_subscript_have_one_set_of_requirements_and_each_its_effect() {
    // The bodies of a subscript are one definition: what one requires, all require, in one
    // order, so that a value of the subscript gives each body its evidence. Each body performs
    // its own effect: here reading performs that of `A`, and writing that of `B`.
    let source = indoc! { r#"
        trait A<Self |-> ! E> { fn run_a(x: Self) -> int ! E; }
        impl A for <Self = string |-> ! E = fallible> {
            fn run_a(x) { idiv(6, string_len(x)) }
        }
        impl A for <Self = int |-> ! E = ()> {
            fn run_a(x) { x }
        }
        trait B<Self |-> ! E> { fn run_b(x: Self) -> int ! E; }
        impl B for <Self = string |-> ! E = ()> {
            fn run_b(x) { string_len(x) }
        }
        impl B for <Self = int |-> ! E = fallible> {
            fn run_b(x) { idiv(12, x) }
        }
        fn pure_only(f: () -> int ! ()) -> int { f() }

        subscript cell<T, U>(slot: &mut int, a: T, b: U, depth: int) -> int {
            ref {
                let local = if depth == 0 {
                    slot + run_a(a)
                } else {
                    slot->[cell](a, b, depth - 1)
                };
                yield local
            }

            mut {
                let mut local = if depth == 0 {
                    slot + run_b(b)
                } else {
                    100
                };
                if depth > 0 {
                    slot->[cell](a, b, depth - 1) += 1000
                };
                yield local;
                slot = slot + local
            }
        }

        fn read(a, b) -> int {
            let mut slot = 1;
            slot->[cell](a, b, 2)
        }

        fn write(a, b) -> int {
            let mut slot = 1;
            slot->[cell](a, b, 2) += 10;
            slot
        }

        fn by_value(a, b) -> int {
            let accessor = cell;
            let mut slot = 1;
            slot->[accessor](a, b, 1) += 7;
            slot->[accessor](a, b, 1)
        }

        fn read_ints() -> int { read(3, 4) }
        fn read_string_int() -> int { read("ab", 4) }
        fn write_ints() -> int { write(3, 4) }
        fn write_strings() -> int { write("ab", "abc") }
    "# };
    assert_val_eq!(
        run_experimental_subscript_source(&format!(
            "{source}(read_string_int(), pure_only(read_ints), write_ints(), pure_only(write_strings), by_value(\"ab\", \"abc\"), by_value(3, 4))"
        )),
        expected_tuple([4, 4, 2215, 2215, 1115, 1115].map(int))
    );
    for impure in ["read_string_int", "write_ints"] {
        experimental_session()
            .fail_compilation(&format!("{source}pure_only({impure})"))
            .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_recursive_subscript_whose_contracts_do_not_settle_is_refused() {
    // As a recursive function: each round of the recursion needs `Tr` at the effect that the
    // round before gave, so no signature is found, and a written one is accepted.
    let prelude = indoc! { r#"
        struct Pair<A, B>(A, B)
        trait Tr<Self |-> ! Out> { fn tr(x: Self) -> int ! Out; }
        impl<T, ! E> Tr for <Self = Pair<T, (() -> int ! E)> |-> ! Out = E> {
            fn tr(x) { (x.1)() + 1 }
        }
        fn step<T, ! E, O>(x: T, g: () -> int ! E) -> (() -> int ! O)
        where Pair<T, (() -> int ! E)>: Tr<! Out = O> { || tr(Pair(x, g)) }
        fn pure_only(f: () -> int ! ()) -> int { f() }
    "# };
    let bodies = |base: &str| {
        format!(
            "{{
                ref {{
                    let local = if n == 0 {{ {base} }} else {{ slot->[f](x, step(x, g), n - 1) }};
                    yield local
                }}

                mut {{
                    let mut local = if n == 0 {{ {base} }} else {{ slot->[f](x, step(x, g), n - 1) }};
                    yield local;
                    slot = local
                }}
            }}\n"
        )
    };
    experimental_session()
        .fail_compilation(&format!(
            "{prelude}subscript f<T>(slot: &mut int, x: T, g, n: int) -> int {}0",
            bodies("0")
        ))
        .expect_recursive_group_does_not_settle("f", "Pair<T, ");
    let written = "subscript f<T, ! E>(slot: &mut int, x: T, g: () -> int ! E, n: int) -> int\nwhere Pair<T, (() -> int ! E)>: Tr<! Out = E> ";
    let uses = indoc! { r#"
        fn read() -> int {
            let mut slot = 0;
            slot->[f](1, || 10, 3)
        }

        fn write() -> int {
            let mut slot = 0;
            slot->[f](1, || idiv(10, 2), 3) += 1;
            slot
        }

        (pure_only(read), write())
    "# };
    assert_val_eq!(
        run_experimental_subscript_source(&format!("{prelude}{written}{}{uses}", bodies("g()"))),
        expected_tuple([int(13), int(9)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_function_of_the_group_of_a_subscript_reads_it_as_a_field() {
    // The types of a group are known before its effects are inferred, so a function of the
    // group that reads the field of an argument left to infer finds the subscript.
    let value = run_experimental_subscript_source(indoc! { r#"
        trait A<Self |-> ! E> { fn run_a(x: Self) -> int ! E; }
        impl A for <Self = string |-> ! E = fallible> {
            fn run_a(x) { idiv(6, string_len(x)) }
        }
        impl A for <Self = int |-> ! E = ()> {
            fn run_a(x) { x }
        }
        fn pure_only(f: () -> int ! ()) -> int { f() }

        fn get(x) {
            x.value
        }

        #[private_repr]
        struct Secret<T> {
            raw: T,
            depth: int,
        }

        fn read<T>(secret: Secret<T>) -> int {
            get(secret)
        }

        subscript Secret<T>.value(self) -> int {
            ref {
                let local = if self.depth == 0 {
                    run_a(self.raw)
                } else {
                    read(Secret { raw: self.raw, depth: self.depth - 1 })
                };
                yield local
            }
        }

        fn of_string() -> int { Secret { raw: "ab", depth: 2 }.value }
        fn of_int() -> int { Secret { raw: 7, depth: 2 }.value }
        (of_string(), pure_only(of_int))
    "# });
    assert_val_eq!(value, expected_tuple([int(3), int(7)]));
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
fn read_only_subscript_coercions_preserve_argument_variance() {
    for accessor in ["first", "black_box(first)"] {
        let source = format!(
            "subscript first(slot: (int, () -> int ! fallible)) -> int {{
                 ref {{ let result = slot.0; yield result }}
             }}
             fn answer() -> int {{ 42 }}
             fn read_with(accessor) -> (int, int) {{
                 let mut slot = (7, answer);
                 let observed = slot->[accessor];
                 (observed, slot.1())
             }}
             let accessor = {accessor};
             read_with(accessor)"
        );
        assert_val_eq!(
            run_experimental_subscript_source(&source),
            expected_tuple([int(7), int(42)])
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mutable_subscript_result_cannot_widen_stored_callback() {
    let source = indoc! { r#"
        fn diverge() { loop {} }
        fn answer() -> int { 42 }
        subscript cell(slot: &mut int) {
            mut {
                let mut callback = diverge;
                yield callback;
                slot = 1;
            }
        }
        fn replace_with(accessor, slot: &mut int) {
            slot->[accessor] = answer;
        }
        let mut slot = 0;
        replace_with(cell, slot);
        slot
    "# };
    let error = experimental_session().fail_compilation(source);
    assert!(matches!(
        error.into_inner(),
        CompilationErrorImpl::TypeMismatch { .. }
    ));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mutable_subscript_result_preserves_callback_effects() {
    let source = indoc! { r#"
        type Pure = () -> int;
        struct Slot(Pure)
        fn answer() -> int { 42 }
        fn fail() -> int { abort() }
        subscript cell(slot: &mut Slot) -> Pure {
            ref mut { slot.0 }
        }
        fn replace_with(accessor, slot: &mut Slot) {
            slot->[accessor] = fail;
        }
        let mut slot = Slot(answer);
        replace_with(cell, slot);
        ()
    "# };
    // This is a typing rejection, not a failure while invoking the callback.
    experimental_session()
        .try_compile(source)
        .expect_err("a mutable result cannot widen stored callback effects")
        .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn subscript_result_widening_can_discard_mutable_access() {
    let source = indoc! { r#"
        type Pure = () -> int;
        type Fallible = () -> int ! fallible;
        struct Slot(Pure)
        fn answer() -> int { 42 }
        subscript cell(slot: &mut Slot) -> Pure {
            ref mut { slot.0 }
        }
        fn read_with(accessor, slot: &mut Slot) -> Fallible {
            slot->[accessor]
        }
        let mut slot = Slot(answer);
        let callback = read_with(cell, slot);
        callback()
    "# };
    assert_val_eq!(run_experimental_subscript_source(source), int(42));
    let source = indoc! { r#"
        fn diverge() { loop {} }
        subscript cell(slot: &mut int) {
            ref mut {
                let mut callback = diverge;
                yield callback;
                slot = 1;
            }
        }
        fn read_with(accessor, slot: &mut int) -> () -> int {
            slot->[accessor]
        }
        let mut slot = 0;
        let callback = read_with(cell, slot);
        slot
    "# };
    assert_val_eq!(run_experimental_subscript_source(source), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mutable_subscript_result_replaces_matching_callback_types() {
    for body in [
        "ref mut { slot.0 }",
        "mut { let mut callback = slot.0; yield callback; slot.0 = callback; }",
    ] {
        for accessor in ["cell", "black_box(cell)"] {
            let source = format!(
                "type Pure = () -> int;
                 struct Slot(Pure)
                 fn answer() -> int {{ 42 }}
                 fn replacement() -> int {{ 43 }}
                 subscript cell(slot: &mut Slot) -> Pure {{ {body} }}
                 fn replace_with(accessor, slot: &mut Slot) {{
                     slot->[accessor] = replacement;
                 }}
                 let mut slot = Slot(answer);
                 replace_with({accessor}, slot);
                 (slot.0)()"
            );
            assert_val_eq!(run_experimental_subscript_source(&source), int(43));
        }
    }
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
fn generic_first_class_subscript_in_same_module() {
    let subscript = indoc! { r#"
        subscript cell<T>(value: &mut T) -> T where T: Value {
            ref { let local = value; yield local; }
            mut { let mut local = value; yield local; value = local; }
        }
    "# };
    let caller = indoc! { r#"
        fn set<T>(value: &mut T, replacement: T) {
            let accessor = cell;
            let copied = accessor;
            value->[copied] = replacement;
        }
    "# };
    for declarations in [
        format!("{subscript}{caller}"),
        format!("{caller}{subscript}"),
    ] {
        let source = format!(
            "{declarations}
             fn compute() {{
                 let mut number = 1; set(number, 2);
                 let mut text = \"before\"; set(text, \"after\");
                 (number, text)
             }}
             compute()"
        );
        assert_val_eq!(
            run_experimental_subscript_source(&source),
            expected_tuple([int(2), string("after")])
        );
    }
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
fn generated_structural_projection_hir_captures_open_member_layout() {
    fn inspect_subscripts(arena: &ENodeArena, node: ENodeId, found: &mut Vec<String>) -> bool {
        match &arena[node].kind {
            NodeKind::BuildSubscriptValue(build) if !build.evidence_captures.is_empty() => true,
            NodeKind::BuildSubscriptValue(build) => {
                found.push(format!(
                    "build with {} captures",
                    build.evidence_captures.len()
                ));
                false
            }
            NodeKind::GetSubscript(get) => {
                found.push(format!(
                    "get with {} requirements",
                    get.inst_data.dicts_req.len()
                ));
                false
            }
            _ => crate::harness::hir_child_nodes(arena, node)
                .into_iter()
                .any(|child| inspect_subscripts(arena, child, found)),
        }
    }

    let mut session = TestSession::new();
    let module_id = session
        .compile(indoc! { r#"
            fn get_x<T>(record: T) { record.x }
            fn forward<A>(record: { x: A }) -> A { get_x(record) }
        "# })
        .module_id;
    let module = session.session().expect_fresh_module(module_id);
    let function = module
        .get_function(ustr("forward"))
        .expect("forward should be compiled");
    let entry = function.get_code_entry().expect("forward should have HIR");

    let mut found = Vec::new();
    assert!(
        inspect_subscripts(&module.hir_arena, entry, &mut found),
        "an open structural addressor should close over its member layout evidence: {found:?}; bindings: {:#?}",
        function.evidence_bindings,
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

        fn fail(target: &mut int) { target = [0][1] }
        testing::reset_tracked_drops();
        let mut slot = 5;
        fail(slot->[cell])
    "# };

    assert_eq!(
        session.fail_run(source),
        SourceFailureKind::Aborted(Some(
            "Array access out of bounds: index 1 for length 1".to_string()
        ))
    );
    assert_val_eq!(session.run("testing::tracked_drop_log()"), int(7));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_slide_error_unwinds_caller_owned_locals() {
    let mut session = experimental_session();
    session.allow_unsafe();
    let source = indoc! { r#"
        struct Probe(int)

        impl Value for Probe {
            fn eq(left: Probe, right: Probe) -> bool { left.0 == right.0 }
            fn to_string(value: Probe) -> string { to_string(value.0) }
            fn hash(value: Probe, state: &mut hasher) { hash(value.0, state) }
            fn clone(source: Probe) -> Probe { Probe(source.0) }
            fn drop(target: &mut Probe) { testing::record_tracked_drop(target.0) }
        }

        subscript cell(slot: &mut int) -> int {
            mut {
                let mut local = slot;
                yield local;
                slot = local;
                let ignored = [0][1];
            }
        }

        testing::reset_tracked_drops();
        let owned = Probe(7);
        let mut slot = 5;
        slot->[cell] = 9
    "# };

    assert_eq!(
        session.fail_run(source),
        SourceFailureKind::Aborted(Some(
            "Array access out of bounds: index 1 for length 1".to_string()
        ))
    );
    assert_val_eq!(session.run("testing::tracked_drop_log()"), int(7));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_slide_error_cleans_accessor_argument_temporaries() {
    let mut session = experimental_session();
    session.allow_unsafe();
    let source = indoc! { r#"
        struct Probe(int)

        impl Value for Probe {
            fn eq(left: Probe, right: Probe) -> bool { left.0 == right.0 }
            fn to_string(value: Probe) -> string { to_string(value.0) }
            fn hash(value: Probe, state: &mut hasher) { hash(value.0, state) }
            fn clone(source: Probe) -> Probe { Probe(source.0) }
            fn drop(target: &mut Probe) { testing::record_tracked_drop(target.0) }
        }

        subscript cell(slot: &mut int, marker: Probe) -> int {
            mut {
                let mut local = slot;
                yield local;
                let ignored = marker;
                let slide_error = [0][1];
            }
        }

        testing::reset_tracked_drops();
        let mut slot = 5;
        slot->[cell](Probe(7)) = 9
    "# };

    assert_eq!(
        session.fail_run(source),
        SourceFailureKind::Aborted(Some(
            "Array access out of bounds: index 1 for length 1".to_string()
        ))
    );
    assert_val_eq!(session.run("testing::tracked_drop_log()"), int(7));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_slide_error_during_unwind_poisons_without_outer_semantic_cleanup() {
    let mut session = experimental_session();
    session.allow_unsafe();
    let source = indoc! { r#"
        struct Probe(int)

        impl Value for Probe {
            fn eq(left: Probe, right: Probe) -> bool { left.0 == right.0 }
            fn to_string(value: Probe) -> string { to_string(value.0) }
            fn hash(value: Probe, state: &mut hasher) { hash(value.0, state) }
            fn clone(source: Probe) -> Probe { Probe(source.0) }
            fn drop(target: &mut Probe) { testing::record_tracked_drop(target.0) }
        }

        subscript cell(slot: &mut int) -> int {
            mut {
                let mut local = slot;
                yield local;
                slot = local;
                let slide_error = [0][1];
            }
        }

        fn fail(target: &mut int) { target = [0][2] }
        testing::reset_tracked_drops();
        let owned = Probe(7);
        let mut slot = 5;
        fail(slot->[cell])
    "# };

    // The body starts unwinding with index 2, then the accessor slide raises index 1. A second
    // failure during semantic unwind poisons the executor, retaining both causes and skipping
    // all remaining Ferlium cleanup.
    let error = session
        .try_run(source)
        .expect_err("the accessor body and slide must both fail");
    let failure = error
        .failure_during_cleanup()
        .expect("a second source failure during cleanup must be retained structurally");
    assert_eq!(
        failure.initial().kind(),
        SourceFailureKind::Aborted(Some(
            "Array access out of bounds: index 2 for length 1".to_string()
        ))
    );
    assert_eq!(
        failure.during_cleanup().kind(),
        SourceFailureKind::Aborted(Some(
            "Array access out of bounds: index 1 for length 1".to_string()
        ))
    );
    assert_val_eq!(session.run("testing::tracked_drop_log()"), int(0));
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
        SourceFailureKind::Aborted(Some(
            "Array access out of bounds: index 1 for length 1".to_string()
        ))
    );
    assert_val_eq!(session.run("testing::tracked_drop_log()"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_subscript_prologue_error_unwinds_caller_owned_locals() {
    let mut session = experimental_session();
    session.allow_unsafe();
    let source = indoc! { r#"
        struct Probe(int)

        impl Value for Probe {
            fn eq(left: Probe, right: Probe) -> bool { left.0 == right.0 }
            fn to_string(value: Probe) -> string { to_string(value.0) }
            fn hash(value: Probe, state: &mut hasher) { hash(value.0, state) }
            fn clone(source: Probe) -> Probe { Probe(source.0) }
            fn drop(target: &mut Probe) { testing::record_tracked_drop(target.0) }
        }

        subscript cell(slot: &mut int) -> int {
            mut {
                let ignored = [0][1];
                let mut local = slot;
                yield local;
                slot = local
            }
        }

        testing::reset_tracked_drops();
        let owned = Probe(7);
        let mut slot = 5;
        slot->[cell] = 9
    "# };

    assert_eq!(
        session.fail_run(source),
        SourceFailureKind::Aborted(Some(
            "Array access out of bounds: index 1 for length 1".to_string()
        ))
    );
    assert_val_eq!(session.run("testing::tracked_drop_log()"), int(7));
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

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_field_that_a_type_declares_as_a_subscript_is_a_use_of_that_subscript() {
    // A field of a type that declares a subscript for it is a use of the subscript, with its
    // requirements and its effects, also when the access is typed before its receiver: in a
    // function that is generic in the receiver, in one that calls it, or in a lambda.
    let declarations = indoc! { r#"
        trait A<Self |-> ! E> { fn run_a(x: Self) -> int ! E; }
        impl A for <Self = string |-> ! E = fallible> {
            fn run_a(x) { idiv(6, string_len(x)) }
        }
        impl A for <Self = int |-> ! E = ()> {
            fn run_a(x) { x }
        }
        fn pure_only(f: () -> int ! ()) -> int { f() }

        #[private_repr]
        struct Secret<T> {
            raw: T,
            total: int,
        }

        subscript Secret<T>.value(self) -> int {
            ref {
                let local = run_a(self.raw);
                yield local
            }

            mut {
                let mut local = run_a(self.raw);
                yield local;
                self.total = self.total + local
            }
        }

        fn get(x) { x.value }
        fn add(x, n: int) { x.value += n }
        fn through<U>(secret: Secret<U>) -> int { get(secret) }

        fn of_string() -> int { get(Secret { raw: "ab", total: 0 }) }
        fn of_int() -> int { get(Secret { raw: 7, total: 0 }) }
        fn through_string() -> int { through(Secret { raw: "ab", total: 0 }) }
        fn added_int() -> int {
            let mut secret = Secret { raw: 7, total: 1 };
            add(secret, 5);
            secret.total
        }
        fn added_string() -> int {
            let mut secret = Secret { raw: "abc", total: 1 };
            add(secret, 5);
            secret.total
        }
        fn in_lambda_string() -> int {
            let read = |x| x.value;
            read(Secret { raw: "ab", total: 0 })
        }
        fn in_lambda_int() -> int {
            let mut secret = Secret { raw: 7, total: 1 };
            let bump = |x, n| { x.value += n };
            bump(secret, 5);
            secret.total
        }
    "# };
    assert_val_eq!(
        run_experimental_subscript_source(&format!(
            "{declarations}(of_string(), pure_only(of_int), through_string(), pure_only(added_int), added_string(), in_lambda_string(), pure_only(in_lambda_int))"
        )),
        expected_tuple([3, 7, 3, 13, 8, 3, 13].map(int))
    );
    for fallible in [
        "of_string",
        "through_string",
        "added_string",
        "in_lambda_string",
    ] {
        experimental_session()
            .fail_compilation(&format!("{declarations}pure_only({fallible})"))
            .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
    }
    // What the subscript requires is required of the type of the receiver.
    for missing in [
        "get(Secret { raw: 1.5, total: 0 })",
        "through(Secret { raw: 1.5, total: 0 })",
        "{ let read = |x| x.value; read(Secret { raw: 1.5, total: 0 }) }",
    ] {
        experimental_session()
            .fail_compilation(&format!("{declarations}{missing}"))
            .expect_trait_impl_not_found("A", &["Self = float"]);
    }

    // The same for a type whose representation is a tuple.
    let value = run_experimental_subscript_source(indoc! { r#"
        #[private_repr]
        struct Pair(int, int)

        subscript Pair.sum(self) -> int {
            ref {
                let local = self.0 + self.1;
                yield local
            }
        }

        fn get(x) { x.sum }
        fn in_lambda() -> int {
            let read = |x| x.sum;
            read(Pair(3, 4))
        }
        (get(Pair(1, 2)), in_lambda())
    "# });
    assert_val_eq!(value, expected_tuple([int(3), int(7)]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_field_read_inside_the_group_of_its_subscript_is_a_reference_of_the_group() {
    // A function of the group of a subscript reads its field in a lambda, where the access is
    // typed before its receiver: the read is a reference to the subscript as one by name is,
    // with effects of its own, and the function requires what the subscript requires.
    let declarations = indoc! { r#"
        trait A<Self |-> ! E> { fn run_a(x: Self) -> int ! E; }
        impl A for <Self = string |-> ! E = fallible> {
            fn run_a(x) { idiv(6, string_len(x)) }
        }
        impl A for <Self = int |-> ! E = ()> {
            fn run_a(x) { x }
        }
        fn pure_only(f: () -> int ! ()) -> int { f() }

        #[private_repr]
        struct Secret<T> {
            raw: T,
            depth: int,
        }

        fn read<T>(secret: Secret<T>) -> int {
            let field = |x| x.value;
            field(secret)
        }

        subscript Secret<T>.value(self) -> int {
            ref {
                let local = if self.depth == 0 {
                    run_a(self.raw)
                } else {
                    read(Secret { raw: self.raw, depth: self.depth - 1 })
                };
                yield local
            }
        }

        fn of_string() -> int { Secret { raw: "ab", depth: 2 }.value }
        fn of_int() -> int { Secret { raw: 7, depth: 2 }.value }
    "# };
    assert_val_eq!(
        run_experimental_subscript_source(&format!(
            "{declarations}(of_string(), pure_only(of_int))"
        )),
        expected_tuple([int(3), int(7)])
    );
    experimental_session()
        .fail_compilation(&format!("{declarations}pure_only(of_string)"))
        .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());

    // Each access is a reference of the function that makes it: two functions of the group
    // that read the field, one of them twice, each require what the subscript requires,
    // whatever the order of the definitions.
    let prelude = indoc! { r#"
        trait A<Self |-> ! E> { fn run_a(x: Self) -> int ! E; }
        impl A for <Self = string |-> ! E = fallible> {
            fn run_a(x) { idiv(6, string_len(x)) }
        }
        impl A for <Self = int |-> ! E = ()> {
            fn run_a(x) { x }
        }
        fn pure_only(f: () -> int ! ()) -> int { f() }

        #[private_repr]
        struct Secret<T> {
            raw: T,
            depth: int,
        }
    "# };
    let read1 = indoc! { r#"
        fn read1<T>(secret: Secret<T>) -> int {
            let field = |x| x.value;
            field(secret)
        }
    "# };
    let read2 = indoc! { r#"
        fn read2<T>(secret: Secret<T>) -> int {
            let field = |x| x.value;
            let again = |x| x.value;
            field(secret) + again(Secret { raw: secret.raw, depth: 0 })
        }
    "# };
    let subscript = indoc! { r#"
        subscript Secret<T>.value(self) -> int {
            ref {
                let local = if self.depth == 0 {
                    run_a(self.raw)
                } else if self.depth == 1 {
                    read1(Secret { raw: self.raw, depth: 0 })
                } else {
                    read2(Secret { raw: self.raw, depth: self.depth - 1 })
                };
                yield local
            }
        }
    "# };
    for items in [
        [read1, read2, subscript],
        [read2, read1, subscript],
        [subscript, read1, read2],
        [subscript, read2, read1],
        [read1, subscript, read2],
        [read2, subscript, read1],
    ] {
        let items = items.concat();
        assert_val_eq!(
            run_experimental_subscript_source(&format!(
                "{prelude}{items}(read2(Secret {{ raw: \"ab\", depth: 2 }}), pure_only(|| read1(Secret {{ raw: 7, depth: 3 }})))"
            )),
            expected_tuple([int(9), int(21)]),
            "{items}"
        );
        assert!(
            matches!(
                experimental_session()
                    .fail_compilation(&format!(
                        "{prelude}{items}pure_only(|| read1(Secret {{ raw: \"ab\", depth: 3 }}))"
                    ))
                    .into_inner(),
                CompilationErrorImpl::TraitImplOutputEffectsMismatch { .. }
            ),
            "{items}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_declared_field_typed_before_its_receiver_is_an_instance_of_its_subscript() {
    // An access typed before its receiver is an instance of the subscript that the type
    // declares: a generic that the types of the receiver and of the result do not name is an
    // output of what the subscript requires. Here the type of the field is such an output.
    let declarations = indoc! { r#"
        trait Read<Self |-> Out> { fn read(x: Self) -> Out; }
        impl Read for <Self = int |-> Out = string> {
            fn read(x) { "hello" }
        }
        impl Read for <Self = bool |-> Out = int> {
            fn read(x) { 42 }
        }

        #[private_repr]
        struct Box<T>(T)

        subscript Box<T>.value(self) -> _ {
            ref {
                let local = read(self.0);
                yield local
            }
        }

        fn get(x) { x.value }
        fn through(b) { get(b) }
        fn generic<T, O>(b: Box<T>) -> O where T: Read<Out = O> {
            let field = |x| x.value;
            field(b)
        }
        fn in_lambdas() {
            let of_int = |x| x.value;
            let of_bool = |x| x.value;
            (of_int(Box(4)), of_bool(Box(true)))
        }
    "# };
    assert_val_eq!(
        run_experimental_subscript_source(&format!(
            "{declarations}(in_lambdas(), get(Box(4)), get(Box(true)), generic(Box(4)), generic(Box(true)), through(Box(4)))"
        )),
        expected_tuple([
            expected_tuple([string("hello"), int(42)]),
            string("hello"),
            int(42),
            string("hello"),
            int(42),
            string("hello"),
        ])
    );
    experimental_session()
        .fail_compilation(&format!(
            "{declarations}{{ let field = |x| x.value; field(Box(1.5)) }}"
        ))
        .expect_trait_impl_not_found("Read", &["Self = float"]);

    // An effect that only what the subscript requires names is an output too: here the
    // effect of the callback that the body gives to `use_it`.
    let declarations = indoc! { r#"
        trait Run<Self |-> ! E> { fn run(x: Self) -> int ! E; }
        impl Run for <Self = string |-> ! E = fallible> {
            fn run(x) { idiv(6, string_len(x)) }
        }
        impl Run for <Self = int |-> ! E = ()> {
            fn run(x) { x }
        }
        trait Use<Self |-> ! F> { fn use_it(x: Self) -> int ! F; }
        struct Pair<T, U>(T, U)
        impl<T, ! E> Use for <Self = Pair<T, (() -> int ! E)> |-> ! F = E>
        where T: Run<! E = E> {
            fn use_it(x) { x.1() }
        }
        fn pure_only(f: () -> int ! ()) -> int { f() }

        #[private_repr]
        struct Box<T>(T)

        subscript Box<T>.value(self) -> int {
            ref {
                let callback = || run(self.0);
                let local = use_it(Pair(self.0, callback));
                yield local
            }
        }

        fn of_string() -> int {
            let field = |x| x.value;
            field(Box("ab"))
        }
        fn of_int() -> int {
            let field = |x| x.value;
            field(Box(7))
        }
        fn generic<T, ! E>(b: Box<T>) -> int where T: Run<! E = E> {
            let field = |x| x.value;
            field(b)
        }
    "# };
    assert_val_eq!(
        run_experimental_subscript_source(&format!(
            "{declarations}(of_string(), pure_only(of_int), generic(Box(\"ab\")), pure_only(|| generic(Box(7))))"
        )),
        expected_tuple([3, 7, 3, 7].map(int))
    );
    experimental_session()
        .fail_compilation(&format!("{declarations}pure_only(of_string)"))
        .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_declared_field_is_the_same_whenever_its_receiver_is_known() {
    // An access typed before its receiver follows the rule of one typed after it: the
    // subscript that the type declares for the field, for a type that stores fields and for
    // one that stores none.
    let value = run_experimental_subscript_source(indoc! { r#"
        #[private_repr]
        struct Secret {
            raw: int,
        }

        subscript Secret.value(self) -> int {
            ref {
                let local = self.raw + 1;
                yield local
            }

            mut {
                let mut local = self.raw + 1;
                yield local;
                self.raw = local * 10
            }
        }

        fn get(x) { x.value }
        fn set(x: &mut _) { x.value = 7 }

        fn all() -> (int, int, int, int) {
            let mut secret = Secret { raw: 4 };
            let before = get(secret);
            set(secret);
            let read = |x| x.value;
            (before, read(secret), get(secret), secret.value)
        }
        all()
    "# });
    assert_val_eq!(value, expected_tuple([5, 71, 71, 71].map(int)));

    let value = run_experimental_subscript_source(indoc! { r#"
        enum Choice {
            Default,
            Given(int),
        }

        subscript Choice.value(self) -> int {
            ref {
                let local = match self {
                    Default => 7,
                    Given(n) => n,
                };
                yield local
            }
        }

        fn get(x) { x.value }

        fn all() -> (int, int, int) {
            let read = |x| x.value;
            (read(Choice::Given(3)), get(Choice::Default), Choice::Given(1).value)
        }
        all()
    "# });
    assert_val_eq!(value, expected_tuple([3, 7, 1].map(int)));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_implementation_that_reads_a_declared_field_requires_what_its_subscript_requires() {
    // An implementation for any type that has the field applies to a type that declares it
    // as a subscript when what the subscript requires holds, effects included.
    let declarations = indoc! { r#"
        trait A<Self |-> ! E> { fn run_a(x: Self) -> int ! E; }
        impl A for <Self = string |-> ! E = fallible> {
            fn run_a(x) { idiv(6, string_len(x)) }
        }
        impl A for <Self = int |-> ! E = ()> {
            fn run_a(x) { x }
        }

        #[private_repr]
        struct Secret<T> {
            raw: T,
        }

        subscript Secret<T>.value(self) -> int {
            ref {
                let local = run_a(self.raw);
                yield local
            }
        }

        trait Show<Self> { fn show(x: Self) -> int; }
        struct Wrapper<T>(T)
        impl<T> Show for Wrapper<T> {
            fn show(x) { x.0.value }
        }

        fn generic<T>(x: T) -> int { show(Wrapper(Secret { raw: x })) }
    "# };
    assert_val_eq!(
        run_experimental_subscript_source(&format!(
            "{declarations}(show(Wrapper(Secret {{ raw: 7 }})), generic(5))"
        )),
        expected_tuple([int(7), int(5)])
    );
    for missing in ["show(Wrapper(Secret { raw: 1.5 }))", "generic(1.5)"] {
        experimental_session()
            .fail_compilation(&format!("{declarations}{missing}"))
            .expect_trait_impl_not_found("Show", &["Self = Wrapper<Secret<float>>"]);
    }
    // `show` is pure, and reading the field of a `Secret<string>` is not.
    assert!(matches!(
        experimental_session()
            .fail_compilation(&format!(
                "{declarations}show(Wrapper(Secret {{ raw: \"ab\" }}))"
            ))
            .into_inner(),
        CompilationErrorImpl::TraitImplEffectsMismatch { .. }
    ));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_declared_field_of_a_generic_receiver_keeps_the_instance_of_its_use() {
    // What the subscript requires of a generic of the function that reads the field is given
    // to that function, and an output of it is known from there only: here `Out`, which the
    // types of the access do not name. The use keeps the instance that inference made.
    let declarations = |body: &str| {
        formatdoc! { r#"
            trait Read<Self |-> Out> {{ fn read(x: Self) -> Out; }}
            impl Read for <Self = int |-> Out = string> {{
                fn read(x) {{ "hello" }}
            }}
            impl Read for <Self = bool |-> Out = int> {{
                fn read(x) {{ 42 }}
            }}

            #[private_repr]
            struct Box<T>(T)

            subscript Box<T>.value(self) -> string {{
                ref {{
                    let local = to_string(read(self.0));
                    yield local
                }}
            }}

            fn get(x) {{ x.value }}

            fn generic<T>(b: Box<T>) -> string {{
                {body}
            }}

            (generic(Box(4)), generic(Box(true)))
        "# }
    };
    for body in [
        "b.value",
        "let field = |x| x.value; field(b)",
        "get(b)",
        "let field = |x| x.value; let twice = |x| field(x); twice(b)",
    ] {
        assert_val_eq!(
            run_experimental_subscript_source(&declarations(body)),
            expected_tuple([string("hello"), string("42")]),
            "{body}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_declared_field_of_a_generic_receiver_requires_and_writes_as_a_use_by_name() {
    // A subscript that reads a declared field of its generic requires what that field
    // requires, and so on: each use keeps its instance, also the one that another use makes.
    let nested = |body: &str| {
        formatdoc! { r#"
            trait Read<Self |-> Out> {{ fn read(x: Self) -> Out; }}
            impl Read for <Self = int |-> Out = string> {{
                fn read(x) {{ "hello" }}
            }}
            impl Read for <Self = bool |-> Out = int> {{
                fn read(x) {{ 42 }}
            }}

            #[private_repr]
            struct Box<T>(T)
            subscript Box<T>.value(self) -> string {{
                ref {{
                    let local = to_string(read(self.0));
                    yield local
                }}
            }}

            #[private_repr]
            struct Outer<T>(T)
            subscript Outer<T>.value(self) -> string {{
                ref {{
                    let local = string_concat("<", self.0.value);
                    yield local
                }}
            }}

            fn get(x) {{ x.value }}

            {body}

            (generic(Outer(Box(4))), generic(Outer(Box(true))))
        "# }
    };
    for body in [
        "fn generic<U>(o: Outer<Box<U>>) -> string { o.value }",
        "fn generic<U>(o: Outer<Box<U>>) -> string { let field = |x| x.value; field(o) }",
        "fn generic<U>(o: Outer<Box<U>>) -> string { get(o) }",
        "fn generic<U>(o: Outer<U>) -> string { let field = |x| x.value; field(o) }",
    ] {
        assert_val_eq!(
            run_experimental_subscript_source(&nested(body)),
            expected_tuple([string("<hello"), string("<42")]),
            "{body}"
        );
    }

    // The body that writes requires `Scale` of the generic of the function.
    let value = run_experimental_subscript_source(indoc! { r#"
        trait Scale<Self> { fn scale(x: Self) -> int; }
        impl Scale for int {
            fn scale(x) { 10 }
        }
        impl Scale for bool {
            fn scale(x) { 100 }
        }

        #[private_repr]
        struct Cell<T> {
            raw: int,
            tag: T,
        }

        subscript Cell<T>.value(self) -> int {
            ref {
                let local = self.raw;
                yield local
            }

            mut {
                let mut local = self.raw;
                yield local;
                self.raw = local * scale(self.tag)
            }
        }

        fn set(x: &mut _) { x.value = 7 }

        fn generic<T>(tag: T) -> (int, int) {
            let mut cell = Cell { raw: 1, tag };
            let before = cell.value;
            set(cell);
            let read = |x| x.value;
            (before, read(cell))
        }

        (generic(1), generic(true))
    "# });
    assert_val_eq!(
        value,
        expected_tuple([
            expected_tuple([int(1), int(70)]),
            expected_tuple([int(1), int(700)]),
        ])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_implementation_outputs_the_type_of_a_declared_field() {
    // The type of the field is here an output of what its subscript requires, known once
    // that is solved: the output of the implementation follows it.
    let declarations = indoc! { r#"
        trait Read<Self |-> Out> { fn read(x: Self) -> Out; }
        impl Read for <Self = int |-> Out = string> {
            fn read(x) { "hello" }
        }
        impl Read for <Self = bool |-> Out = (int) -> int> {
            fn read(x) {
                |y| if x {
                    y
                } else {
                    0 - y
                }
            }
        }

        #[private_repr]
        struct Box<T>(T)

        subscript Box<T>.value(self) -> _ {
            ref {
                let local = read(self.0);
                yield local
            }
        }

        struct Wrapper<T>(T)
        trait Get<Self |-> R> { fn get(x: Self) -> R; }
        impl<T, R> Get for <Self = Wrapper<T> |-> R = R> {
            fn get(x) { x.0.value }
        }

        fn of_int() -> string { get(Wrapper(Box(4))) }
        fn of_bool() -> int { get(Wrapper(Box(false)))(3) }
        fn generic(x) { get(Wrapper(Box(x))) }
        fn applied(w) { get(w)(3) }
    "# };
    assert_val_eq!(
        run_experimental_subscript_source(&format!(
            "{declarations}to_string((of_int(), of_bool(), generic(5), generic(true)(2), \
             applied(Wrapper(Box(false)))))"
        )),
        string("(hello, -3, hello, 2, -3)")
    );
    experimental_session()
        .fail_compilation(&format!("{declarations}get(Wrapper(Box(1.5)))"))
        .expect_trait_impl_not_found("Get", &["Self = Wrapper<Box<float>>"]);
}
