// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ferlium::{
    effects::EffType,
    error::CompilationErrorImpl,
    format::{FormatWith, FormatWithData},
    std::{
        array::array_type,
        logic::bool_type,
        math::{float_type, int_type},
        string::string_type,
        variant,
    },
    r#type::{FnType, Type, record_type, tuple_type, variant_type},
    value::Value,
};

use indoc::indoc;

use ustr::ustr;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

use crate::common::{TestSession, float, int};

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn primitive() {
    let mut session = TestSession::new();
    assert_eq!(session.resolve_defined_type("()").unwrap(), Type::unit());
    assert_eq!(session.resolve_defined_type("bool").unwrap(), bool_type());
    assert_eq!(session.resolve_defined_type("int").unwrap(), int_type());
    assert_eq!(session.resolve_defined_type("float").unwrap(), float_type());
    assert_eq!(
        session.resolve_defined_type("string").unwrap(),
        string_type()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn tuple() {
    let mut session = TestSession::new();
    assert_eq!(
        session.resolve_defined_type("(int,)").unwrap(),
        tuple_type([int_type()])
    );
    assert_eq!(
        session.resolve_defined_type("(int, int)").unwrap(),
        tuple_type([int_type(), int_type()])
    );
    assert_eq!(
        session.resolve_defined_type("(int, int, int)").unwrap(),
        tuple_type([int_type(), int_type(), int_type()])
    );
    assert_eq!(
        session.resolve_defined_type("(int, float)").unwrap(),
        tuple_type([int_type(), float_type()])
    );
    assert_eq!(
        session
            .resolve_defined_type("(int, (bool, string))")
            .unwrap(),
        tuple_type([int_type(), tuple_type([bool_type(), string_type()])])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn record() {
    let mut session = TestSession::new();
    assert_eq!(
        session.resolve_defined_type("{a: int}").unwrap(),
        record_type([("a", int_type())])
    );
    assert_eq!(
        session.resolve_defined_type("{a: int,}").unwrap(),
        record_type([("a", int_type())])
    );
    assert_eq!(
        session.resolve_defined_type("{a: int, b: bool}").unwrap(),
        record_type([("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        session.resolve_defined_type("{a: int, b: bool, }").unwrap(),
        record_type([("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        session.resolve_defined_type("{b: bool, a: int}").unwrap(),
        record_type([("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        session.resolve_defined_type("{b: bool, a: int}").unwrap(),
        session.resolve_defined_type("{a: int, b: bool}").unwrap(),
    );
    assert_eq!(
        session
            .resolve_defined_type("{a: int, b: { c: bool, d: float } }")
            .unwrap(),
        record_type([
            ("a", int_type()),
            ("b", record_type([("c", bool_type()), ("d", float_type())]))
        ])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn variant() {
    let mut session = TestSession::new();
    assert_eq!(
        session.resolve_defined_type("Some(int)|None").unwrap(),
        variant_type([("Some", tuple_type([int_type()])), ("None", Type::unit()),])
    );
    assert_eq!(
        session
            .resolve_defined_type("RGB (int, int, int) | Color(string)")
            .unwrap(),
        variant_type([
            ("RGB", tuple_type([int_type(), int_type(), int_type()])),
            ("Color", tuple_type([string_type()])),
        ])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parentheses() {
    let mut session = TestSession::new();
    assert_eq!(session.resolve_defined_type("int").unwrap(), int_type());
    assert_eq!(session.resolve_defined_type("(int)").unwrap(), int_type());
    assert_eq!(session.resolve_defined_type("((int))").unwrap(), int_type());
    assert_eq!(
        session.resolve_defined_type("(((int)))").unwrap(),
        int_type()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fn_type() {
    let mut session = TestSession::new();
    assert_eq!(
        session.resolve_defined_type("() -> ()").unwrap(),
        Type::function_by_val_with_effects([], Type::unit(), EffType::empty())
    );
    assert_eq!(
        session.resolve_defined_type("(int) -> int").unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty())
    );
    assert_eq!(
        session.resolve_defined_type("((int)) -> int").unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty())
    );
    assert_eq!(
        session.resolve_defined_type("(int) -> (int)").unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty())
    );
    assert_eq!(
        session.resolve_defined_type("(int) -> (int,)").unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            tuple_type([int_type()]),
            EffType::empty()
        )
    );
    assert_eq!(
        session.resolve_defined_type("(int, float) -> ()").unwrap(),
        Type::function_by_val_with_effects(
            [int_type(), float_type()],
            Type::unit(),
            EffType::empty()
        )
    );
    assert_eq!(
        session
            .resolve_defined_type("((int, float)) -> ()")
            .unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            Type::unit(),
            EffType::empty()
        )
    );
    assert_eq!(
        session
            .resolve_defined_type("((int, float)) -> (bool, string)")
            .unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            tuple_type([bool_type(), string_type()]),
            EffType::empty()
        )
    );
    assert_eq!(
        session.resolve_defined_type("(&mut [int]) -> int").unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(int_type()), true)],
            int_type(),
            EffType::empty()
        ))
    );
    assert_eq!(
        session
            .resolve_defined_type("(&mut [float], &mut int) -> ()")
            .unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(float_type()), true), (int_type(), true)],
            Type::unit(),
            EffType::empty()
        ))
    );

    assert_eq!(
        session.resolve_holed_type("() -> ()").unwrap(),
        Type::function_by_val_with_effects([], Type::unit(), EffType::single_variable_id(0))
    );
    assert_eq!(
        session.resolve_holed_type("(int) -> int").unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        session.resolve_holed_type("((int)) -> int").unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        session.resolve_holed_type("(int) -> (int)").unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        session.resolve_holed_type("(int) -> (int,)").unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            tuple_type([int_type()]),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        session.resolve_holed_type("(int, float) -> ()").unwrap(),
        Type::function_by_val_with_effects(
            [int_type(), float_type()],
            Type::unit(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        session.resolve_holed_type("((int, float)) -> ()").unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            Type::unit(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        session
            .resolve_holed_type("((int, float)) -> (bool, string)")
            .unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            tuple_type([bool_type(), string_type()]),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        session.resolve_holed_type("(&mut [int]) -> int").unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(int_type()), true)],
            int_type(),
            EffType::single_variable_id(0)
        ))
    );
    assert_eq!(
        session
            .resolve_holed_type("(&mut [float], &mut int) -> ()")
            .unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(float_type()), true), (int_type(), true)],
            Type::unit(),
            EffType::single_variable_id(0)
        ))
    );

    assert!(
        format!(
            "{}",
            FormatWithData::new(
                &session.resolve_defined_type("(&mut int)").unwrap_err(),
                session.source_table(),
            )
        )
        .starts_with(
            "Parsing failed: types outside function arguments cannot be &mut in `&mut int`"
        )
    );
    assert!(
        format!(
            "{}",
            FormatWithData::new(
                &session.resolve_defined_type("(&mut int,)").unwrap_err(),
                session.source_table(),
            )
        )
        .starts_with(
            "Parsing failed: types outside function arguments cannot be &mut in `&mut int`"
        )
    );
    assert!(
        format!(
            "{}",
            FormatWithData::new(
                &session
                    .resolve_defined_type("(bool, float, &mut int)")
                    .unwrap_err(),
                session.source_table(),
            )
        )
        .starts_with(
            "Parsing failed: types outside function arguments cannot be &mut in `&mut int`"
        )
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_types() {
    let mut session = TestSession::new();
    assert_eq!(
        session.resolve_holed_type("_").unwrap(),
        Type::variable_id(0)
    );
    assert_eq!(
        session.resolve_holed_type("(int, _)").unwrap(),
        tuple_type([int_type(), Type::variable_id(0)])
    );
    assert_eq!(
        session.resolve_holed_type("(_, _)").unwrap(),
        tuple_type([Type::variable_id(0), Type::variable_id(0)])
    );
    assert_eq!(
        session
            .resolve_holed_type("(&mut [_], &mut int) -> _")
            .unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(Type::variable_id(0)), true), (int_type(), true)],
            Type::variable_id(0),
            EffType::single_variable_id(0)
        ))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn complex_type() {
    let mut session = TestSession::new();
    assert_eq!(
        session
            .resolve_defined_type("[{name: string, age: int, nick: Some(string) | None}]")
            .unwrap(),
        array_type(record_type([
            ("name", string_type()),
            ("age", int_type()),
            (
                "nick",
                variant_type([
                    ("Some", tuple_type([string_type()])),
                    ("None", Type::unit()),
                ])
            )
        ]))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn variant_type_ascription() {
    let mut session = TestSession::new();
    let result = session.run(indoc! { r#"
        fn score(value) -> int {
            match value {
                Some { value } => value,
                Pair(x, y) => x + y,
                Empty => 0,
            }
        }

        let record: Some { value: int } | Pair(int, int) | Empty = Some { value: 40 };
        let tuple: Some { value: int } | Pair(int, int) | Empty = Pair(1, 2);
        let unit: Some { value: int } | Pair(int, int) | Empty = Empty;

        (
            score(record),
            score(tuple),
            score(unit),
        )
    "# });
    assert_eq!(result, tuple!(int(40), int(3), int(0)),);

    // Limitation: to avoid a conflict, return types instantiate the grammar without record variants.
    let err = session.fail_compilation(indoc! { r#"
        fn invalid() -> Some { value: int } | Pair(int, int) {
            Empty
        }
    "# });
    match err.into_inner() {
        CompilationErrorImpl::ParsingFailed(_) => {}
        other => {
            panic!("expected parsing failure for record-style variant return types, got {other:?}")
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ret_type_overloading() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
            fn f() { let a = 0; a }
            ((f(): int), (f(): float))
        "# }),
        tuple!(int(0), float(0.0)),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn returning_variant_is_properly_unified() {
    let mut session = TestSession::new();
    // Test the Variant type which had the original issue
    // This tests deeply nested recursive variant structures
    let module = session.compile_and_get_module(indoc! { r#"
        fn make_variant_array() -> Variant {
            Array([])
        }
    "# });

    let fn_def = &module
        .get_function(ustr("make_variant_array"))
        .unwrap()
        .definition;
    assert_eq!(
        fn_def.ty_scheme.ty().ret,
        variant::variant_type(),
        "Expected return type to be Variant"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn variant_type_alias_in_function_signature() {
    let mut session = TestSession::new();
    // Test that the Variant type alias is preserved in function signatures
    // This reproduces the issue where Variant appears unfolded in function types
    let module_id = session
        .compile(indoc! { r#"
        fn process_variant(v: Variant) -> Variant {
            v
        }

        fn process_variant_array(entries: [(string, Variant)]) -> Variant {
            entries[0].1
        }
    "# })
        .module_id;

    // Check first function
    let module = session.modules().get(module_id).unwrap();
    let fn_def1 = &module
        .get_function(ustr("process_variant"))
        .unwrap()
        .definition;
    let sig1 = fn_def1
        .ty_scheme
        .ty()
        .clone()
        .format_with(&session.std_module_env())
        .to_string();
    println!("process_variant signature: {}", sig1);

    // The signature should contain "Variant", not the unfolded type
    assert!(
        sig1.contains("Variant"),
        "Expected 'Variant' in signature, got: {}",
        sig1
    );
    assert!(
        !sig1.contains("Array ([Self])"),
        "Type alias should not be unfolded, got: {}",
        sig1
    );

    // Check second function
    let fn_def2 = &module
        .get_function(ustr("process_variant_array"))
        .unwrap()
        .definition;
    let sig2 = fn_def2
        .ty_scheme
        .ty()
        .format_with(&session.std_module_env())
        .to_string();
    println!("process_variant_array signature: {}", sig2);

    // Debug: Check what type is actually in the tuple
    let arg_ty = fn_def2.ty_scheme.ty().args[0].ty;
    println!("Argument type: {:?}", arg_ty);
    let arg_ty_data = arg_ty.data();
    if let Some(arr) = arg_ty_data.as_native() {
        println!("Array element type: {:?}", arr.arguments[0]);
        let elem_data = arr.arguments[0].data();
        if let Some(tup) = elem_data.as_tuple() {
            println!("Tuple element 0 (string): {:?}", tup[0]);
            println!("Tuple element 1 (should be Variant): {:?}", tup[1]);
            println!("Canonical variant_type(): {:?}", variant::variant_type());
            println!("Are they equal? {}", tup[1] == variant::variant_type());

            // Verify that the Variant type is correctly identified as world 1
            assert_eq!(
                tup[1],
                variant::variant_type(),
                "Tuple element should be the canonical Variant type from world 1"
            );

            // Dump world 1 to show the canonical Variant
            println!("\n=== Dumping world 1 (canonical Variant) ===");
            ferlium::r#type::dump_type_world(1, &session.std_module_env());
        } else {
            panic!("Expected array element to be a tuple");
        }
    }

    // The signature should contain "Variant", not the unfolded type
    assert!(
        sig2.contains("Variant"),
        "Expected 'Variant' in signature, got: {}",
        sig2
    );
    assert!(
        !sig2.contains("Array ([Self])"),
        "Type alias should not be unfolded, got: {}",
        sig2
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_solver_recursion_limit() {
    let mut session = TestSession::new();
    let code = indoc! { r#"
        fn buggy(s: string) -> Variant {
            (deserialize(parse_json(s)) : Variant)
        }
    "# };
    // We expect the solver to hit a cycle because Variant is a recursive type
    // and its automatic derivation loops back into itself.
    let err = session.fail_compilation(code);
    use CompilationErrorImpl::*;
    match err.into_inner() {
        TraitImplNotFound { .. }
        | TraitSolverCycleDetected { .. }
        | TraitSolverRecursionLimitExceeded { .. } => {}
        other => {
            panic!(
                "expected TraitImplNotFound or TraitSolverCycleDetected or TraitSolverRecursionLimitExceeded, got {other:?}"
            )
        }
    }
}
