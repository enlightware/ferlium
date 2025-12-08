// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ferlium::{
    effects::EffType,
    format::{FormatWith, FormatWithData},
    module::ModuleEnv,
    resolve_defined_type, resolve_holed_type,
    std::{
        StdModuleEnv,
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

use crate::common::{compile, float, int, run};

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn primitive() {
    let env = StdModuleEnv::new();
    assert_eq!(
        resolve_defined_type("()", &env.get()).unwrap(),
        Type::unit()
    );
    assert_eq!(
        resolve_defined_type("bool", &env.get()).unwrap(),
        bool_type()
    );
    assert_eq!(resolve_defined_type("int", &env.get()).unwrap(), int_type());
    assert_eq!(
        resolve_defined_type("float", &env.get()).unwrap(),
        float_type()
    );
    assert_eq!(
        resolve_defined_type("string", &env.get()).unwrap(),
        string_type()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn tuple() {
    let env = StdModuleEnv::new();
    assert_eq!(
        resolve_defined_type("(int,)", &env.get()).unwrap(),
        tuple_type([int_type()])
    );
    assert_eq!(
        resolve_defined_type("(int, int)", &env.get()).unwrap(),
        tuple_type([int_type(), int_type()])
    );
    assert_eq!(
        resolve_defined_type("(int, int, int)", &env.get()).unwrap(),
        tuple_type([int_type(), int_type(), int_type()])
    );
    assert_eq!(
        resolve_defined_type("(int, float)", &env.get()).unwrap(),
        tuple_type([int_type(), float_type()])
    );
    assert_eq!(
        resolve_defined_type("(int, (bool, string))", &env.get()).unwrap(),
        tuple_type([int_type(), tuple_type([bool_type(), string_type()])])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn record() {
    let env = StdModuleEnv::new();
    assert_eq!(
        resolve_defined_type("{a: int}", &env.get()).unwrap(),
        record_type([("a", int_type())])
    );
    assert_eq!(
        resolve_defined_type("{a: int,}", &env.get()).unwrap(),
        record_type([("a", int_type())])
    );
    assert_eq!(
        resolve_defined_type("{a: int, b: bool}", &env.get()).unwrap(),
        record_type([("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        resolve_defined_type("{a: int, b: bool, }", &env.get()).unwrap(),
        record_type([("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        resolve_defined_type("{b: bool, a: int}", &env.get()).unwrap(),
        record_type([("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        resolve_defined_type("{b: bool, a: int}", &env.get()).unwrap(),
        resolve_defined_type("{a: int, b: bool}", &env.get()).unwrap(),
    );
    assert_eq!(
        resolve_defined_type("{a: int, b: { c: bool, d: float } }", &env.get()).unwrap(),
        record_type([
            ("a", int_type()),
            ("b", record_type([("c", bool_type()), ("d", float_type())]))
        ])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn variant() {
    let env = StdModuleEnv::new();
    assert_eq!(
        resolve_defined_type("Some(int)|None", &env.get()).unwrap(),
        variant_type([("Some", tuple_type([int_type()])), ("None", Type::unit()),])
    );
    assert_eq!(
        resolve_defined_type("RGB (int, int, int) | Color(string)", &env.get()).unwrap(),
        variant_type([
            ("RGB", tuple_type([int_type(), int_type(), int_type()])),
            ("Color", tuple_type([string_type()])),
        ])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parentheses() {
    let env = StdModuleEnv::new();
    assert_eq!(resolve_defined_type("int", &env.get()).unwrap(), int_type());
    assert_eq!(
        resolve_defined_type("(int)", &env.get()).unwrap(),
        int_type()
    );
    assert_eq!(
        resolve_defined_type("((int))", &env.get()).unwrap(),
        int_type()
    );
    assert_eq!(
        resolve_defined_type("(((int)))", &env.get()).unwrap(),
        int_type()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fn_type() {
    let env = StdModuleEnv::new();
    assert_eq!(
        resolve_defined_type("() -> ()", &env.get()).unwrap(),
        Type::function_by_val_with_effects([], Type::unit(), EffType::empty())
    );
    assert_eq!(
        resolve_defined_type("(int) -> int", &env.get()).unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty())
    );
    assert_eq!(
        resolve_defined_type("((int)) -> int", &env.get()).unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty())
    );
    assert_eq!(
        resolve_defined_type("(int) -> (int)", &env.get()).unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty())
    );
    assert_eq!(
        resolve_defined_type("(int) -> (int,)", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            tuple_type([int_type()]),
            EffType::empty()
        )
    );
    assert_eq!(
        resolve_defined_type("(int, float) -> ()", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [int_type(), float_type()],
            Type::unit(),
            EffType::empty()
        )
    );
    assert_eq!(
        resolve_defined_type("((int, float)) -> ()", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            Type::unit(),
            EffType::empty()
        )
    );
    assert_eq!(
        resolve_defined_type("((int, float)) -> (bool, string)", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            tuple_type([bool_type(), string_type()]),
            EffType::empty()
        )
    );
    assert_eq!(
        resolve_defined_type("(&mut [int]) -> int", &env.get()).unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(int_type()), true)],
            int_type(),
            EffType::empty()
        ))
    );
    assert_eq!(
        resolve_defined_type("(&mut [float], &mut int) -> ()", &env.get()).unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(float_type()), true), (int_type(), true)],
            Type::unit(),
            EffType::empty()
        ))
    );

    assert_eq!(
        resolve_holed_type("() -> ()", &env.get()).unwrap(),
        Type::function_by_val_with_effects([], Type::unit(), EffType::single_variable_id(0))
    );
    assert_eq!(
        resolve_holed_type("(int) -> int", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        resolve_holed_type("((int)) -> int", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        resolve_holed_type("(int) -> (int)", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        resolve_holed_type("(int) -> (int,)", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            tuple_type([int_type()]),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        resolve_holed_type("(int, float) -> ()", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [int_type(), float_type()],
            Type::unit(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        resolve_holed_type("((int, float)) -> ()", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            Type::unit(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        resolve_holed_type("((int, float)) -> (bool, string)", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            tuple_type([bool_type(), string_type()]),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        resolve_holed_type("(&mut [int]) -> int", &env.get()).unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(int_type()), true)],
            int_type(),
            EffType::single_variable_id(0)
        ))
    );
    assert_eq!(
        resolve_holed_type("(&mut [float], &mut int) -> ()", &env.get()).unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(float_type()), true), (int_type(), true)],
            Type::unit(),
            EffType::single_variable_id(0)
        ))
    );

    assert_eq!(
        format!(
            "{}",
            FormatWithData::new(
                &resolve_defined_type("(&mut int)", &env.get()).unwrap_err(),
                &"(&mut int)"
            )
        ),
        "Parsing failed: types outside function arguments cannot be &mut in &mut int"
    );
    assert_eq!(
        format!(
            "{}",
            FormatWithData::new(
                &resolve_defined_type("(&mut int,)", &env.get()).unwrap_err(),
                &"(&mut int,)"
            )
        ),
        "Parsing failed: types outside function arguments cannot be &mut in &mut int"
    );
    assert_eq!(
        format!(
            "{}",
            FormatWithData::new(
                &resolve_defined_type("(bool, float, &mut int)", &env.get()).unwrap_err(),
                &"(bool, float, &mut int)"
            )
        ),
        "Parsing failed: types outside function arguments cannot be &mut in &mut int"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_types() {
    let env = StdModuleEnv::new();
    assert_eq!(
        resolve_holed_type("_", &env.get()).unwrap(),
        Type::variable_id(0)
    );
    assert_eq!(
        resolve_holed_type("(int, _)", &env.get()).unwrap(),
        tuple_type([int_type(), Type::variable_id(0)])
    );
    assert_eq!(
        resolve_holed_type("(_, _)", &env.get()).unwrap(),
        tuple_type([Type::variable_id(0), Type::variable_id(0)])
    );
    assert_eq!(
        resolve_holed_type("(&mut [_], &mut int) -> _", &env.get()).unwrap(),
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
    let env = StdModuleEnv::new();
    assert_eq!(
        resolve_defined_type(
            "[{name: string, age: int, nick: Some(string) | None}]",
            &env.get()
        )
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
fn ret_type_overloading() {
    assert_eq!(
        run(indoc! { r#"
            fn f() { let a = 0; a }
            ((f(): int), (f(): float))
        "# }),
        tuple!(int(0), float(0.0)),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn returning_variant_is_properly_unified() {
    // Test the Variant type which had the original issue
    // This tests deeply nested recursive variant structures
    let (module_and_expr, modules) = compile(indoc! { r#"
        fn make_variant_array() -> Variant {
            Array([])
        }
    "# });
    let module = module_and_expr.module;
    let fn_def = &module
        .get_own_function(ustr("make_variant_array"))
        .unwrap()
        .definition;
    if fn_def.ty_scheme.ty().ret != variant::variant_type() {
        let module_env = ModuleEnv::new(&module, &modules, false);
        panic!(
            "Expected return type to be Variant, got {}",
            fn_def.ty_scheme.ty().ret.format_with(&module_env)
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn variant_type_alias_in_function_signature() {
    // Test that the Variant type alias is preserved in function signatures
    // This reproduces the issue where Variant appears unfolded in function types
    let (module_and_expr, modules) = compile(indoc! { r#"
        fn process_variant(v: Variant) -> Variant {
            v
        }
        
        fn process_variant_array(entries: [(string, Variant)]) -> Variant {
            entries[0].1
        }
    "# });
    let module = module_and_expr.module;
    let module_env = ModuleEnv::new(&module, &modules, false);

    // Check first function
    let fn_def1 = &module
        .get_own_function(ustr("process_variant"))
        .unwrap()
        .definition;
    let sig1 = fn_def1.ty_scheme.ty().format_with(&module_env).to_string();
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
        .get_own_function(ustr("process_variant_array"))
        .unwrap()
        .definition;
    let sig2 = fn_def2.ty_scheme.ty().format_with(&module_env).to_string();
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
            ferlium::r#type::dump_type_world(1, &module_env);
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
