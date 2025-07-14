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
    format::FormatWith,
    r#type::{record_type, tuple_type, variant_type, FnType, Type},
    resolve_concrete_type, resolve_generic_type,
    std::{
        array::array_type,
        logic::bool_type,
        math::{float_type, int_type},
        string::string_type,
        StdModuleEnv,
    },
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn primitive() {
    let env = StdModuleEnv::new();
    assert_eq!(
        resolve_concrete_type("()", &env.get()).unwrap(),
        Type::unit()
    );
    assert_eq!(
        resolve_concrete_type("bool", &env.get()).unwrap(),
        bool_type()
    );
    assert_eq!(
        resolve_concrete_type("int", &env.get()).unwrap(),
        int_type()
    );
    assert_eq!(
        resolve_concrete_type("float", &env.get()).unwrap(),
        float_type()
    );
    assert_eq!(
        resolve_concrete_type("string", &env.get()).unwrap(),
        string_type()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn tuple() {
    let env = StdModuleEnv::new();
    assert_eq!(
        resolve_concrete_type("(int,)", &env.get()).unwrap(),
        tuple_type([int_type()])
    );
    assert_eq!(
        resolve_concrete_type("(int, int)", &env.get()).unwrap(),
        tuple_type([int_type(), int_type()])
    );
    assert_eq!(
        resolve_concrete_type("(int, int, int)", &env.get()).unwrap(),
        tuple_type([int_type(), int_type(), int_type()])
    );
    assert_eq!(
        resolve_concrete_type("(int, float)", &env.get()).unwrap(),
        tuple_type([int_type(), float_type()])
    );
    assert_eq!(
        resolve_concrete_type("(int, (bool, string))", &env.get()).unwrap(),
        tuple_type([int_type(), tuple_type([bool_type(), string_type()])])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn record() {
    let env = StdModuleEnv::new();
    assert_eq!(
        resolve_concrete_type("{a: int}", &env.get()).unwrap(),
        record_type([("a", int_type())])
    );
    assert_eq!(
        resolve_concrete_type("{a: int,}", &env.get()).unwrap(),
        record_type([("a", int_type())])
    );
    assert_eq!(
        resolve_concrete_type("{a: int, b: bool}", &env.get()).unwrap(),
        record_type([("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        resolve_concrete_type("{a: int, b: bool, }", &env.get()).unwrap(),
        record_type([("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        resolve_concrete_type("{b: bool, a: int}", &env.get()).unwrap(),
        record_type([("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        resolve_concrete_type("{b: bool, a: int}", &env.get()).unwrap(),
        resolve_concrete_type("{a: int, b: bool}", &env.get()).unwrap(),
    );
    assert_eq!(
        resolve_concrete_type("{a: int, b: { c: bool, d: float } }", &env.get()).unwrap(),
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
        resolve_concrete_type("Some(int)|None", &env.get()).unwrap(),
        variant_type([("Some", tuple_type([int_type()])), ("None", Type::unit()),])
    );
    assert_eq!(
        resolve_concrete_type("RGB (int, int, int) | Color(string)", &env.get()).unwrap(),
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
    assert_eq!(
        resolve_concrete_type("int", &env.get()).unwrap(),
        int_type()
    );
    assert_eq!(
        resolve_concrete_type("(int)", &env.get()).unwrap(),
        int_type()
    );
    assert_eq!(
        resolve_concrete_type("((int))", &env.get()).unwrap(),
        int_type()
    );
    assert_eq!(
        resolve_concrete_type("(((int)))", &env.get()).unwrap(),
        int_type()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fn_type() {
    let env = StdModuleEnv::new();
    assert_eq!(
        resolve_concrete_type("() -> ()", &env.get()).unwrap(),
        Type::function_by_val_with_effects([], Type::unit(), EffType::empty())
    );
    assert_eq!(
        resolve_concrete_type("(int) -> int", &env.get()).unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty())
    );
    assert_eq!(
        resolve_concrete_type("((int)) -> int", &env.get()).unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty())
    );
    assert_eq!(
        resolve_concrete_type("(int) -> (int)", &env.get()).unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty())
    );
    assert_eq!(
        resolve_concrete_type("(int) -> (int,)", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            tuple_type([int_type()]),
            EffType::empty()
        )
    );
    assert_eq!(
        resolve_concrete_type("(int, float) -> ()", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [int_type(), float_type()],
            Type::unit(),
            EffType::empty()
        )
    );
    assert_eq!(
        resolve_concrete_type("((int, float)) -> ()", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            Type::unit(),
            EffType::empty()
        )
    );
    assert_eq!(
        resolve_concrete_type("((int, float)) -> (bool, string)", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            tuple_type([bool_type(), string_type()]),
            EffType::empty()
        )
    );
    assert_eq!(
        resolve_concrete_type("(&mut [int]) -> int", &env.get()).unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(int_type()), true)],
            int_type(),
            EffType::empty()
        ))
    );
    assert_eq!(
        resolve_concrete_type("(&mut [float], &mut int) -> ()", &env.get()).unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(float_type()), true), (int_type(), true)],
            Type::unit(),
            EffType::empty()
        ))
    );

    assert_eq!(
        resolve_generic_type("() -> ()", &env.get()).unwrap(),
        Type::function_by_val_with_effects([], Type::unit(), EffType::single_variable_id(0))
    );
    assert_eq!(
        resolve_generic_type("(int) -> int", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        resolve_generic_type("((int)) -> int", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        resolve_generic_type("(int) -> (int)", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        resolve_generic_type("(int) -> (int,)", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            tuple_type([int_type()]),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        resolve_generic_type("(int, float) -> ()", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [int_type(), float_type()],
            Type::unit(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        resolve_generic_type("((int, float)) -> ()", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            Type::unit(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        resolve_generic_type("((int, float)) -> (bool, string)", &env.get()).unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            tuple_type([bool_type(), string_type()]),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        resolve_generic_type("(&mut [int]) -> int", &env.get()).unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(int_type()), true)],
            int_type(),
            EffType::single_variable_id(0)
        ))
    );
    assert_eq!(
        resolve_generic_type("(&mut [float], &mut int) -> ()", &env.get()).unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(float_type()), true), (int_type(), true)],
            Type::unit(),
            EffType::single_variable_id(0)
        ))
    );

    assert_eq!(
        format!(
            "{}",
            FormatWith::new(
                &resolve_concrete_type("(&mut int)", &env.get()).unwrap_err(),
                &"(&mut int)"
            )
        ),
        "Parsing failed: types outside function arguments cannot be &mut in &mut int"
    );
    assert_eq!(
        format!(
            "{}",
            FormatWith::new(
                &resolve_concrete_type("(&mut int,)", &env.get()).unwrap_err(),
                &"(&mut int,)"
            )
        ),
        "Parsing failed: types outside function arguments cannot be &mut in &mut int"
    );
    assert_eq!(
        format!(
            "{}",
            FormatWith::new(
                &resolve_concrete_type("(bool, float, &mut int)", &env.get()).unwrap_err(),
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
        resolve_generic_type("_", &env.get()).unwrap(),
        Type::variable_id(0)
    );
    assert_eq!(
        resolve_generic_type("(int, _)", &env.get()).unwrap(),
        tuple_type([int_type(), Type::variable_id(0)])
    );
    assert_eq!(
        resolve_generic_type("(_, _)", &env.get()).unwrap(),
        tuple_type([Type::variable_id(0), Type::variable_id(0)])
    );
    assert_eq!(
        resolve_generic_type("(&mut [_], &mut int) -> _", &env.get()).unwrap(),
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
        resolve_concrete_type(
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
