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
    parse_concrete_type, parse_generic_type,
    r#type::{record_type, tuple_type, variant_type, FnType, Type},
    std::{
        array::array_type,
        logic::bool_type,
        math::{float_type, int_type},
        string::string_type,
    },
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn primitive() {
    assert_eq!(parse_concrete_type("()").unwrap(), Type::unit());
    assert_eq!(parse_concrete_type("bool").unwrap(), bool_type());
    assert_eq!(parse_concrete_type("int").unwrap(), int_type());
    assert_eq!(parse_concrete_type("float").unwrap(), float_type());
    assert_eq!(parse_concrete_type("string").unwrap(), string_type());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn tuple() {
    assert_eq!(
        parse_concrete_type("(int,)").unwrap(),
        tuple_type([int_type()])
    );
    assert_eq!(
        parse_concrete_type("(int, int)").unwrap(),
        tuple_type([int_type(), int_type()])
    );
    assert_eq!(
        parse_concrete_type("(int, int, int)").unwrap(),
        tuple_type([int_type(), int_type(), int_type()])
    );
    assert_eq!(
        parse_concrete_type("(int, float)").unwrap(),
        tuple_type([int_type(), float_type()])
    );
    assert_eq!(
        parse_concrete_type("(int, (bool, string))").unwrap(),
        tuple_type([int_type(), tuple_type([bool_type(), string_type()])])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn record() {
    assert_eq!(
        parse_concrete_type("{a: int}").unwrap(),
        record_type(&[("a", int_type())])
    );
    assert_eq!(
        parse_concrete_type("{a: int,}").unwrap(),
        record_type(&[("a", int_type())])
    );
    assert_eq!(
        parse_concrete_type("{a: int, b: bool}").unwrap(),
        record_type(&[("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        parse_concrete_type("{a: int, b: bool, }").unwrap(),
        record_type(&[("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        parse_concrete_type("{b: bool, a: int}").unwrap(),
        record_type(&[("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        parse_concrete_type("{b: bool, a: int}").unwrap(),
        parse_concrete_type("{a: int, b: bool}").unwrap(),
    );
    assert_eq!(
        parse_concrete_type("{a: int, b: { c: bool, d: float } }").unwrap(),
        record_type(&[
            ("a", int_type()),
            ("b", record_type(&[("c", bool_type()), ("d", float_type())]))
        ])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn variant() {
    assert_eq!(
        parse_concrete_type("Some(int)|None").unwrap(),
        variant_type(&[("Some", int_type()), ("None", Type::unit()),])
    );
    assert_eq!(
        parse_concrete_type("RGB (int, int, int) | Color(string)").unwrap(),
        variant_type(&[
            ("RGB", tuple_type([int_type(), int_type(), int_type()])),
            ("Color", string_type()),
        ])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parentheses() {
    assert_eq!(parse_concrete_type("int").unwrap(), int_type());
    assert_eq!(parse_concrete_type("(int)").unwrap(), int_type());
    assert_eq!(parse_concrete_type("((int))").unwrap(), int_type());
    assert_eq!(parse_concrete_type("(((int)))").unwrap(), int_type());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fn_type() {
    assert_eq!(
        parse_concrete_type("() -> ()").unwrap(),
        Type::function_by_val_with_effects(&[], Type::unit(), EffType::single_variable_id(0))
    );
    assert_eq!(
        parse_concrete_type("(int) -> int").unwrap(),
        Type::function_by_val_with_effects(
            &[int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        parse_concrete_type("((int)) -> int").unwrap(),
        Type::function_by_val_with_effects(
            &[int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        parse_concrete_type("(int) -> (int)").unwrap(),
        Type::function_by_val_with_effects(
            &[int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        parse_concrete_type("(int) -> (int,)").unwrap(),
        Type::function_by_val_with_effects(
            &[int_type()],
            tuple_type([int_type()]),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        parse_concrete_type("(int, float) -> ()").unwrap(),
        Type::function_by_val_with_effects(
            &[int_type(), float_type()],
            Type::unit(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        parse_concrete_type("((int, float)) -> ()").unwrap(),
        Type::function_by_val_with_effects(
            &[tuple_type([int_type(), float_type()])],
            Type::unit(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        parse_concrete_type("((int, float)) -> (bool, string)").unwrap(),
        Type::function_by_val_with_effects(
            &[tuple_type([int_type(), float_type()])],
            tuple_type([bool_type(), string_type()]),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        parse_concrete_type("(&mut [int]) -> int").unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            &[(array_type(int_type()), true)],
            int_type(),
            EffType::single_variable_id(0)
        ))
    );
    assert_eq!(
        parse_concrete_type("(&mut [float], &mut int) -> ()").unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            &[(array_type(float_type()), true), (int_type(), true)],
            Type::unit(),
            EffType::single_variable_id(0)
        ))
    );
    assert_eq!(
        parse_concrete_type("(&mut int)").unwrap_err().0,
        "types outside function arguments cannot be &mut"
    );
    assert_eq!(
        parse_concrete_type("(&mut int,)").unwrap_err().0,
        "types outside function arguments cannot be &mut"
    );
    assert_eq!(
        parse_concrete_type("(bool, float, &mut int)")
            .unwrap_err()
            .0,
        "types outside function arguments cannot be &mut"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_types() {
    assert_eq!(parse_generic_type("_").unwrap(), Type::variable_id(0));
    assert_eq!(
        parse_generic_type("(int, _)").unwrap(),
        tuple_type([int_type(), Type::variable_id(0)])
    );
    assert_eq!(
        parse_generic_type("(_, _)").unwrap(),
        tuple_type([Type::variable_id(0), Type::variable_id(0)])
    );
    assert_eq!(
        parse_generic_type("(&mut [_], &mut int) -> _").unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            &[(array_type(Type::variable_id(0)), true), (int_type(), true)],
            Type::variable_id(0),
            EffType::single_variable_id(0)
        ))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn complex_type() {
    assert_eq!(
        parse_concrete_type("[{name: string, age: int, nick: Some(string) | None}]").unwrap(),
        array_type(record_type(&[
            ("name", string_type()),
            ("age", int_type()),
            (
                "nick",
                variant_type(&[("Some", string_type()), ("None", Type::unit()),])
            )
        ]))
    );
}
