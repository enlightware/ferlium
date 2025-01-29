// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use ferlium::{
    parse_type,
    r#type::Type,
    std::{
        array::array_type,
        logic::bool_type,
        math::{float_type, int_type},
        string::string_type,
    },
};
use ustr::ustr;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn primitive() {
    assert_eq!(parse_type("()").unwrap(), Type::unit());
    assert_eq!(parse_type("bool").unwrap(), bool_type());
    assert_eq!(parse_type("int").unwrap(), int_type());
    assert_eq!(parse_type("float").unwrap(), float_type());
    assert_eq!(parse_type("string").unwrap(), string_type());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn tuple() {
    assert_eq!(parse_type("(int,)").unwrap(), Type::tuple(vec![int_type()]));
    assert_eq!(
        parse_type("(int, int)").unwrap(),
        Type::tuple(vec![int_type(), int_type()])
    );
    assert_eq!(
        parse_type("(int, int, int)").unwrap(),
        Type::tuple(vec![int_type(), int_type(), int_type()])
    );
    assert_eq!(
        parse_type("(int, float)").unwrap(),
        Type::tuple(vec![int_type(), float_type()])
    );
    assert_eq!(
        parse_type("(int, (bool, string))").unwrap(),
        Type::tuple(vec![
            int_type(),
            Type::tuple(vec![bool_type(), string_type()])
        ])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn record() {
    assert_eq!(
        parse_type("{a: int}").unwrap(),
        Type::record(vec![(ustr("a"), int_type())])
    );
    assert_eq!(
        parse_type("{a: int,}").unwrap(),
        Type::record(vec![(ustr("a"), int_type())])
    );
    assert_eq!(
        parse_type("{a: int, b: bool}").unwrap(),
        Type::record(vec![(ustr("a"), int_type()), (ustr("b"), bool_type())])
    );
    assert_eq!(
        parse_type("{a: int, b: bool, }").unwrap(),
        Type::record(vec![(ustr("a"), int_type()), (ustr("b"), bool_type())])
    );
    assert_eq!(
        parse_type("{b: bool, a: int}").unwrap(),
        Type::record(vec![(ustr("a"), int_type()), (ustr("b"), bool_type())])
    );
    assert_eq!(
        parse_type("{a: int, b: { c: bool, d: float } }").unwrap(),
        Type::record(vec![
            (ustr("a"), int_type()),
            (
                ustr("b"),
                Type::record(vec![(ustr("c"), bool_type()), (ustr("d"), float_type())])
            )
        ])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn variant() {
    assert_eq!(
        parse_type("Some(int)|None").unwrap(),
        Type::variant(vec![
            (ustr("Some"), int_type()),
            (ustr("None"), Type::unit()),
        ])
    );
    assert_eq!(
        parse_type("RGB (int, int, int) | Color(string)").unwrap(),
        Type::variant(vec![
            (
                ustr("RGB"),
                Type::tuple(vec![int_type(), int_type(), int_type()])
            ),
            (ustr("Color"), string_type()),
        ])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parentheses() {
    assert_eq!(parse_type("int").unwrap(), int_type());
    assert_eq!(parse_type("(int)").unwrap(), int_type());
    assert_eq!(parse_type("((int))").unwrap(), int_type());
    assert_eq!(parse_type("(((int)))").unwrap(), int_type());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn complex_type() {
    assert_eq!(
        parse_type("[{name: string, age: int, nick: Some(string) | None}]").unwrap(),
        array_type(Type::record(vec![
            (ustr("name"), string_type()),
            (ustr("age"), int_type()),
            (
                ustr("nick"),
                Type::variant(vec![
                    (ustr("Some"), string_type()),
                    (ustr("None"), Type::unit()),
                ])
            )
        ]))
    );
}
