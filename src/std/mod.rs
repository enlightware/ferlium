// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::str::FromStr;

use crate::{
    Location,
    location::SourceTable,
    module::{self, Module, ModuleId},
    r#type::{Type, TypeKind, bare_native_type},
    value::Value,
};

use array::Array;
use math::{Float, Int};

pub mod array;
pub mod cast;
pub mod core;
pub mod core_traits_names;
pub mod default;
pub mod empty;
pub mod flow;
pub mod io;
mod json;
pub mod logic;
pub mod math;
pub mod mem;
pub mod option;
pub mod ordering;
mod prelude;
mod product_value_deriver;
pub mod serde;
pub mod string;
pub mod value;
pub mod variant;

pub(crate) static STD_MODULE_ID: ModuleId = ModuleId(0);

pub fn std_module(source_table: &mut SourceTable) -> Module {
    let mut module = Module::new(STD_MODULE_ID);
    // Built-in or derivable
    value::add_to_module(&mut module);
    core::add_to_module(&mut module);
    default::add_to_module(&mut module);
    empty::add_to_module(&mut module);
    flow::add_to_module(&mut module);
    cast::add_to_module(&mut module);
    module = prelude::declare_traits(module, source_table, STD_MODULE_ID);
    // mem::add_to_module(&mut module);
    logic::add_to_module(&mut module);
    math::add_to_module(&mut module);
    array::add_to_module(&mut module);
    io::add_to_module(&mut module);
    string::add_to_module(&mut module);
    variant::add_to_module(&mut module);
    serde::add_to_module(&mut module);
    json::add_to_module(&mut module);
    prelude::add_impls(module, source_table, STD_MODULE_ID)
}

pub fn new_module_using_std(module_id: ModuleId) -> Module {
    let mut new_module = Module::new(module_id);
    new_module.add_wildcard_use(module::Path::single_str("std"), Location::new_synthesized());
    new_module
}

pub fn default_value_for_type(ty: Type) -> Option<Value> {
    use TypeKind::*;
    match &*ty.data() {
        Variable(_) => None,
        Native(native_type) => {
            if native_type.bare_ty == bare_native_type::<()>() {
                Some(Value::unit())
            } else if native_type.bare_ty == bare_native_type::<bool>() {
                Some(Value::native(false))
            } else if native_type.bare_ty == bare_native_type::<Int>() {
                Some(Value::native(0))
            } else if native_type.bare_ty == bare_native_type::<Float>() {
                Some(Value::native::<Float>(Float::new(0.0).unwrap()))
            } else if native_type.bare_ty == bare_native_type::<string::String>() {
                Some(Value::native(string::String::from_str("").unwrap()))
            } else if native_type.bare_ty == bare_native_type::<Array>() {
                Some(Value::native(Array::new()))
            } else {
                None
            }
        }
        Tuple(tys) => tys
            .iter()
            .map(|ty| default_value_for_type(*ty))
            .collect::<Option<Vec<_>>>()
            .map(Value::tuple),
        Record(fields) => fields
            .iter()
            .map(|(_, ty)| default_value_for_type(*ty))
            .collect::<Option<Vec<_>>>()
            .map(Value::tuple),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;
    use ustr::ustr;

    use ordered_float::NotNan;

    use crate::{
        std::{
            array::{Array, array_type},
            logic::bool_type,
            math::{float_type, int_type},
            string::{self, string_type},
        },
        r#type::{Type, tuple_type},
        value::Value,
    };

    fn test_values_eq(actual: &Value, expected: &Value) -> bool {
        match (actual, expected) {
            (Value::Native(_), Value::Native(_)) => {
                if actual.as_primitive_ty::<()>().is_some()
                    && expected.as_primitive_ty::<()>().is_some()
                {
                    true
                } else if let (Some(actual), Some(expected)) = (
                    actual.as_primitive_ty::<bool>(),
                    expected.as_primitive_ty::<bool>(),
                ) {
                    actual == expected
                } else if let (Some(actual), Some(expected)) = (
                    actual.as_primitive_ty::<isize>(),
                    expected.as_primitive_ty::<isize>(),
                ) {
                    actual == expected
                } else if let (Some(actual), Some(expected)) = (
                    actual.as_primitive_ty::<NotNan<f64>>(),
                    expected.as_primitive_ty::<NotNan<f64>>(),
                ) {
                    actual == expected
                } else if let (Some(actual), Some(expected)) = (
                    actual.as_primitive_ty::<string::String>(),
                    expected.as_primitive_ty::<string::String>(),
                ) {
                    actual == expected
                } else if let (Some(actual), Some(expected)) = (
                    actual.as_primitive_ty::<Array>(),
                    expected.as_primitive_ty::<Array>(),
                ) {
                    actual.len() == expected.len()
                        && (0..actual.len()).all(|index| {
                            test_values_eq(actual.get(index).unwrap(), expected.get(index).unwrap())
                        })
                } else {
                    false
                }
            }
            (Value::Variant(actual), Value::Variant(expected)) => {
                actual.tag == expected.tag && test_values_eq(&actual.value, &expected.value)
            }
            (Value::Tuple(actual), Value::Tuple(expected)) => {
                actual.len() == expected.len()
                    && actual
                        .iter()
                        .zip(expected.iter())
                        .all(|(actual, expected)| test_values_eq(actual, expected))
            }
            (Value::Function(actual), Value::Function(expected)) => {
                actual.function == expected.function
                    && actual.module == expected.module
                    && actual.captured.len() == expected.captured.len()
                    && actual
                        .captured
                        .iter()
                        .zip(expected.captured.iter())
                        .all(|(actual, expected)| test_values_eq(actual, expected))
            }
            _ => false,
        }
    }

    fn assert_some_value_eq(actual: Option<Value>, expected: Value) {
        let actual = actual.expect("expected Some(value)");
        assert!(
            test_values_eq(&actual, &expected),
            "expected {}, got {}",
            expected.to_string_repr(),
            actual.to_string_repr()
        );
    }

    #[test]
    fn default_value_for_type() {
        use super::default_value_for_type as def_val;
        assert_some_value_eq(def_val(Type::unit()), Value::unit());
        assert_some_value_eq(def_val(bool_type()), Value::native(false));
        assert_some_value_eq(def_val(int_type()), Value::native(0_isize));
        assert_some_value_eq(
            def_val(float_type()),
            Value::native(NotNan::new(0.0_f64).unwrap()),
        );
        assert_some_value_eq(
            def_val(string_type()),
            Value::native(string::String::from_str("").unwrap()),
        );
        assert_some_value_eq(def_val(array_type(int_type())), Value::native(Array::new()));
        assert_some_value_eq(
            def_val(array_type(float_type())),
            Value::native(Array::new()),
        );
        assert_some_value_eq(
            def_val(tuple_type([int_type(), bool_type()])),
            Value::tuple([Value::native(0_isize), Value::native(false)]),
        );
        assert_some_value_eq(
            def_val(Type::record([
                (ustr("a"), int_type()),
                (ustr("b"), bool_type()),
            ])),
            Value::tuple([Value::native(0_isize), Value::native(false)]),
        );
    }
}
