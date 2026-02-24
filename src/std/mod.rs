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
pub mod bits;
pub mod cast;
pub mod concat;
pub mod contains;
pub mod core;
pub mod flow;
pub mod io;
pub mod iterator;
mod json;
pub mod logic;
pub mod math;
pub mod mem;
pub mod option;
pub mod ordering;
mod prelude;
pub mod serde;
pub mod string;
pub mod variant;

pub fn std_module(source_table: &mut SourceTable, module_id: ModuleId) -> Module {
    let mut module = Module::new(module_id);
    core::add_to_module(&mut module);
    flow::add_to_module(&mut module);
    cast::add_to_module(&mut module);
    // mem::add_to_module(&mut module);
    bits::add_to_module(&mut module);
    logic::add_to_module(&mut module);
    ordering::add_to_module(&mut module);
    concat::add_to_module(&mut module);
    contains::add_to_module(&mut module);
    math::add_to_module(&mut module);
    array::add_to_module(&mut module);
    io::add_to_module(&mut module);
    string::add_to_module(&mut module);
    variant::add_to_module(&mut module);
    iterator::add_to_module(&mut module);
    serde::add_to_module(&mut module);
    json::add_to_module(&mut module);
    prelude::add_to_module(&mut module, source_table, module_id);
    module
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

    #[test]
    fn default_value_for_type() {
        use super::default_value_for_type as def_val;
        assert_eq!(def_val(Type::unit()), Some(Value::unit()));
        assert_eq!(def_val(bool_type()), Some(Value::native(false)));
        assert_eq!(def_val(int_type()), Some(Value::native(0_isize)));
        assert_eq!(
            def_val(float_type()),
            Some(Value::native(NotNan::new(0.0_f64).unwrap()))
        );
        assert_eq!(
            def_val(string_type()),
            Some(Value::native(string::String::from_str("").unwrap()))
        );
        assert_eq!(
            def_val(array_type(int_type())),
            Some(Value::native(Array::new()))
        );
        assert_eq!(
            def_val(array_type(float_type())),
            Some(Value::native(Array::new()))
        );
        assert_eq!(
            def_val(tuple_type([int_type(), bool_type()])),
            Some(Value::tuple([Value::native(0_isize), Value::native(false)]))
        );
        assert_eq!(
            def_val(Type::record([
                (ustr("a"), int_type()),
                (ustr("b"), bool_type())
            ])),
            Some(Value::tuple([Value::native(0_isize), Value::native(false)]))
        );
    }
}
