// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    cached_ty,
    hir::value::Value,
    module::{LocalTypeDefId, TypeDefId},
    std::{STD_MODULE_ID, buffer::Buffer, math::int_type},
    types::r#type::Type,
};

// `std_module` declares `array_type.fer` before any other std type definition.
const ARRAY_TYPE_DEF: TypeDefId = TypeDefId {
    module: STD_MODULE_ID,
    index: LocalTypeDefId::new(0),
};

pub fn array_type(element_ty: Type) -> Type {
    Type::named(array_type_def(), [element_ty])
}

pub fn array_value_from_vec(values: Vec<Value>) -> Value {
    let len = values.len() as isize;
    // Record fields are currently stored in normalized field-name order:
    // capacity, data, len, start.
    Value::tuple([
        Value::native(len),
        Value::native(Buffer::from_vec(values)),
        Value::native(len),
        Value::native(0isize),
    ])
}

pub fn array_type_def() -> TypeDefId {
    ARRAY_TYPE_DEF
}

pub fn int_array_type() -> Type {
    cached_ty!(|| array_type(int_type()))
}

pub fn array_type_generic() -> Type {
    cached_ty!(|| array_type(Type::variable_id(0)))
}
