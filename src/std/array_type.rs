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

/// Borrows an interpreter array's initialized elements in logical order.
///
/// This is the inverse view of [`array_value_from_vec`] used by MIR reification. It deliberately
/// validates the compiler-known array representation rather than accepting a malformed tuple: a
/// drift between the std type and this runtime shape must refuse an optimization, not manufacture
/// a different value.
pub(crate) fn array_value_elements(value: &Value) -> Option<Vec<&Value>> {
    let fields = value.as_tuple()?;
    if fields.len() != 4 {
        return None;
    }
    let capacity = usize::try_from(*fields[0].as_primitive_ty::<isize>()?).ok()?;
    let buffer = fields[1].as_primitive_ty::<Buffer>()?;
    let len = usize::try_from(*fields[2].as_primitive_ty::<isize>()?).ok()?;
    let start = usize::try_from(*fields[3].as_primitive_ty::<isize>()?).ok()?;
    if capacity != buffer.capacity()
        || len > capacity
        || (capacity == 0 && (len != 0 || start != 0))
        || (capacity != 0 && start >= capacity)
    {
        return None;
    }
    (0..len)
        .map(|offset| buffer.get((start + offset) % capacity))
        .collect()
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, std::buffer::buffer_type};
    use ustr::ustr;

    /// `BuildArray`, HIR array lowering and interpreter values all rely on this compiler-known
    /// boundary. A std record edit must update them together rather than silently changing which
    /// tuple field is interpreted as the backing buffer or logical length.
    #[test]
    fn compiler_array_shape_matches_runtime_tuple_representation() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let int = int_type();
        let named = array_type(int).data().as_named().unwrap().clone();
        let shape = named.instantiated_shape(&env);
        let fields = shape.data().as_record().unwrap().clone();
        assert_eq!(
            fields,
            vec![
                (ustr("capacity"), int),
                (ustr("data"), buffer_type(int)),
                (ustr("len"), int),
                (ustr("start"), int),
            ]
        );

        let value = array_value_from_vec(vec![Value::native(10isize), Value::native(20isize)]);
        let runtime = value.as_tuple().expect("an array value is tuple-backed");
        assert_eq!(runtime.len(), fields.len());
        assert_eq!(runtime[0].as_primitive_ty::<isize>(), Some(&2));
        assert_eq!(
            runtime[1].as_primitive_ty::<Buffer>().unwrap().capacity(),
            2
        );
        assert_eq!(runtime[2].as_primitive_ty::<isize>(), Some(&2));
        assert_eq!(runtime[3].as_primitive_ty::<isize>(), Some(&0));
        assert_eq!(
            array_value_elements(&value)
                .unwrap()
                .into_iter()
                .map(|element| *element.as_primitive_ty::<isize>().unwrap())
                .collect::<Vec<_>>(),
            vec![10, 20]
        );
        value.discard_storage();
    }
}
