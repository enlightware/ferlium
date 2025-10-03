// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    cached_ty,
    containers::b,
    module::Module,
    std::{
        array::Array,
        logic::bool_type,
        math::{float_type, int_type},
        string::string_type,
    },
    r#type::{NativeType, Type, TypeKind, bare_native_type, store_types},
};
use ustr::ustr;

pub fn variant_type() -> Type {
    cached_ty!(|| {
        let bool_tuple1 = Type::tuple([bool_type()]);
        let int_tuple1 = Type::tuple([int_type()]);
        let float_tuple1 = Type::tuple([float_type()]);
        let string_tuple1 = Type::tuple([string_type()]);
        let bare_array_ty = bare_native_type::<Array>();
        let seq_array = TypeKind::Native(b(NativeType {
            bare_ty: bare_array_ty.clone(),
            arguments: vec![Type::new_local(5)],
        }));
        let seq_tuple1 = TypeKind::Tuple(vec![Type::new_local(0)]);
        let object_entry_tuple = TypeKind::Tuple(vec![string_type(), Type::new_local(5)]);
        let object_array = TypeKind::Native(b(NativeType {
            bare_ty: bare_array_ty,
            arguments: vec![Type::new_local(2)],
        }));
        let object_tuple1 = TypeKind::Tuple(vec![Type::new_local(3)]);
        let variant = TypeKind::Variant(vec![
            (ustr("None"), Type::unit()),
            (ustr("Bool"), bool_tuple1),
            (ustr("Int"), int_tuple1),
            (ustr("Float"), float_tuple1),
            (ustr("String"), string_tuple1),
            (ustr("Array"), Type::new_local(1)),
            (ustr("Object"), Type::new_local(4)),
        ]);
        store_types(&[
            seq_array,
            seq_tuple1,
            object_entry_tuple,
            object_array,
            object_tuple1,
            variant,
        ])[5]
    })
}

pub fn variant_object_entry_type() -> Type {
    Type::tuple([string_type(), variant_type()])
}

pub fn add_to_module(to: &mut Module) {
    // Types
    to.type_aliases.set("Variant", variant_type());
}
