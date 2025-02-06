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
    r#type::{bare_native_type, store_types, NativeType, Type, TypeKind},
    std::{
        array::Array,
        logic::bool_type,
        math::{float_type, int_type},
        string::string_type,
    },
};
use ustr::ustr;

pub fn script_variant_type() -> Type {
    cached_ty!(|| {
        let bare_array_ty = bare_native_type::<Array>();
        let seq = TypeKind::Native(b(NativeType {
            bare_ty: bare_array_ty,
            arguments: vec![Type::new_local(1)],
        }));
        let variant = TypeKind::Variant(vec![
            (ustr("None"), Type::unit()),
            (ustr("Bool"), bool_type()),
            (ustr("Int"), int_type()),
            (ustr("Float"), float_type()),
            (ustr("String"), string_type()),
            (ustr("Seq"), Type::new_local(0)),
        ]);
        store_types(&[seq, variant])[1]
    })
}

pub fn add_to_module(to: &mut Module) {
    // Types
    to.types.set("variant", script_variant_type());
}
