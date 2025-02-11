// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    containers::b,
    effects::EffType,
    error::RuntimeError,
    function::{Function, FunctionDefinition, UnaryNativeFnNV, UnaryNativeFnVFN},
    module::Module,
    r#trait::TraitRef,
    r#type::{FnType, Type},
    std::{
        logic::bool_type,
        math::{float_type, int_type},
        string::string_type,
    },
    value::Value,
};
use ustr::ustr;

use super::{
    array::Array,
    math::{Float, Int},
    string::String as Str,
    variant::script_variant_type,
};

pub const SERIALIZE_TRAIT_NAME: &str = "Serialize";
pub const DESERIALIZE_TRAIT_NAME: &str = "Deserialize";

fn serialize_unit(_u: ()) -> Value {
    Value::variant(ustr("None"), Value::unit())
}

fn deserialize_unit(variant: Value) -> Result<(), RuntimeError> {
    let variant = variant.into_variant().unwrap();
    match &*variant.tag {
        "None" => Ok(()),
        "Seq" => {
            let seq = variant.value.into_primitive_ty::<Array>().unwrap();
            if seq.is_empty() {
                Ok(())
            } else {
                Err(RuntimeError::InvalidArgument(
                    "Expected array of size 0".into(),
                ))
            }
        }
        _ => Err(RuntimeError::InvalidArgument(
            "Expected None variant or Seq variant of size 0".into(),
        )),
    }
}

fn serialize_bool(value: bool) -> Value {
    Value::variant(ustr("Bool"), Value::native(value))
}

fn deserialize_bool(variant: Value) -> Result<bool, RuntimeError> {
    let variant = variant.into_variant().unwrap();
    match &*variant.tag {
        "Bool" => Ok(variant.value.into_primitive_ty::<bool>().unwrap()),
        _ => Err(RuntimeError::InvalidArgument(
            "Expected Bool variant".into(),
        )),
    }
}

fn serialize_int(value: Int) -> Value {
    Value::variant(ustr("Int"), Value::native(value))
}

fn deserialize_int(variant: Value) -> Result<Int, RuntimeError> {
    let variant = variant.into_variant().unwrap();
    match &*variant.tag {
        "Int" => Ok(variant.value.into_primitive_ty::<Int>().unwrap()),
        _ => Err(RuntimeError::InvalidArgument("Expected Int variant".into())),
    }
}

fn serialize_float(value: Float) -> Value {
    Value::variant(ustr("Float"), Value::native(value))
}

fn deserialize_float(variant: Value) -> Result<Float, RuntimeError> {
    let variant = variant.into_variant().unwrap();
    match &*variant.tag {
        "Int" => Ok(Float::new(variant.value.into_primitive_ty::<Int>().unwrap() as f64).unwrap()),
        "Float" => Ok(variant.value.into_primitive_ty::<Float>().unwrap()),
        _ => Err(RuntimeError::InvalidArgument(
            "Expected Float or Int variants".into(),
        )),
    }
}

fn serialize_string(value: Str) -> Value {
    Value::variant(ustr("String"), Value::native(value))
}

fn deserialize_string(variant: Value) -> Result<Str, RuntimeError> {
    let variant = variant.into_variant().unwrap();
    match &*variant.tag {
        "String" => Ok(variant.value.into_primitive_ty::<Str>().unwrap()),
        _ => Err(RuntimeError::InvalidArgument(
            "Expected String variant".into(),
        )),
    }
}

pub fn add_to_module(to: &mut Module) {
    // Traits
    let var0_ty = Type::variable_id(0);
    use FunctionDefinition as Def;
    let serialize_trait = TraitRef::new(
        SERIALIZE_TRAIT_NAME,
        1,
        0,
        [(
            "serialize",
            Def::new_infer_quantifiers(
                FnType::new_by_val(&[var0_ty], script_variant_type(), EffType::empty()),
                &["value"],
                "Serialize this value into a variant.",
            ),
        )],
    );
    to.traits.push(serialize_trait.clone());
    let deserialize_trait = TraitRef::new(
        DESERIALIZE_TRAIT_NAME,
        1,
        0,
        [(
            "deserialize",
            Def::new_infer_quantifiers(
                FnType::new_by_val(&[script_variant_type()], var0_ty, EffType::empty()),
                &["variant"],
                "Deserialize a variant into a value of this type.",
            ),
        )],
    );
    to.traits.push(deserialize_trait.clone());

    // Trait implementations
    to.impls.add(
        serialize_trait.clone(),
        [Type::unit()],
        [],
        [b(UnaryNativeFnNV::new(serialize_unit)) as Function],
    );
    to.impls.add(
        deserialize_trait.clone(),
        [script_variant_type()],
        [],
        [b(UnaryNativeFnVFN::new(deserialize_unit)) as Function],
    );
    to.impls.add(
        serialize_trait.clone(),
        [bool_type()],
        [],
        [b(UnaryNativeFnNV::new(serialize_bool)) as Function],
    );
    to.impls.add(
        deserialize_trait.clone(),
        [bool_type()],
        [],
        [b(UnaryNativeFnVFN::new(deserialize_bool)) as Function],
    );
    to.impls.add(
        serialize_trait.clone(),
        [int_type()],
        [],
        [b(UnaryNativeFnNV::new(serialize_int)) as Function],
    );
    to.impls.add(
        deserialize_trait.clone(),
        [int_type()],
        [],
        [b(UnaryNativeFnVFN::new(deserialize_int)) as Function],
    );
    to.impls.add(
        serialize_trait.clone(),
        [float_type()],
        [],
        [b(UnaryNativeFnNV::new(serialize_float)) as Function],
    );
    to.impls.add(
        deserialize_trait.clone(),
        [float_type()],
        [],
        [b(UnaryNativeFnVFN::new(deserialize_float)) as Function],
    );
    to.impls.add(
        serialize_trait.clone(),
        [string_type()],
        [],
        [b(UnaryNativeFnNV::new(serialize_string)) as Function],
    );
    to.impls.add(
        deserialize_trait.clone(),
        [string_type()],
        [],
        [b(UnaryNativeFnVFN::new(deserialize_string)) as Function],
    );
}
