// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    effects::EffType,
    function::FunctionDefinition,
    module::Module,
    r#trait::TraitRef,
    r#type::{FnType, Type},
};

use super::variant::script_variant_type;

pub const SERIALIZE_TRAIT_NAME: &str = "Serialize";
pub const DESERIALIZE_TRAIT_NAME: &str = "Deserialize";

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

    // Trait implementations are in the prelude.
}
