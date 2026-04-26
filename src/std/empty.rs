// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

use std::sync::LazyLock;

use crate::{
    hir::function::FunctionDefinition,
    module::Module,
    std::{STD_MODULE_ID, product_value_deriver::ProductValueDeriver},
    types::effects::EffType,
    types::r#trait::TraitRef,
    types::r#type::{FnType, Type},
};

use FunctionDefinition as Def;

pub static EMPTY_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    let var_ty = Type::variable_id(0);
    let trait_ref = TraitRef::new_with_self_input_type(
        "Empty",
        "A type with a canonical empty value, typically used as the identity for concatenation.",
        [],
        [(
            "empty",
            Def::new_infer_quantifiers(
                FnType::new_by_val([], var_ty, EffType::empty()),
                [],
                "Returns the empty value for this type.",
            ),
        )],
    );
    trait_ref.with_module_id_and_deriver(STD_MODULE_ID, ProductValueDeriver)
});

pub fn add_to_module(to: &mut Module) {
    to.add_trait(EMPTY_TRAIT.clone());
}
