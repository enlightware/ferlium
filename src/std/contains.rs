// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::sync::LazyLock;

use crate::{
    effects::EffType,
    function::FunctionDefinition,
    module::Module,
    std::logic::bool_type,
    r#trait::TraitRef,
    r#type::{FnType, Type},
};

use FunctionDefinition as Def;

pub static CONTAINS_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    let var0_ty = Type::variable_id(0);
    let var1_ty = Type::variable_id(1);
    let binary_fn_ty = FnType::new_by_val([var0_ty, var1_ty], bool_type(), EffType::empty());

    TraitRef::new_with_self_input_type(
        "Contains",
        "A type that can be checked for the presence of an element.",
        ["Element"],
        [(
            "contains",
            Def::new_infer_quantifiers(
                binary_fn_ty.clone(),
                ["container", "element"],
                "Returns true if `container` contains `element`.",
            ),
        )],
    )
});

pub fn add_to_module(to: &mut Module) {
    // Traits
    to.traits.push(CONTAINS_TRAIT.clone());
}
