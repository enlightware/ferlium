// Copyright 2026 Enlightware GmbH
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
    r#trait::TraitRef,
    r#type::{FnType, Type},
};

use FunctionDefinition as Def;

pub static CONCAT_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    let var_ty = Type::variable_id(0);
    let binary_fn_ty = FnType::new_by_val([var_ty, var_ty], var_ty, EffType::empty());

    TraitRef::new_with_self_input_type(
        "Concat",
        "A type that can be concatenated.",
        [],
        [(
            "concat",
            Def::new_infer_quantifiers(
                binary_fn_ty.clone(),
                ["left", "right"],
                "Concatenates `left` and `right`.",
            ),
        )],
    )
});

pub fn add_to_module(to: &mut Module) {
    // Traits
    to.add_trait(CONCAT_TRAIT.clone());
}
