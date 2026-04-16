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
    std::logic::bool_type,
    r#trait::TraitRef,
    r#type::{FnType, Type},
};

use FunctionDefinition as Def;

pub static DEDUP_BY_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    TraitRef::new_with_self_input_type(
        "DedupBy",
        "A value that can remove consecutive duplicate elements using a custom equivalence relation.",
        ["Item", "Output"],
        [(
            "dedup_by",
            Def::new_infer_quantifiers(
                FnType::new_by_val(
                    [
                        Type::variable_id(0),
                        Type::function_by_val(
                            [Type::variable_id(1), Type::variable_id(1)],
                            bool_type(),
                        ),
                    ],
                    Type::variable_id(2),
                    EffType::empty(),
                ),
                ["value", "same"],
                "Removes consecutive elements of `value` for which `same` returns true.",
            ),
        )],
    )
});

pub fn add_to_module(to: &mut Module) {
    to.add_trait(DEDUP_BY_TRAIT.clone());
}
