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
    effects::{PrimitiveEffect, effect},
    function::FunctionDefinition,
    module::Module,
    std::ordering::ordering_type,
    r#trait::TraitRef,
    r#type::{FnType, Type},
};

use FunctionDefinition as Def;

pub static SORT_BY_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    TraitRef::new_with_self_input_type(
        "SortBy",
        "A value that can be sorted with a custom comparator.",
        ["Item", "Output"],
        [(
            "sort_by",
            Def::new_infer_quantifiers(
                FnType::new_by_val(
                    [
                        Type::variable_id(0),
                        Type::function_by_val(
                            [Type::variable_id(1), Type::variable_id(1)],
                            ordering_type(),
                        ),
                    ],
                    Type::variable_id(2),
                    effect(PrimitiveEffect::Fallible),
                ),
                ["value", "compare"],
                "Returns a stable sort of `value` using `compare`.",
            ),
        )],
    )
});

pub fn add_to_module(to: &mut Module) {
    to.add_trait(SORT_BY_TRAIT.clone());
}
