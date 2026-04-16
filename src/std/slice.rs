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
    std::math::int_type,
    r#trait::TraitRef,
    r#type::{FnType, Type},
};

use FunctionDefinition as Def;

pub static SLICE_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    TraitRef::new_with_self_input_type(
        "Slice",
        "A sequence-like value that can extract a subrange.",
        ["Output"],
        [(
            "slice",
            Def::new_infer_quantifiers(
                FnType::new_by_val(
                    [Type::variable_id(0), int_type(), int_type()],
                    Type::variable_id(1),
                    EffType::empty(),
                ),
                ["value", "start", "end"],
                "Returns the slice of `value` from `start` to `end` (end-exclusive). Negative indices count from the end.",
            ),
        )],
    )
});

pub fn add_to_module(to: &mut Module) {
    to.add_trait(SLICE_TRAIT.clone());
}
