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
    effects::effect,
    function::FunctionDefinition,
    module::Module,
    r#trait::TraitRef,
    r#type::{FnType, Type},
};

use FunctionDefinition as Def;

pub static REVERSE_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    TraitRef::new_with_self_input_type(
        "Reverse",
        "A value that can be reversed in place.",
        [],
        [(
            "reverse",
            Def::new_infer_quantifiers(
                FnType::new_mut_resolved(
                    [(Type::variable_id(0), true)],
                    Type::unit(),
                    effect(crate::effects::PrimitiveEffect::Fallible),
                ),
                ["value"],
                "Reverses `value` in place.",
            ),
        )],
    )
});

pub fn add_to_module(to: &mut Module) {
    to.add_trait(REVERSE_TRAIT.clone());
}
