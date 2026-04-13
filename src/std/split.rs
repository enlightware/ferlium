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
    location::InstantiableLocation,
    module::Module,
    std::iterator::ITERATOR_TRAIT,
    r#trait::TraitRef,
    r#type::{FnType, Type},
    type_scheme::PubTypeConstraint,
};

use FunctionDefinition as Def;

pub static SPLIT_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    // Variable IDs: Self=0, Separator=1, Part=2, Iter=3, Output=4
    let iter_part_constraint = PubTypeConstraint::HaveTrait {
        trait_ref: ITERATOR_TRAIT.clone(),
        input_tys: vec![Type::variable_id(3)],
        output_tys: vec![Type::variable_id(2)],
        span: InstantiableLocation::new_synthesized(),
    };

    TraitRef::new_with_constraints(
        "Split",
        "A type that can be split around a non-empty separator, yielding parts lazily.",
        ["Self", "Separator"],
        ["Part", "Iter", "Output"],
        [iter_part_constraint],
        [(
            "split_iterator",
            Def::new_infer_quantifiers(
                FnType::new_by_val(
                    [Type::variable_id(0), Type::variable_id(1)],
                    Type::variable_id(3),
                    effect(PrimitiveEffect::Fallible),
                ),
                ["value", "separator"],
                "Returns an iterator over the parts of `value` separated by `separator`.",
            ),
        )],
    )
});

pub fn add_to_module(to: &mut Module) {
    to.add_trait(SPLIT_TRAIT.clone());
}
