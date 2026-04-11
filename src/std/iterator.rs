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
    location::InstantiableLocation,
    module::Module,
    std::{logic::bool_type, math::int_type, option::option_type},
    r#trait::TraitRef,
    r#type::{FnType, Type},
    type_scheme::PubTypeConstraint,
};

pub const ITERATOR_TRAIT_NAME: &str = "Iterator";
pub const SEQ_TRAIT_NAME: &str = "Seq";
pub const FROM_ITERATOR_TRAIT_NAME: &str = "FromIterator";
pub const REBIND_ITEM_TRAIT_NAME: &str = "RebindItem";
pub const MAP_TRAIT_NAME: &str = "Map";
pub const FILTER_TRAIT_NAME: &str = "Filter";
pub const FILTER_MAP_TRAIT_NAME: &str = "FilterMap";
pub const SIZED_SEQ_TRAIT_NAME: &str = "SizedSeq";

pub static ITERATOR_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    use FunctionDefinition as Def;
    TraitRef::new_with_self_input_type(
        ITERATOR_TRAIT_NAME,
        "An iterator that can produce a sequence of values.",
        ["Item"],
        [(
            "next",
            Def::new_infer_quantifiers(
                FnType::new_mut_resolved(
                    [(Type::variable_id(0), true)],
                    option_type(Type::variable_id(1)),
                    EffType::empty(),
                ),
                ["iterator"],
                "Get the next element of the iterator, or None if the iterator is exhausted.",
            ),
        )],
    )
});

pub fn add_to_module(to: &mut Module) {
    // Traits
    use FunctionDefinition as Def;
    let iterator_trait = ITERATOR_TRAIT.clone();
    to.add_trait(iterator_trait.clone());

    let iter_item_constraint = PubTypeConstraint::HaveTrait {
        trait_ref: iterator_trait.clone(),
        input_tys: vec![Type::variable_id(2)],
        output_tys: vec![Type::variable_id(1)],
        span: InstantiableLocation::new_synthesized(),
    };
    let seq_trait = TraitRef::new_with_constraints(
        SEQ_TRAIT_NAME,
        "A sequence of elements that can produce an iterator over its elements.",
        ["Self"],
        ["Item", "Iter"],
        [iter_item_constraint.clone()],
        [(
            "iter",
            Def::new_infer_quantifiers(
                FnType::new_by_val(
                    [Type::variable_id(0)],
                    Type::variable_id(2),
                    EffType::empty(),
                ),
                ["seq"],
                "Get an iterator over the elements of this sequence.",
            ),
        )],
    );
    to.add_trait(seq_trait.clone());

    let from_iter_trait = TraitRef::new(
        FROM_ITERATOR_TRAIT_NAME,
        "A collection that can be built from an iterator.",
        ["Self", "Iter"],
        [],
        [(
            "from_iter",
            Def::new_infer_quantifiers(
                FnType::new_by_val(
                    [Type::variable_id(1)],
                    Type::variable_id(0),
                    EffType::empty(),
                ),
                ["iterator"],
                "Create a collection from an iterator.",
            ),
        )],
    );
    to.add_trait(from_iter_trait);

    let rebind_item_trait = TraitRef::new(
        REBIND_ITEM_TRAIT_NAME,
        "Relates a collection family to the collection obtained by replacing its element type.",
        ["Self", "Item"],
        ["Output"],
        Vec::<(&str, FunctionDefinition)>::new(),
    );
    to.add_trait(rebind_item_trait);

    let map_trait = TraitRef::new(
        MAP_TRAIT_NAME,
        "Maps a function over a value, producing either a lazy iterator adaptor or an eagerly rebuilt collection depending on the input type.",
        ["Self", "Mapped"],
        ["Item", "Output"],
        [(
            "map",
            Def::new_infer_quantifiers(
                FnType::new_by_val(
                    [
                        Type::variable_id(0),
                        Type::function_by_val([Type::variable_id(2)], Type::variable_id(1)),
                    ],
                    Type::variable_id(3),
                    EffType::empty(),
                ),
                ["value", "mapper"],
                "Map `mapper` over `value`.",
            ),
        )],
    );
    to.add_trait(map_trait);

    let filter_trait = TraitRef::new(
        FILTER_TRAIT_NAME,
        "Filters a value with a predicate, producing either a lazy iterator adaptor or an eagerly rebuilt collection depending on the input type.",
        ["Self"],
        ["Item", "Output"],
        [(
            "filter",
            Def::new_infer_quantifiers(
                FnType::new_by_val(
                    [
                        Type::variable_id(0),
                        Type::function_by_val([Type::variable_id(1)], bool_type()),
                    ],
                    Type::variable_id(2),
                    EffType::empty(),
                ),
                ["value", "predicate"],
                "Keep only the elements of `value` that satisfy `predicate`.",
            ),
        )],
    );
    to.add_trait(filter_trait);

    let filter_map_trait = TraitRef::new(
        FILTER_MAP_TRAIT_NAME,
        "Filters and maps a value in one pass, producing either a lazy iterator adaptor or an eagerly rebuilt collection depending on the input type.",
        ["Self", "Mapped"],
        ["Item", "Output"],
        [(
            "filter_map",
            Def::new_infer_quantifiers(
                FnType::new_by_val(
                    [
                        Type::variable_id(0),
                        Type::function_by_val(
                            [Type::variable_id(2)],
                            option_type(Type::variable_id(1)),
                        ),
                    ],
                    Type::variable_id(3),
                    EffType::empty(),
                ),
                ["value", "mapper"],
                "Apply `mapper` to each element, keeping only `Some` results.",
            ),
        )],
    );
    to.add_trait(filter_map_trait);

    let sized_seq_trait = TraitRef::new_with_self_input_type(
        SIZED_SEQ_TRAIT_NAME,
        "A sequence with a known, fixed size.",
        [],
        [(
            "len",
            Def::new_infer_quantifiers(
                FnType::new_by_val([Type::variable_id(0)], int_type(), EffType::empty()),
                ["seq"],
                "Return the number of elements in this sequence.",
            ),
        )],
    );
    to.add_trait(sized_seq_trait);

    // Trait implementations are in the prelude.
}
