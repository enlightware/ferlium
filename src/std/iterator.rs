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
    std::{math::int_type, option::option_type},
    type_scheme::PubTypeConstraint,
    Location,
};

pub const ITERATOR_TRAIT_NAME: &str = "Iterator";
pub const SEQ_TRAIT_NAME: &str = "Seq";
pub const SIZED_SEQ_TRAIT_NAME: &str = "SizedSeq";

pub fn add_to_module(to: &mut Module) {
    // Traits
    use FunctionDefinition as Def;
    let iterator_trait = TraitRef::new(
        ITERATOR_TRAIT_NAME,
        1,
        1,
        [(
            "next",
            Def::new_infer_quantifiers(
                FnType::new_mut_resolved(
                    &[(Type::variable_id(0), true)],
                    option_type(Type::variable_id(1)),
                    EffType::empty(),
                ),
                &["iterator"],
                "Get the next element of the iterator, or None if the iterator is exhausted.",
            ),
        )],
    );
    to.traits.push(iterator_trait.clone());

    let iter_item_constraint = PubTypeConstraint::HaveTrait {
        trait_ref: iterator_trait,
        input_tys: vec![Type::variable_id(2)],
        output_tys: vec![Type::variable_id(1)],
        span: Location::new_local(0, 0), // FIXME: we should not have a location here.
    };
    let seq_trait = TraitRef::new_with_constraints(
        SEQ_TRAIT_NAME,
        1,
        2,
        [iter_item_constraint],
        [(
            "iter",
            Def::new_infer_quantifiers(
                FnType::new_by_val(
                    &[Type::variable_id(0)],
                    Type::variable_id(2),
                    EffType::empty(),
                ),
                &["seq"],
                "Get an iterator over the elements of this sequence.",
            ),
        )],
    );
    to.traits.push(seq_trait);

    let sized_seq_trait = TraitRef::new(
        SIZED_SEQ_TRAIT_NAME,
        1,
        0,
        [(
            "len",
            Def::new_infer_quantifiers(
                FnType::new_by_val(&[Type::variable_id(0)], int_type(), EffType::empty()),
                &["seq"],
                "Return the number of elements in this sequence.",
            ),
        )],
    );
    to.traits.push(sized_seq_trait);

    // Trait implementations are in the prelude.
}
