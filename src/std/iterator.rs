// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    containers::b,
    effects::EffType,
    function::{BinaryNativeFnVVV, FunctionDefinition},
    location::InstantiableLocation,
    module::{BlanketTraitImplSubKey, Module},
    std::{math::int_type, option::option_type},
    r#trait::TraitRef,
    r#type::{FnType, Type},
    type_scheme::PubTypeConstraint,
    value::Value,
};

pub const ITERATOR_TRAIT_NAME: &str = "Iterator";
pub const SEQ_TRAIT_NAME: &str = "Seq";
pub const FROM_ITERATOR_TRAIT_NAME: &str = "FromIterator";
pub const SIZED_SEQ_TRAIT_NAME: &str = "SizedSeq";

pub fn add_to_module(to: &mut Module) {
    // Traits
    use FunctionDefinition as Def;
    let iterator_trait = TraitRef::new_with_self_input_type(
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
    );
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

    // Requires per trait method generics
    // let from_iter_trait = TraitRef::new_with_constraints(
    //     FROM_ITERATOR_TRAIT_NAME,
    //     1,
    //     0,
    //     [iter_item_constraint],
    //     [(
    //         "from_iter",
    //         Def::new_infer_quantifiers(
    //             FnType::new_by_val(
    //                 &[Type::variable_id(2)],
    //                 Type::variable_id(0),
    //                 EffType::empty(),
    //             ),
    //             &["iterator"],
    //             "Create a sequence from an iterator.",
    //         ),
    //     )],
    // );
    // to.traits.push(from_iter_trait);

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

    // Implementation of Seq trait for Iterator
    // TODO: implement in Ferlium itself once we have constraint parsing in blanket implementations.
    to.add_blanket_impl(
        seq_trait,
        BlanketTraitImplSubKey {
            input_tys: vec![Type::variable_id(0)],
            ty_var_count: 2,
            constraints: vec![PubTypeConstraint::HaveTrait {
                trait_ref: iterator_trait,
                input_tys: vec![Type::variable_id(0)],
                output_tys: vec![Type::variable_id(1)],
                span: InstantiableLocation::new_synthesized(),
            }],
        },
        vec![Type::variable_id(1), Type::variable_id(0)],
        vec![
            // As we have one HaveTrait constraint, we need to add one extra argument
            // for the constraint dictionary, even if it is not used.
            b(BinaryNativeFnVVV::new(|_dict: Value, v: Value| v))
                as Box<dyn crate::function::Callable>,
        ],
    );

    // Trait implementations are in the prelude.
}
