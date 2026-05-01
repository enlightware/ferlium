// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{convert::identity, fmt, ops};

use ustr::ustr;

use crate::{
    cached_primitive_ty,
    containers::b,
    hir::function::{
        BinaryNativeFnNMN, BinaryNativeFnNNN, Function, NullaryNativeFnN, UnaryNativeFnNN,
    },
    hir::value::NativeDisplay,
    module::Module,
    std::{
        core::TRIVIAL_COPY_TRAIT,
        core_traits_names::BITS_TRAIT_NAME,
        default::DEFAULT_TRAIT,
        hash::Hasher,
        math::Int,
        string::String,
        value::{VALUE_TRAIT, equal},
    },
    types::effects::no_effects,
    types::r#type::Type,
};

pub fn bool_type() -> Type {
    cached_primitive_ty!(bool)
}

impl NativeDisplay for bool {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

fn false_value(_: bool) -> bool {
    false
}

fn count_ones(value: bool) -> Int {
    if value { 1 } else { 0 }
}

fn count_zeros(value: bool) -> Int {
    if value { 0 } else { 1 }
}

fn bit(position: Int) -> bool {
    position == 0
}

fn set_bit(value: bool, position: Int) -> bool {
    if position == 0 { true } else { value }
}

fn clear_bit(value: bool, position: Int) -> bool {
    if position == 0 { false } else { value }
}

fn test_bit(value: bool, position: Int) -> bool {
    if position == 0 { value } else { false }
}

fn hash_bool(value: bool, state: &mut Hasher) {
    state.write_bool(value);
}

pub fn add_to_module(to: &mut Module) {
    // Types
    // Note: bool alias is added in core.rs

    // Operations on booleans
    use BinaryNativeFnNNN as BinaryFn;
    use UnaryNativeFnNN as UnaryFn;
    to.add_concrete_impl_no_locals(
        VALUE_TRAIT.clone(),
        [bool_type()],
        [],
        [
            b(BinaryFn::new(equal::<bool>)) as Function,
            b(UnaryFn::new(|value: bool| String::new(&value.to_string()))) as Function,
            b(BinaryNativeFnNMN::new(hash_bool)) as Function,
        ],
    );
    let bits_trait = to.get_trait_str(BITS_TRAIT_NAME).unwrap().clone();
    to.add_concrete_impl_no_locals(
        bits_trait,
        [bool_type()],
        [],
        [
            b(BinaryFn::new(<bool as ops::BitAnd>::bitand)) as Function,
            b(BinaryFn::new(<bool as ops::BitOr>::bitor)) as Function,
            b(BinaryFn::new(<bool as ops::BitXor>::bitxor)) as Function,
            b(UnaryFn::new(<bool as ops::Not>::not)) as Function,
            b(UnaryFn::new(false_value)) as Function,
            b(UnaryFn::new(false_value)) as Function,
            b(UnaryFn::new(identity::<bool>)) as Function,
            b(UnaryFn::new(identity::<bool>)) as Function,
            b(UnaryFn::new(count_ones)) as Function,
            b(UnaryFn::new(count_zeros)) as Function,
            b(UnaryFn::new(bit)) as Function,
            b(BinaryFn::new(set_bit)) as Function,
            b(BinaryFn::new(clear_bit)) as Function,
            b(BinaryFn::new(test_bit)) as Function,
        ],
    );
    to.add_concrete_impl_no_locals(
        DEFAULT_TRAIT.clone(),
        [bool_type()],
        [],
        [b(NullaryNativeFnN::new(|| false)) as Function],
    );
    to.add_concrete_impl_no_locals(
        TRIVIAL_COPY_TRAIT.clone(),
        [bool_type()],
        [],
        Vec::<Function>::new(),
    );
    to.add_function(
        ustr("not"),
        UnaryNativeFnNN::description_with_default_ty(
            std::ops::Not::not as fn(bool) -> bool,
            ["value"],
            "Performs a logical NOT operation.",
            no_effects(),
        ),
    );
}
