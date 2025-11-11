// Copyright 2025 Enlightware GmbH
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
    effects::no_effects,
    function::{BinaryNativeFnNNN, BinaryNativeFnVVN, Function, UnaryNativeFnNN},
    module::Module,
    std::{bits::BITS_TRAIT, math::Int},
    r#type::Type,
    value::{NativeDisplay, Value},
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

pub fn add_to_module(to: &mut Module) {
    // Types
    to.type_aliases.set("bool", bool_type());

    // Operations on booleans
    use BinaryNativeFnNNN as BinaryFn;
    use UnaryNativeFnNN as UnaryFn;
    to.add_concrete_impl(
        BITS_TRAIT.clone(),
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
    to.add_named_function(
        ustr("not"),
        UnaryNativeFnNN::description_with_default_ty(
            std::ops::Not::not as fn(bool) -> bool,
            ["value"],
            "Performs a logical NOT operation.",
            no_effects(),
        ),
    );

    // Generic equalities
    to.add_named_function(
        ustr("eq"),
        BinaryNativeFnVVN::description_with_default_ty(
            |a: Value, b: Value| a == b,
            ["left", "right"],
            "Returns `true` if `left` is equal to `right`, otherwise `false`.",
            no_effects(),
        ),
    );
}
