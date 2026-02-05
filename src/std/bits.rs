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
    std::{logic::bool_type, math::int_type},
    r#trait::TraitRef,
    r#type::{FnType, Type},
};

use FunctionDefinition as Def;

pub static BITS_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    let var0_ty = Type::variable_id(0);
    let unary_fn_ty = FnType::new_by_val([var0_ty], var0_ty, EffType::empty());
    let unary_ret_int_fn_ty = FnType::new_by_val([var0_ty], int_type(), EffType::empty());
    let unary_int_ret_self_fn_ty = FnType::new_by_val([int_type()], var0_ty, EffType::empty());
    let binary_fn_ty = FnType::new_by_val([var0_ty, var0_ty], var0_ty, EffType::empty());
    let binary_self_int_fn_ty =
        FnType::new_by_val([var0_ty, int_type()], var0_ty, EffType::empty());
    let binary_self_int_ret_bool_fn_ty =
        FnType::new_by_val([var0_ty, int_type()], bool_type(), EffType::empty());

    TraitRef::new_with_self_input_type(
        "Bits",
        "A type that has bitwise operations.",
        [],
        [
            (
                "bit_and",
                Def::new_infer_quantifiers(
                    binary_fn_ty.clone(),
                    ["left", "right"],
                    "Returns the bitwise AND of `left` and `right`.",
                ),
            ),
            (
                "bit_or",
                Def::new_infer_quantifiers(
                    binary_fn_ty.clone(),
                    ["left", "right"],
                    "Returns the bitwise OR of `left` and `right`.",
                ),
            ),
            (
                "bit_xor",
                Def::new_infer_quantifiers(
                    binary_fn_ty,
                    ["left", "right"],
                    "Returns the bitwise XOR of `left` and `right`.",
                ),
            ),
            (
                "bit_not",
                Def::new_infer_quantifiers(
                    unary_fn_ty,
                    ["value"],
                    "Returns the bitwise NOT of `value`.",
                ),
            ),
            (
                "shift_left",
                Def::new_infer_quantifiers(
                    binary_self_int_fn_ty.clone(),
                    ["value", "shift"],
                    "Returns `value` shifted left by `shift` bits.",
                ),
            ),
            (
                "shift_right",
                Def::new_infer_quantifiers(
                    binary_self_int_fn_ty.clone(),
                    ["value", "shift"],
                    "Returns `value` shifted right by `shift` bits.",
                ),
            ),
            (
                "rotate_left",
                Def::new_infer_quantifiers(
                    binary_self_int_fn_ty.clone(),
                    ["value", "rotate"],
                    "Returns `value` rotated left by `rotate` bits.",
                ),
            ),
            (
                "rotate_right",
                Def::new_infer_quantifiers(
                    binary_self_int_fn_ty.clone(),
                    ["value", "rotate"],
                    "Returns `value` rotated right by `rotate` bits.",
                ),
            ),
            (
                "count_ones",
                Def::new_infer_quantifiers(
                    unary_ret_int_fn_ty.clone(),
                    ["value"],
                    "Returns the number of one bits in `value`.",
                ),
            ),
            (
                "count_zeros",
                Def::new_infer_quantifiers(
                    unary_ret_int_fn_ty.clone(),
                    ["value"],
                    "Returns the number of zero bits in `value`.",
                ),
            ),
            (
                "bit",
                Def::new_infer_quantifiers(
                    unary_int_ret_self_fn_ty,
                    ["position"],
                    "Returns a value with only the bit at `position` set.",
                ),
            ),
            (
                "set_bit",
                Def::new_infer_quantifiers(
                    binary_self_int_fn_ty.clone(),
                    ["value", "position"],
                    "Returns `value` with the bit at `position` set to 1.",
                ),
            ),
            (
                "clear_bit",
                Def::new_infer_quantifiers(
                    binary_self_int_fn_ty,
                    ["value", "position"],
                    "Returns `value` with the bit at `position` cleared to 0.",
                ),
            ),
            (
                "test_bit",
                Def::new_infer_quantifiers(
                    binary_self_int_ret_bool_fn_ty,
                    ["value", "position"],
                    "Returns `true` if the bit at `position` in `value` is set, otherwise `false`.",
                ),
            ),
        ],
    )
});

pub fn add_to_module(to: &mut Module) {
    // Traits
    to.add_trait(BITS_TRAIT.clone());
}
