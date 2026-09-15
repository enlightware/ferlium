// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::fmt;

use ustr::ustr;

use crate::{
    cached_primitive_ty,
    containers::b,
    hir::function::Function,
    hir::native_functions::{
        NativeFallibleOutFnN, NativeFn0, NativeFnN, NativeFnNM, NativeFnNN, NativeOutFnN,
    },
    hir::value::NativeDisplay,
    module::Module,
    std::{
        core_traits_names::{
            BITS_TRAIT_NAME, DEFAULT_TRAIT_NAME, INSPECT_TRAIT_NAME, TRIVIAL_COPY_TRAIT_NAME,
            VALUE_TRAIT_NAME,
        },
        hash::Hasher,
        math::Int,
        string::String,
        value::{
            equal, native_layout_associated_consts, native_value_clone_function,
            native_value_drop_function,
        },
    },
    types::effects::no_effects,
    types::r#type::Type,
};

pub fn bool_type() -> Type {
    cached_primitive_ty!(bool)
}

extern "C" fn not_bool(value: bool) -> bool {
    !value
}

impl NativeDisplay for bool {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

extern "C" fn false_with_int(_: bool, _: Int) -> bool {
    false
}

extern "C" fn identity_with_int(value: bool, _: Int) -> bool {
    value
}

extern "C" fn count_ones(value: bool) -> Int {
    if value { 1 } else { 0 }
}

extern "C" fn count_zeros(value: bool) -> Int {
    if value { 0 } else { 1 }
}

extern "C" fn bit(position: Int) -> bool {
    position == 0
}

extern "C" fn set_bit(value: bool, position: Int) -> bool {
    if position == 0 { true } else { value }
}

extern "C" fn clear_bit(value: bool, position: Int) -> bool {
    if position == 0 { false } else { value }
}

extern "C" fn test_bit(value: bool, position: Int) -> bool {
    if position == 0 { value } else { false }
}

extern "C" fn hash_bool(value: bool, state: &mut Hasher) {
    state.write_bool(value);
}

fn bool_to_string(value: bool) -> String {
    String::new(&value.to_string())
}

pub fn add_to_module(to: &mut Module) {
    let value_trait_id = to.expect_std_trait_id_in_current_module(VALUE_TRAIT_NAME);
    let inspect_trait_id = to.expect_std_trait_id_in_current_module(INSPECT_TRAIT_NAME);
    let bits_trait_id = to.expect_std_trait_id_in_current_module(BITS_TRAIT_NAME);
    let default_trait_id = to.expect_std_trait_id_in_current_module(DEFAULT_TRAIT_NAME);
    let trivial_copy_trait_id = to.expect_std_trait_id_in_current_module(TRIVIAL_COPY_TRAIT_NAME);
    // Types
    // Note: bool alias is added in core.rs

    // Operations on booleans
    to.add_concrete_impl_no_locals(
        value_trait_id,
        [bool_type()],
        [],
        native_layout_associated_consts::<bool>(),
        [
            b(NativeFnNN::new(equal::<bool>)) as Function,
            b(NativeOutFnN::from_rust(bool_to_string)) as Function,
            b(NativeFnNM::new(hash_bool)) as Function,
            native_value_clone_function::<bool>(),
            native_value_drop_function::<bool>(),
        ],
    );
    to.add_concrete_impl_no_locals(
        inspect_trait_id,
        [bool_type()],
        [],
        [],
        [b(NativeFallibleOutFnN::from_rust_infallible(bool_to_string)) as Function],
    );
    to.add_native_concrete_impl(
        bits_trait_id,
        [bool_type()],
        [],
        [
            b(NativeFnNN::from_rust(<bool as std::ops::BitAnd>::bitand)) as Function,
            b(NativeFnNN::from_rust(<bool as std::ops::BitOr>::bitor)) as Function,
            b(NativeFnNN::from_rust(<bool as std::ops::BitXor>::bitxor)) as Function,
            b(NativeFnN::new(not_bool)) as Function,
            b(NativeFnNN::new(false_with_int)) as Function,
            b(NativeFnNN::new(false_with_int)) as Function,
            b(NativeFnNN::new(identity_with_int)) as Function,
            b(NativeFnNN::new(identity_with_int)) as Function,
            b(NativeFnN::new(count_ones)) as Function,
            b(NativeFnN::new(count_zeros)) as Function,
            b(NativeFnN::new(bit)) as Function,
            b(NativeFnNN::new(set_bit)) as Function,
            b(NativeFnNN::new(clear_bit)) as Function,
            b(NativeFnNN::new(test_bit)) as Function,
        ],
    );
    to.add_native_concrete_impl(
        default_trait_id,
        [bool_type()],
        [],
        [b(NativeFn0::from_rust(|| false)) as Function],
    );
    to.add_native_concrete_impl(
        trivial_copy_trait_id,
        [bool_type()],
        [],
        Vec::<Function>::new(),
    );
    to.add_function(
        ustr("not"),
        NativeFnN::new(not_bool).description(
            ["value"],
            "Performs a logical NOT operation.",
            no_effects(),
        ),
    );
}
