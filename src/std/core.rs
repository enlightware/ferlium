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
    hir::function::{
        BinaryNativeFnNMN, BinaryNativeFnNNN, Function, NullaryNativeFnN, UnaryNativeFnNN,
    },
    module::Module,
    std::{
        core_traits_names::{
            DEFAULT_TRAIT_NAME, INSPECT_TRAIT_NAME, REPR_TRAIT_NAME, TRIVIAL_COPY_TRAIT_NAME,
            VALUE_TRAIT_NAME,
        },
        hash::Hasher,
        logic::bool_type,
        math::{float_type, int_type},
        string::string_type,
        value::{
            native_layout_associated_consts, native_value_clone_function,
            native_value_drop_function,
        },
    },
    types::r#trait::Trait,
    types::r#type::Type,
};

fn repr_trait() -> Trait {
    Trait::new_with_self_input_type(
        "Repr",
        "Marker trait for types whose value is the same representation as one of another type. Used in Rust-style struct and enums (new types) to allow matches and projections on the underlying representation.",
        ["Is"],
        [],
    )
}

fn trivial_copy_trait() -> Trait {
    Trait::new_with_self_input_type(
        "TrivialCopy",
        "Marker trait for trusted native types that native adapters may pass by value.",
        [],
        [],
    )
    .with_native_impl_only()
}

fn unit_to_string(_: ()) -> crate::std::string::String {
    crate::std::string::String::new("()")
}

fn unit_hash(_: (), _: &mut Hasher) {}

pub fn add_to_module(to: &mut Module) {
    // Add aliases for basic types
    to.add_type_alias_str_with_doc(
        "()",
        Type::unit(),
        "The unit type. It has exactly one value: ().",
    );
    to.add_type_alias_str_with_doc("bool", bool_type(), "A Boolean value: true or false.");
    to.add_type_alias_str_with_doc("int", int_type(), "A signed machine-sized integer.");
    to.add_type_alias_str_with_doc(
        "float",
        float_type(),
        "A finite 64-bit floating-point number.",
    );
    to.add_type_alias_str_with_doc("string", string_type(), "An owned UTF-8 string.");

    // Add the `Repr` trait
    let repr_trait_id = to.add_trait(repr_trait());
    let trivial_copy_trait_id = to.add_trait(trivial_copy_trait());
    let repr_trait_id = crate::module::TraitId::new(to.module_id(), repr_trait_id);
    let trivial_copy_trait_id = crate::module::TraitId::new(to.module_id(), trivial_copy_trait_id);
    debug_assert_eq!(to.trait_def(repr_trait_id).name, REPR_TRAIT_NAME);
    debug_assert_eq!(
        to.trait_def(trivial_copy_trait_id).name,
        TRIVIAL_COPY_TRAIT_NAME
    );
    let value_trait_id = to.expect_std_trait_id_in_current_module(VALUE_TRAIT_NAME);
    let inspect_trait_id = to.expect_std_trait_id_in_current_module(INSPECT_TRAIT_NAME);

    to.add_concrete_impl_no_locals(
        value_trait_id,
        [Type::unit()],
        [],
        native_layout_associated_consts::<()>(),
        [
            b(BinaryNativeFnNNN::new(|_: (), _: ()| true)) as Function,
            b(UnaryNativeFnNN::new(unit_to_string)) as Function,
            b(BinaryNativeFnNMN::new(unit_hash)) as Function,
            native_value_clone_function::<()>(),
            native_value_drop_function::<()>(),
        ],
    );
    to.add_concrete_impl_no_locals(
        inspect_trait_id,
        [Type::unit()],
        [],
        [],
        [b(UnaryNativeFnNN::new(unit_to_string)) as Function],
    );
    let default_trait_id = to.expect_std_trait_id_in_current_module(DEFAULT_TRAIT_NAME);
    to.add_native_concrete_impl(
        default_trait_id,
        [Type::unit()],
        [],
        [b(NullaryNativeFnN::new(|| ())) as Function],
    );
    to.add_native_concrete_impl(
        trivial_copy_trait_id,
        [Type::unit()],
        [],
        Vec::<Function>::new(),
    );

    // All types implement `Repr` to themselves, but to avoid overlapping
    // blanket implementations, this is implemented manually in the code.
    // let ty_var0 = Type::variable_id(0);
    // to.impls.add_blanket(coercible_trait, [ty_var0], [ty_var0], 1, [], []);
}
