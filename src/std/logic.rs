// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::fmt;

use ustr::ustr;

use crate::{
    cached_primitive_ty,
    effects::no_effects,
    function::{BinaryNativeFnNNN, BinaryNativeFnVVN, UnaryNativeFnNN},
    module::Module,
    r#type::Type,
    value::{NativeDisplay, Value},
};

pub fn bool_type() -> Type {
    cached_primitive_ty!(bool)
}

impl NativeDisplay for bool {
    fn fmt_as_literal(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

pub fn add_to_module(to: &mut Module) {
    // Types
    to.type_aliases.set("bool", bool_type());

    // Operations on booleans
    to.add_named_function(
        ustr("bitor"),
        BinaryNativeFnNNN::description_with_default_ty(
            std::ops::BitOr::bitor as fn(bool, bool) -> bool,
            ["left", "right"],
            None,
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("bitand"),
        BinaryNativeFnNNN::description_with_default_ty(
            std::ops::BitAnd::bitand as fn(bool, bool) -> bool,
            ["left", "right"],
            None,
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("not"),
        UnaryNativeFnNN::description_with_default_ty(
            std::ops::Not::not as fn(bool) -> bool,
            ["value"],
            None,
            no_effects(),
        ),
    );

    // Generic equalities
    to.add_named_function(
        ustr("eq"),
        BinaryNativeFnVVN::description_with_default_ty(
            |a: Value, b: Value| a == b,
            ["left", "right"],
            None,
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("ne"),
        BinaryNativeFnVVN::description_with_default_ty(
            |a: Value, b: Value| a != b,
            ["left", "right"],
            None,
            no_effects(),
        ),
    );
}
