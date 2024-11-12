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
    to.types.set(ustr("bool"), bool_type());

    // Operations on booleans
    to.functions.insert(
        ustr("@or"),
        BinaryNativeFnNNN::description_with_default_ty(
            std::ops::BitOr::bitor as fn(bool, bool) -> bool,
            ["left", "right"],
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@and"),
        BinaryNativeFnNNN::description_with_default_ty(
            std::ops::BitAnd::bitand as fn(bool, bool) -> bool,
            ["left", "right"],
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@not"),
        UnaryNativeFnNN::description_with_default_ty(
            std::ops::Not::not as fn(bool) -> bool,
            ["value"],
            no_effects(),
        ),
    );

    // Generic equalities and inequalities
    to.functions.insert(
        ustr("@=="),
        BinaryNativeFnVVN::description_with_default_ty(
            |a: Value, b: Value| a == b,
            ["left", "right"],
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@!="),
        BinaryNativeFnVVN::description_with_default_ty(
            |a: Value, b: Value| a != b,
            ["left", "right"],
            no_effects(),
        ),
    );
}
