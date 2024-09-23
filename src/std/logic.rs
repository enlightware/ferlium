use std::fmt;

use ustr::ustr;

use crate::{
    cached_primitive_ty,
    effects::no_effects,
    function::{BinaryNativeFnNNI, BinaryNativeFnVVI, UnaryNativeFnNI},
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
        BinaryNativeFnNNI::description_with_default_ty(
            std::ops::BitOr::bitor as fn(bool, bool) -> bool,
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@and"),
        BinaryNativeFnNNI::description_with_default_ty(
            std::ops::BitAnd::bitand as fn(bool, bool) -> bool,
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@not"),
        UnaryNativeFnNI::description_with_default_ty(
            std::ops::Not::not as fn(bool) -> bool,
            no_effects(),
        ),
    );

    // Generic equalities and inequalities
    to.functions.insert(
        ustr("@=="),
        BinaryNativeFnVVI::description_with_default_ty(|a: Value, b: Value| a == b, no_effects()),
    );
    to.functions.insert(
        ustr("@!="),
        BinaryNativeFnVVI::description_with_default_ty(|a: Value, b: Value| a != b, no_effects()),
    );
}
