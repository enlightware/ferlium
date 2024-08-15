use std::fmt;

use ustr::ustr;

use crate::{
    function::{BinaryNativeFnNNI, BinaryNativeFnVVI, UnaryNativeFnNI},
    module::Module,
    r#type::Type,
    value::{NativeDisplay, Value},
};

pub fn bool_type() -> Type {
    Type::primitive::<bool>()
}

impl NativeDisplay for bool {
    fn fmt_as_literal(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

pub fn unit_type() -> Type {
    Type::primitive::<()>()
}

impl NativeDisplay for () {
    fn fmt_as_literal(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "()")
    }
}

pub fn add_to_module(to: &mut Module) {
    // Types
    to.types.set(ustr("bool"), bool_type());
    to.types.set(ustr("()"), unit_type());

    // Operations on booleans
    to.functions.insert(
        ustr("@or"),
        BinaryNativeFnNNI::description_with_default_ty(
            std::ops::BitOr::bitor as fn(bool, bool) -> bool,
        ),
    );
    to.functions.insert(
        ustr("@and"),
        BinaryNativeFnNNI::description_with_default_ty(
            std::ops::BitAnd::bitand as fn(bool, bool) -> bool,
        ),
    );
    to.functions.insert(
        ustr("@not"),
        UnaryNativeFnNI::description_with_default_ty(std::ops::Not::not as fn(bool) -> bool),
    );

    // Generic equalities and inequalities
    to.functions.insert(
        ustr("@=="),
        BinaryNativeFnVVI::description_with_default_ty(|a: Value, b: Value| a == b),
    );
    to.functions.insert(
        ustr("@!="),
        BinaryNativeFnVVI::description_with_default_ty(|a: Value, b: Value| a != b),
    );
}
