use std::fmt;

use ustr::ustr;

use crate::{
    function::{BinaryNativeFn, BinaryNativeFnVVP, UnaryNativeFn},
    module::Module,
    r#type::Type,
    value::{NativeDisplay, Value},
};

pub fn bool_type() -> Type {
    Type::primitive::<bool>()
}

impl NativeDisplay for bool {
    fn native_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

pub fn unit_type() -> Type {
    Type::primitive::<()>()
}

impl NativeDisplay for () {
    fn native_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
        BinaryNativeFn::description(std::ops::BitOr::bitor as fn(bool, bool) -> bool),
    );
    to.functions.insert(
        ustr("@and"),
        BinaryNativeFn::description(std::ops::BitAnd::bitand as fn(bool, bool) -> bool),
    );
    to.functions.insert(
        ustr("@not"),
        UnaryNativeFn::description(std::ops::Not::not as fn(bool) -> bool),
    );

    // Generic equalities and inequalities
    to.functions.insert(
        ustr("@=="),
        BinaryNativeFnVVP::description_gen0_gen0(
            std::cmp::PartialEq::eq as fn(&Value, &Value) -> bool,
        ),
    );
    to.functions.insert(
        ustr("@!="),
        BinaryNativeFnVVP::description_gen0_gen0(
            std::cmp::PartialEq::ne as fn(&Value, &Value) -> bool,
        ),
    );
}
