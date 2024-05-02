use std::{cell::RefCell, rc::Rc};

use ustr::ustr;

use crate::{
    function::{BinaryNativeFn, BinaryNativeFnVVP, UnaryNativeFn}, impl_bare_native_type, module::Module, r#type::Type, value::Value
};

pub fn bool_type() -> Type {
    Type::primitive::<bool>()
}

impl_bare_native_type!(bool);

impl_bare_native_type!(());

pub fn add_to_module(to: &mut Module) {
    // Types
    to.types.set(ustr("bool"), bool_type());

    // Operations on booleans
    to.functions.insert(
        ustr("@or"),
        Rc::new(RefCell::new(BinaryNativeFn::description(
            std::ops::BitOr::bitor as fn(bool, bool) -> bool,
        ))),
    );
    to.functions.insert(
        ustr("@and"),
        Rc::new(RefCell::new(BinaryNativeFn::description(
            std::ops::BitAnd::bitand as fn(bool, bool) -> bool,
        ))),
    );
    to.functions.insert(
        ustr("@not"),
        Rc::new(RefCell::new(UnaryNativeFn::description(
            std::ops::Not::not as fn(bool) -> bool,
        ))),
    );

    // Generic equalities and inequalities
    to.functions.insert(
        ustr("@=="),
        Rc::new(RefCell::new(BinaryNativeFnVVP::description(
            std::cmp::PartialEq::eq as fn(&Value, &Value) -> bool,
        ))),
    );
    to.functions.insert(
        ustr("@!="),
        Rc::new(RefCell::new(BinaryNativeFnVVP::description(
            std::cmp::PartialEq::ne as fn(&Value, &Value) -> bool,
        ))),
    );
}
