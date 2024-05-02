use std::{cell::RefCell, rc::Rc};

use ordered_float::NotNan;
use ustr::ustr;

use crate::{
    error::RuntimeError, function::{BinaryNativeFn, TryBinaryNativeFn, UnaryNativeFn}, impl_bare_native_type, module::Module, r#type::Type
};

pub fn int_type() -> Type {
    Type::primitive::<isize>()
}

impl_bare_native_type!(isize);

pub fn float_type() -> Type {
    Type::primitive::<NotNan<f64>>()
}

impl_bare_native_type!(NotNan<f64>);

pub fn add_to_module(to: &mut Module) {
    use RuntimeError::*;

    // Types
    to.types.set(ustr("int"), int_type());
    to.types.set(ustr("float"), float_type());

    // TODO: use type classes to support floats
    // Computations
    to.functions.insert(
        ustr("@b+"),
        Rc::new(RefCell::new(BinaryNativeFn::description(
            std::ops::Add::add as fn(isize, isize) -> isize,
        ))),
    );
    to.functions.insert(
        ustr("@b-"),
        Rc::new(RefCell::new(BinaryNativeFn::description(
            std::ops::Sub::sub as fn(isize, isize) -> isize,
        ))),
    );
    to.functions.insert(
        ustr("@b*"),
        Rc::new(RefCell::new(BinaryNativeFn::description(
            std::ops::Mul::mul as fn(isize, isize) -> isize,
        ))),
    );
    to.functions.insert(
        ustr("@b/"),
        Rc::new(RefCell::new(TryBinaryNativeFn::description(
            |lhs: isize, rhs: isize| {
                if rhs == 0 {
                    Err(DivisionByZero)
                } else {
                    Ok(lhs / rhs)
                }
            },
        ))),
    );
    to.functions.insert(
        ustr("@b%"),
        Rc::new(RefCell::new(TryBinaryNativeFn::description(
            |lhs: isize, rhs: isize| {
                if rhs == 0 {
                    Err(RemainderByZero)
                } else {
                    Ok(lhs % rhs)
                }
            },
        ))),
    );
    to.functions.insert(
        ustr("@u-"),
        Rc::new(RefCell::new(UnaryNativeFn::description(
            std::ops::Neg::neg as fn(isize) -> isize,
        ))),
    );

    // Comparisons
    to.functions.insert(
        ustr("@<"),
        Rc::new(RefCell::new(BinaryNativeFn::description(
            |lhs: isize, rhs: isize| std::cmp::PartialOrd::lt(&lhs, &rhs),
        ))),
    );
    to.functions.insert(
        ustr("@<="),
        Rc::new(RefCell::new(BinaryNativeFn::description(
            |lhs: isize, rhs: isize| std::cmp::PartialOrd::le(&lhs, &rhs),
        ))),
    );
    to.functions.insert(
        ustr("@>"),
        Rc::new(RefCell::new(BinaryNativeFn::description(
            |lhs: isize, rhs: isize| std::cmp::PartialOrd::gt(&lhs, &rhs),
        ))),
    );
    to.functions.insert(
        ustr("@>="),
        Rc::new(RefCell::new(BinaryNativeFn::description(
            |lhs: isize, rhs: isize| std::cmp::PartialOrd::ge(&lhs, &rhs),
        ))),
    );
}
