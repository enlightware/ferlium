use std::fmt;

use ordered_float::NotNan;
use ustr::ustr;

use crate::{
    error::RuntimeError,
    function::{BinaryNativeFn, TryBinaryNativeFn, UnaryNativeFn},
    module::Module,
    r#type::Type,
    value::NativeDisplay,
};

pub fn int_type() -> Type {
    Type::primitive::<isize>()
}

impl NativeDisplay for isize {
    fn native_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

pub fn float_type() -> Type {
    Type::primitive::<NotNan<f64>>()
}

impl NativeDisplay for NotNan<f64> {
    fn native_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.into_inner())
    }
}

pub fn add_to_module(to: &mut Module) {
    use RuntimeError::*;

    // Types
    to.types.set(ustr("int"), int_type());
    to.types.set(ustr("float"), float_type());

    // TODO: use type classes to support floats
    // Computations
    to.functions.insert(
        ustr("@b+"),
        BinaryNativeFn::description(std::ops::Add::add as fn(isize, isize) -> isize),
    );
    to.functions.insert(
        ustr("@b-"),
        BinaryNativeFn::description(std::ops::Sub::sub as fn(isize, isize) -> isize),
    );
    to.functions.insert(
        ustr("@b*"),
        BinaryNativeFn::description(std::ops::Mul::mul as fn(isize, isize) -> isize),
    );
    to.functions.insert(
        ustr("@b/"),
        TryBinaryNativeFn::description(|lhs: isize, rhs: isize| {
            if rhs == 0 {
                Err(DivisionByZero)
            } else {
                Ok(lhs / rhs)
            }
        }),
    );
    to.functions.insert(
        ustr("@b%"),
        TryBinaryNativeFn::description(|lhs: isize, rhs: isize| {
            if rhs == 0 {
                Err(RemainderByZero)
            } else {
                Ok(lhs % rhs)
            }
        }),
    );
    to.functions.insert(
        ustr("@u-"),
        UnaryNativeFn::description(std::ops::Neg::neg as fn(isize) -> isize),
    );

    // Comparisons
    to.functions.insert(
        ustr("@<"),
        BinaryNativeFn::description(|lhs: isize, rhs: isize| std::cmp::PartialOrd::lt(&lhs, &rhs)),
    );
    to.functions.insert(
        ustr("@<="),
        BinaryNativeFn::description(|lhs: isize, rhs: isize| std::cmp::PartialOrd::le(&lhs, &rhs)),
    );
    to.functions.insert(
        ustr("@>"),
        BinaryNativeFn::description(|lhs: isize, rhs: isize| std::cmp::PartialOrd::gt(&lhs, &rhs)),
    );
    to.functions.insert(
        ustr("@>="),
        BinaryNativeFn::description(|lhs: isize, rhs: isize| std::cmp::PartialOrd::ge(&lhs, &rhs)),
    );
}
