use std::fmt;

use ordered_float::NotNan;
use ustr::ustr;

use crate::{
    cached_primitive_ty,
    effects::no_effects,
    error::RuntimeError,
    function::{BinaryNativeFnNNFN, BinaryNativeFnNNN, TernaryNativeFnNNNFN, UnaryNativeFnNN},
    module::Module,
    r#type::Type,
    value::NativeDisplay,
};

pub fn int_type() -> Type {
    cached_primitive_ty!(isize)
}

impl NativeDisplay for isize {
    fn fmt_as_literal(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

pub fn float_type() -> Type {
    cached_primitive_ty!(NotNan<f64>)
}

impl NativeDisplay for NotNan<f64> {
    fn fmt_as_literal(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
        BinaryNativeFnNNN::description_with_default_ty(
            std::ops::Add::add as fn(isize, isize) -> isize,
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@b-"),
        BinaryNativeFnNNN::description_with_default_ty(
            std::ops::Sub::sub as fn(isize, isize) -> isize,
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@b*"),
        BinaryNativeFnNNN::description_with_default_ty(
            std::ops::Mul::mul as fn(isize, isize) -> isize,
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@b/"),
        BinaryNativeFnNNFN::description_with_default_ty(
            |lhs: isize, rhs: isize| {
                if rhs == 0 {
                    Err(DivisionByZero)
                } else {
                    Ok(lhs / rhs)
                }
            },
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@b%"),
        BinaryNativeFnNNFN::description_with_default_ty(
            |lhs: isize, rhs: isize| {
                if rhs == 0 {
                    Err(RemainderByZero)
                } else {
                    Ok(lhs % rhs)
                }
            },
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@u-"),
        UnaryNativeFnNN::description_with_default_ty(
            std::ops::Neg::neg as fn(isize) -> isize,
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("min"),
        BinaryNativeFnNNN::description_with_default_ty(
            std::cmp::min as fn(isize, isize) -> isize,
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("max"),
        BinaryNativeFnNNN::description_with_default_ty(
            std::cmp::max as fn(isize, isize) -> isize,
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("clamp"),
        TernaryNativeFnNNNFN::description_with_default_ty(
            |value: isize, min: isize, max: isize| {
                if min > max {
                    Err(InvalidArgument(ustr(
                        "min must be less than or equal to max",
                    )))
                } else {
                    Ok(value.min(max).max(min))
                }
            },
            no_effects(),
        ),
    );

    // Comparisons
    to.functions.insert(
        ustr("@<"),
        BinaryNativeFnNNN::description_with_default_ty(
            |lhs: isize, rhs: isize| std::cmp::PartialOrd::lt(&lhs, &rhs),
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@<="),
        BinaryNativeFnNNN::description_with_default_ty(
            |lhs: isize, rhs: isize| std::cmp::PartialOrd::le(&lhs, &rhs),
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@>"),
        BinaryNativeFnNNN::description_with_default_ty(
            |lhs: isize, rhs: isize| std::cmp::PartialOrd::gt(&lhs, &rhs),
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@>="),
        BinaryNativeFnNNN::description_with_default_ty(
            |lhs: isize, rhs: isize| std::cmp::PartialOrd::ge(&lhs, &rhs),
            no_effects(),
        ),
    );
}
