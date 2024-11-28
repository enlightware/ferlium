use std::{convert::identity, fmt};

use num_traits::Signed;
use ordered_float::NotNan;
use ustr::ustr;

use crate::{
    cached_primitive_ty,
    containers::b,
    effects::{no_effects, EffType},
    error::RuntimeError,
    function::{
        BinaryNativeFnNNFN, BinaryNativeFnNNN, Function, FunctionDefinition, TernaryNativeFnNNNFN,
        UnaryNativeFnNN,
    },
    module::Module,
    r#trait::TraitRef,
    r#type::{FnType, Type},
    value::NativeDisplay,
};

pub fn int_type() -> Type {
    cached_primitive_ty!(isize)
}

pub type Int = isize;

impl NativeDisplay for isize {
    fn fmt_as_literal(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

pub fn float_type() -> Type {
    cached_primitive_ty!(NotNan<f64>)
}

pub type Float = NotNan<f64>;

impl NativeDisplay for NotNan<f64> {
    fn fmt_as_literal(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.into_inner())
    }
}

fn isize_to_not_nan(value: isize) -> NotNan<f64> {
    // Safe because an `isize` is always a valid `f64`
    NotNan::new(value as f64).expect("Conversion from isize to NotNan<f64> should not fail")
}

pub fn add_to_module(to: &mut Module) {
    use RuntimeError::*;

    // Types
    to.types.set(ustr("int"), int_type());
    to.types.set(ustr("float"), float_type());

    // Traits
    let var0_ty = Type::variable_id(0);
    let unary_fn_ty = FnType::new_by_val(&[var0_ty], var0_ty, EffType::empty());
    let binary_fn_ty = FnType::new_by_val(&[var0_ty, var0_ty], var0_ty, EffType::empty());
    use FunctionDefinition as Def;
    let num_trait = TraitRef::new(
        "Num",
        1,
        0,
        [
            (
                "add",
                Def::new_infer_quantifiers(
                    binary_fn_ty.clone(),
                    &["lhs", "rhs"],
                    "Adds two numbers.",
                ),
            ),
            (
                "sub",
                Def::new_infer_quantifiers(
                    binary_fn_ty.clone(),
                    &["lhs", "rhs"],
                    "Subtracts `rhs` from `lhs`.",
                ),
            ),
            (
                "mul",
                Def::new_infer_quantifiers(
                    binary_fn_ty,
                    &["lhs", "rhs"],
                    "Multiplies two numbers.",
                ),
            ),
            (
                "neg",
                Def::new_infer_quantifiers(unary_fn_ty.clone(), &["value"], "Negates a number."),
            ),
            (
                "abs",
                Def::new_infer_quantifiers(
                    unary_fn_ty.clone(),
                    &["value"],
                    "Returns the absolute value of a number.",
                ),
            ),
            (
                "signum",
                Def::new_infer_quantifiers(
                    unary_fn_ty,
                    &["value"],
                    "Returns the sign of a number.",
                ),
            ),
            (
                "from_int",
                Def::new_infer_quantifiers(
                    FnType::new_by_val(&[int_type()], var0_ty, EffType::empty()),
                    &["value"],
                    "Converts an integer to a number.",
                ),
            ),
        ],
    );
    to.traits.push(num_trait.clone());

    // Trait implementations
    use std::ops;
    use BinaryNativeFnNNN as BinaryFn;
    use UnaryNativeFnNN as UnaryFn;
    to.impls.add(
        num_trait.clone(),
        [int_type()],
        [],
        [
            b(BinaryFn::new(<Int as ops::Add>::add)) as Function,
            b(BinaryFn::new(<Int as ops::Sub>::sub)) as Function,
            b(BinaryFn::new(<Int as ops::Mul>::mul)) as Function,
            b(UnaryFn::new(<Int as ops::Neg>::neg)) as Function,
            b(UnaryFn::new(Int::abs)) as Function,
            b(UnaryFn::new(Int::signum)) as Function,
            b(UnaryFn::new(identity::<Int>)) as Function,
        ],
    );
    to.impls.add(
        num_trait.clone(),
        [float_type()],
        [],
        [
            b(BinaryFn::new(<Float as ops::Add>::add)) as Function,
            b(BinaryFn::new(<Float as ops::Sub>::sub)) as Function,
            b(BinaryFn::new(<Float as ops::Mul>::mul)) as Function,
            b(UnaryFn::new(<Float as ops::Neg>::neg)) as Function,
            b(UnaryFn::new(Float::abs)) as Function,
            b(UnaryFn::new(Float::signum)) as Function,
            b(UnaryFn::new(isize_to_not_nan)) as Function,
        ],
    );

    // Computations
    to.functions.insert(
        ustr("@b+"),
        BinaryNativeFnNNN::description_with_default_ty(
            std::ops::Add::add as fn(isize, isize) -> isize,
            ["left", "right"],
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@b-"),
        BinaryNativeFnNNN::description_with_default_ty(
            std::ops::Sub::sub as fn(isize, isize) -> isize,
            ["left", "right"],
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@b*"),
        BinaryNativeFnNNN::description_with_default_ty(
            std::ops::Mul::mul as fn(isize, isize) -> isize,
            ["left", "right"],
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
            ["left", "right"],
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
            ["left", "right"],
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@u-"),
        UnaryNativeFnNN::description_with_default_ty(
            std::ops::Neg::neg as fn(isize) -> isize,
            ["value"],
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("min"),
        BinaryNativeFnNNN::description_with_default_ty(
            std::cmp::min as fn(isize, isize) -> isize,
            ["left", "right"],
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("max"),
        BinaryNativeFnNNN::description_with_default_ty(
            std::cmp::max as fn(isize, isize) -> isize,
            ["left", "right"],
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
            ["value", "min", "max"],
            no_effects(),
        ),
    );

    // Comparisons
    to.functions.insert(
        ustr("@<"),
        BinaryNativeFnNNN::description_with_default_ty(
            |lhs: isize, rhs: isize| std::cmp::PartialOrd::lt(&lhs, &rhs),
            ["left", "right"],
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@<="),
        BinaryNativeFnNNN::description_with_default_ty(
            |lhs: isize, rhs: isize| std::cmp::PartialOrd::le(&lhs, &rhs),
            ["left", "right"],
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@>"),
        BinaryNativeFnNNN::description_with_default_ty(
            |lhs: isize, rhs: isize| std::cmp::PartialOrd::gt(&lhs, &rhs),
            ["left", "right"],
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("@>="),
        BinaryNativeFnNNN::description_with_default_ty(
            |lhs: isize, rhs: isize| std::cmp::PartialOrd::ge(&lhs, &rhs),
            ["left", "right"],
            no_effects(),
        ),
    );
}
