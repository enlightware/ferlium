// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{convert::identity, fmt, sync::LazyLock};

use num_traits::Signed;
use ordered_float::NotNan;
use ustr::ustr;

use crate::{
    cached_primitive_ty,
    containers::b,
    effects::{no_effects, EffType},
    error::RuntimeError,
    function::{
        BinaryNativeFnNNFN, BinaryNativeFnNNN, BinaryNativeFnNNV, Function, FunctionDefinition,
        UnaryNativeFnNN,
    },
    module::Module,
    r#trait::TraitRef,
    r#type::{FnType, Type},
    std::ordering::{ORDERING_EQUAL, ORDERING_GREATER, ORDERING_LESS, ORD_TRAIT},
    value::{NativeDisplay, Value},
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

fn compare<T>(lhs: T, rhs: T) -> Value
where
    T: std::cmp::Ord,
{
    use std::cmp::Ordering::*;
    match lhs.cmp(&rhs) {
        Less => Value::unit_variant(ustr(ORDERING_LESS)),
        Equal => Value::unit_variant(ustr(ORDERING_EQUAL)),
        Greater => Value::unit_variant(ustr(ORDERING_GREATER)),
    }
}

use FunctionDefinition as Def;

pub static NUM_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    let var0_ty = Type::variable_id(0);
    let unary_fn_ty = FnType::new_by_val([var0_ty], var0_ty, EffType::empty());
    let binary_fn_ty = FnType::new_by_val([var0_ty, var0_ty], var0_ty, EffType::empty());

    TraitRef::new(
        "Num",
        1,
        [],
        [
            (
                "add",
                Def::new_infer_quantifiers(
                    binary_fn_ty.clone(),
                    ["lhs", "rhs"],
                    "Adds two numbers.",
                ),
            ),
            (
                "sub",
                Def::new_infer_quantifiers(
                    binary_fn_ty.clone(),
                    ["lhs", "rhs"],
                    "Subtracts `rhs` from `lhs`.",
                ),
            ),
            (
                "mul",
                Def::new_infer_quantifiers(
                    binary_fn_ty.clone(),
                    ["lhs", "rhs"],
                    "Multiplies two numbers.",
                ),
            ),
            (
                "neg",
                Def::new_infer_quantifiers(unary_fn_ty.clone(), ["value"], "Negates a number."),
            ),
            (
                "abs",
                Def::new_infer_quantifiers(
                    unary_fn_ty.clone(),
                    ["value"],
                    "Returns the absolute value of a number.",
                ),
            ),
            (
                "signum",
                Def::new_infer_quantifiers(unary_fn_ty, ["value"], "Returns the sign of a number."),
            ),
            (
                "from_int",
                Def::new_infer_quantifiers(
                    FnType::new_by_val([int_type()], var0_ty, EffType::empty()),
                    ["value"],
                    "Converts an integer to a number.",
                ),
            ),
        ],
    )
});

pub static DIV_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    let var0_ty = Type::variable_id(0);
    let binary_fn_ty = FnType::new_by_val([var0_ty, var0_ty], var0_ty, EffType::empty());

    TraitRef::new(
        "Div",
        1,
        [],
        [(
            "div",
            Def::new_infer_quantifiers(binary_fn_ty, ["lhs", "rhs"], "Divides `lhs` by `rhs`."),
        )],
    )
});

pub fn add_to_module(to: &mut Module) {
    use RuntimeError::*;

    // Types
    to.type_aliases.set("int", int_type());
    to.type_aliases.set("float", float_type());

    // Traits
    to.traits.push(NUM_TRAIT.clone());
    to.traits.push(DIV_TRAIT.clone());

    // Trait implementations
    use std::ops;
    use BinaryNativeFnNNN as BinaryFn;
    use UnaryNativeFnNN as UnaryFn;

    // int
    to.add_concrete_impl(
        NUM_TRAIT.clone().clone(),
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
    to.add_concrete_impl(
        ORD_TRAIT.clone(),
        [int_type()],
        [],
        [b(BinaryNativeFnNNV::new(compare::<Int>)) as Function],
    );
    to.add_named_function(
        ustr("idiv"),
        BinaryNativeFnNNFN::description_with_default_ty(
            |lhs: isize, rhs: isize| {
                if rhs == 0 {
                    Err(DivisionByZero)
                } else {
                    Ok(lhs / rhs)
                }
            },
            ["lhs", "rhs"],
            Some("Divides `lhs` by `rhs` and truncates the result."),
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("idiv_euclid"),
        BinaryNativeFnNNFN::description_with_default_ty(
            |lhs: isize, rhs: isize| {
                if rhs == 0 {
                    Err(DivisionByZero)
                } else {
                    Ok(lhs.div_euclid(rhs))
                }
            },
            ["lhs", "rhs"],
            Some("Calculates the quotient of Euclidean division of `lhs` by `rhs`."),
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("rem"),
        BinaryNativeFnNNFN::description_with_default_ty(
            |lhs: isize, rhs: isize| {
                if rhs == 0 {
                    Err(RemainderByZero)
                } else {
                    Ok(ops::Rem::rem(lhs, rhs))
                }
            },
            ["lhs", "rhs"],
            Some("Calculates the remainder of the division of `lhs` by `rhs`."),
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("mod"),
        BinaryNativeFnNNFN::description_with_default_ty(
            |lhs: isize, rhs: isize| {
                if rhs == 0 {
                    Err(RemainderByZero)
                } else {
                    Ok(lhs.rem_euclid(rhs))
                }
            },
            ["lhs", "rhs"],
            Some("Calculates the modulo of the division of `lhs` by `rhs`."),
            no_effects(),
        ),
    );

    // float
    to.add_concrete_impl(
        NUM_TRAIT.clone(),
        [float_type()],
        [],
        [
            b(BinaryFn::new(<Float as ops::Add>::add)) as Function,
            b(BinaryFn::new(<Float as ops::Sub>::sub)) as Function,
            b(BinaryFn::new(<Float as ops::Mul>::mul)) as Function,
            b(UnaryFn::new(<Float as ops::Neg>::neg)) as Function,
            b(UnaryFn::new(|value: Float| Float::abs(&value))) as Function,
            b(UnaryFn::new(|value: Float| Float::signum(&value))) as Function,
            b(UnaryFn::new(isize_to_not_nan)) as Function,
        ],
    );
    to.add_concrete_impl(
        ORD_TRAIT.clone(),
        [float_type()],
        [],
        [b(BinaryNativeFnNNV::new(compare::<Float>)) as Function],
    );
    to.add_concrete_impl(
        DIV_TRAIT.clone(),
        [float_type()],
        [],
        [b(BinaryNativeFnNNFN::new(|lhs: Float, rhs: Float| {
            if rhs == 0.0 {
                Err(DivisionByZero)
            } else {
                Ok(lhs / rhs)
            }
        })) as Function],
    );
    to.add_named_function(
        ustr("round"),
        UnaryNativeFnNN::description_with_default_ty(
            |value: Float| value.round() as Int,
            ["value"],
            Some("Rounds a number to the nearest integer."),
            no_effects(),
        ),
    );
}
