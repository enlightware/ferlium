// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{convert::identity, fmt};

use num_traits::{Bounded, NumCast, PrimInt, Signed, Zero};
use ordered_float::{FloatCore, NotNan};
use ustr::ustr;

use crate::{
    cached_primitive_ty,
    containers::b,
    effects::{PrimitiveEffect, effect, no_effects},
    error::RuntimeErrorKind,
    function::{
        BinaryNativeFnNNFN, BinaryNativeFnNNN, BinaryNativeFnNNV, Function, NullaryNativeFnN,
        UnaryNativeFnNN,
    },
    module::Module,
    std::{
        cast::CAST_TRAIT,
        core_traits_names::{BITS_TRAIT_NAME, DIV_TRAIT_NAME, NUM_TRAIT_NAME, ORD_TRAIT_NAME},
        default::DEFAULT_TRAIT,
        ordering::compare,
    },
    r#type::Type,
    value::{NativeDisplay, Value},
};

pub fn int_type() -> Type {
    cached_primitive_ty!(isize)
}

pub fn int_value(i: isize) -> Value {
    Value::native(i)
}

pub type Int = isize;

impl NativeDisplay for isize {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

pub fn float_type() -> Type {
    cached_primitive_ty!(NotNan<f64>)
}

pub fn float_value(value: f64) -> Value {
    Value::native(NotNan::new(value).unwrap())
}

pub type Float = NotNan<f64>;

impl NativeDisplay for NotNan<f64> {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.into_inner())
    }
}

fn isize_to_not_nan(value: isize) -> NotNan<f64> {
    // Safe because an `isize` is always a valid `f64`
    NotNan::new(value as f64).expect("Conversion from isize to NotNan<f64> should not fail")
}

/// Integer → float with finite saturation, wrapped in NotNan.
pub fn saturating_cast_int_to_notnan<I, F>(x: I) -> NotNan<F>
where
    I: NumCast + PrimInt + Zero,
    F: NumCast + FloatCore + Bounded,
{
    // First, try the straightforward numeric cast.
    let mut v: F = NumCast::from(x).unwrap_or_else(|| {
        // If the integer can't be represented at all (e.g., very wide int),
        // pick an extreme based on the sign of x.
        if x < I::zero() {
            <F as Bounded>::min_value()
        } else {
            <F as Bounded>::max_value()
        }
    });

    // Avoid infinities that some int→float casts can produce.
    if v.is_infinite() {
        v = if x < I::zero() {
            <F as Bounded>::min_value()
        } else {
            <F as Bounded>::max_value()
        };
    }

    // y is finite and not NaN by construction.
    NotNan::new(v).unwrap()
}

/// Float → integer with saturation.
fn saturating_trunc<F, I>(x: NotNan<F>) -> I
where
    F: NumCast + FloatCore,
    I: NumCast + Bounded,
{
    if let Some(v) = NumCast::from(x.trunc()) {
        v
    } else if x.is_sign_negative() {
        I::min_value()
    } else {
        I::max_value()
    }
}

fn clamp_to_u32(value: Int) -> u32 {
    if value <= 0 {
        return 0;
    }
    #[cfg(any(target_pointer_width = "16", target_pointer_width = "32"))]
    {
        value as u32
    }
    #[cfg(target_pointer_width = "64")]
    {
        (value as u64).min(u32::MAX as u64) as u32
    }
}

fn clamped_negated_shift_to_u32(shift: Int) -> u32 {
    let shift = if shift == Int::MIN { Int::MAX } else { -shift };
    clamp_to_u32(shift)
}

fn shift_left(value: Int, shift: Int) -> Int {
    if shift < 0 {
        let shift = clamped_negated_shift_to_u32(shift);
        value.wrapping_shr(shift)
    } else {
        let shift = clamp_to_u32(shift);
        value.wrapping_shl(shift)
    }
}

fn shift_right(value: Int, shift: Int) -> Int {
    if shift < 0 {
        let shift = clamped_negated_shift_to_u32(shift);
        value.wrapping_shl(shift)
    } else {
        let shift = clamp_to_u32(shift);
        value.wrapping_shr(shift)
    }
}

fn rotate_left(value: Int, shift: Int) -> Int {
    if shift < 0 {
        let shift = clamped_negated_shift_to_u32(shift);
        value.rotate_right(shift)
    } else {
        let shift = clamp_to_u32(shift);
        value.rotate_left(shift)
    }
}

fn rotate_right(value: Int, shift: Int) -> Int {
    if shift < 0 {
        let shift = clamped_negated_shift_to_u32(shift);
        value.rotate_left(shift)
    } else {
        let shift = clamp_to_u32(shift);
        value.rotate_right(shift)
    }
}

fn count_ones(value: Int) -> Int {
    value.count_ones() as Int
}

fn count_zeros(value: Int) -> Int {
    value.count_zeros() as Int
}

fn bit(position: Int) -> Int {
    if position < 0 {
        return 0;
    }
    let position = clamp_to_u32(position);
    (1 as Int).checked_shl(position).unwrap_or(0)
}

fn set_bit(value: Int, position: Int) -> Int {
    value | bit(position)
}

fn clear_bit(value: Int, position: Int) -> Int {
    value & !bit(position)
}

fn test_bit(value: Int, position: Int) -> bool {
    (value & bit(position)) != 0
}

pub fn add_to_module(to: &mut Module) {
    use RuntimeErrorKind::*;

    // Types
    // Note: aliases are added in core.rs

    // Trait implementations
    use BinaryNativeFnNNN as BinaryFn;
    use UnaryNativeFnNN as UnaryFn;
    use std::ops;

    // int
    let num_trait = to.get_trait_str(NUM_TRAIT_NAME).unwrap().clone();
    to.add_concrete_impl_no_locals(
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
    let bits_trait = to.get_trait_str(BITS_TRAIT_NAME).unwrap().clone();
    to.add_concrete_impl_no_locals(
        bits_trait,
        [int_type()],
        [],
        [
            b(BinaryFn::new(<Int as ops::BitAnd>::bitand)) as Function,
            b(BinaryFn::new(<Int as ops::BitOr>::bitor)) as Function,
            b(BinaryFn::new(<Int as ops::BitXor>::bitxor)) as Function,
            b(UnaryFn::new(<Int as ops::Not>::not)) as Function,
            b(BinaryFn::new(shift_left)) as Function,
            b(BinaryFn::new(shift_right)) as Function,
            b(BinaryFn::new(rotate_left)) as Function,
            b(BinaryFn::new(rotate_right)) as Function,
            b(UnaryFn::new(count_ones)) as Function,
            b(UnaryFn::new(count_zeros)) as Function,
            b(UnaryFn::new(bit)) as Function,
            b(BinaryFn::new(set_bit)) as Function,
            b(BinaryFn::new(clear_bit)) as Function,
            b(BinaryFn::new(test_bit)) as Function,
        ],
    );
    let ord_trait = to.get_trait_str(ORD_TRAIT_NAME).unwrap().clone();
    to.add_concrete_impl_no_locals(
        ord_trait.clone(),
        [int_type()],
        [],
        [b(BinaryNativeFnNNV::new(compare::<Int>)) as Function],
    );
    to.add_concrete_impl_no_locals(
        DEFAULT_TRAIT.clone(),
        [int_type()],
        [],
        [b(NullaryNativeFnN::new(|| 0isize)) as Function],
    );
    to.add_function(
        ustr("idiv"),
        BinaryNativeFnNNFN::description_with_default_ty(
            |lhs: isize, rhs: isize| {
                if rhs == 0 {
                    Err(DivisionByZero)
                } else {
                    Ok(lhs / rhs)
                }
            },
            ["left", "right"],
            "Divides `left` by `right` and truncates the result.",
            effect(PrimitiveEffect::Fallible),
        ),
    );
    to.add_function(
        ustr("idiv_euclid"),
        BinaryNativeFnNNFN::description_with_default_ty(
            |lhs: isize, rhs: isize| {
                if rhs == 0 {
                    Err(DivisionByZero)
                } else {
                    Ok(lhs.div_euclid(rhs))
                }
            },
            ["left", "right"],
            "Calculates the quotient of the Euclidean division of `left` by `right`.",
            effect(PrimitiveEffect::Fallible),
        ),
    );
    to.add_function(
        ustr("rem"),
        BinaryNativeFnNNFN::description_with_default_ty(
            |lhs: isize, rhs: isize| {
                if rhs == 0 {
                    Err(RemainderByZero)
                } else {
                    Ok(ops::Rem::rem(lhs, rhs))
                }
            },
            ["left", "right"],
            "Calculates the remainder of the division of `left` by `right`.",
            effect(PrimitiveEffect::Fallible),
        ),
    );
    to.add_function(
        ustr("mod"),
        BinaryNativeFnNNFN::description_with_default_ty(
            |lhs: isize, rhs: isize| {
                if rhs == 0 {
                    Err(RemainderByZero)
                } else {
                    Ok(lhs.rem_euclid(rhs))
                }
            },
            ["left", "right"],
            "Calculates the modulo of the division of `left` by `right`.",
            effect(PrimitiveEffect::Fallible),
        ),
    );

    // float
    to.add_concrete_impl_no_locals(
        num_trait.clone(),
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
    to.add_concrete_impl_no_locals(
        ord_trait.clone(),
        [float_type()],
        [],
        [b(BinaryNativeFnNNV::new(compare::<Float>)) as Function],
    );
    let div_trait = to.get_trait_str(DIV_TRAIT_NAME).unwrap().clone();
    to.add_concrete_impl_no_locals(
        div_trait,
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
    to.add_concrete_impl_no_locals(
        DEFAULT_TRAIT.clone(),
        [float_type()],
        [],
        [b(NullaryNativeFnN::new(|| Float::new(0.0).unwrap())) as Function],
    );
    to.add_function(
        ustr("round"),
        UnaryNativeFnNN::description_with_default_ty(
            |value: Float| value.round() as Int,
            ["value"],
            "Rounds a number to the nearest integer.",
            no_effects(),
        ),
    );

    // conversions
    to.add_concrete_impl_no_locals(
        CAST_TRAIT.clone(),
        [int_type(), float_type()],
        [],
        [b(UnaryNativeFnNN::new(
            saturating_cast_int_to_notnan::<Int, f64>,
        )) as Function],
    );
    to.add_concrete_impl_no_locals(
        CAST_TRAIT.clone(),
        [float_type(), int_type()],
        [],
        [b(UnaryNativeFnNN::new(saturating_trunc::<f64, Int>)) as Function],
    );
}
