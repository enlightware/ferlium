// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    convert::identity,
    fmt,
    hash::{Hash, Hasher as StdHasher},
    str::FromStr,
    string::String as StdString,
};

use num_traits::{Bounded, NumCast, PrimInt, Signed, Zero};
use ordered_float::NotNan;
use ustr::ustr;

use crate::{
    cached_primitive_ty,
    compiler::error::RuntimeErrorKind,
    containers::b,
    hir::function::{
        BinaryNativeFnNMN, BinaryNativeFnNNFN, BinaryNativeFnNNN, BinaryNativeFnNNV,
        BinaryNativeFnRMN, BinaryNativeFnRRFN, BinaryNativeFnRRN, BinaryNativeFnRRV, Function,
        NullaryNativeFnN, UnaryNativeFnNN, UnaryNativeFnRFN, UnaryNativeFnRN,
    },
    hir::value::{NativeDisplay, Value},
    module::Module,
    std::{
        cast::CAST_TRAIT,
        core::TRIVIAL_COPY_TRAIT,
        core_traits_names::{
            BITS_TRAIT_NAME, DIV_TRAIT_NAME, NUM_TRAIT_NAME, ORD_TRAIT_NAME, REAL_TRAIT_NAME,
        },
        default::DEFAULT_TRAIT,
        hash::Hasher,
        ordering::compare,
        string::String,
        value::{
            VALUE_TRAIT, equal, native_layout_associated_consts, native_value_clone_function,
            native_value_drop_function,
        },
    },
    types::effects::{PrimitiveEffect, effect, no_effects},
    types::r#type::Type,
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
    cached_primitive_ty!(Float)
}

pub fn float_value(value: f64) -> Value {
    Value::native(Float::new(value).unwrap())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Float(NotNan<f64>);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FloatIsNotFinite;

impl Float {
    pub fn new(value: f64) -> Result<Self, FloatIsNotFinite> {
        if value.is_finite() {
            Ok(Self(
                NotNan::new(value).expect("finite f64 values are never NaN"),
            ))
        } else {
            Err(FloatIsNotFinite)
        }
    }

    pub fn new_saturating(value: f64) -> Self {
        if value.is_finite() {
            Self::new(value).expect("finite f64 values should construct a Float")
        } else if value.is_nan() {
            panic!("finite float operation produced NaN")
        } else if value.is_sign_negative() {
            Self::new(-f64::MAX).expect("f64::MAX should construct a Float")
        } else {
            Self::new(f64::MAX).expect("f64::MAX should construct a Float")
        }
    }

    pub fn into_inner(self) -> f64 {
        self.0.into_inner()
    }

    pub fn is_sign_negative(self) -> bool {
        self.into_inner().is_sign_negative()
    }

    pub fn abs(self) -> Self {
        Self(self.0.abs())
    }

    pub fn signum(self) -> Self {
        Self(self.0.signum())
    }

    pub fn round(self) -> f64 {
        self.into_inner().round()
    }

    pub fn floor(self) -> f64 {
        self.into_inner().floor()
    }

    pub fn ceil(self) -> f64 {
        self.into_inner().ceil()
    }
}

impl Hash for Float {
    fn hash<H: StdHasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl fmt::Display for Float {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.into_inner())
    }
}

impl FromStr for Float {
    type Err = StdString;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let value = s.parse::<f64>().map_err(|err| err.to_string())?;
        Self::new(value).map_err(|_| "value must be finite".to_string())
    }
}

impl Bounded for Float {
    fn min_value() -> Self {
        Self::new(-f64::MAX).expect("f64::MAX should construct a Float")
    }

    fn max_value() -> Self {
        Self::new(f64::MAX).expect("f64::MAX should construct a Float")
    }
}

impl NativeDisplay for Float {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.into_inner())
    }
}

fn invalid_real_argument(message: StdString) -> RuntimeErrorKind {
    RuntimeErrorKind::InvalidArgument(ustr(message.as_str()))
}

fn saturated_real_result(value: f64) -> Float {
    Float::new_saturating(value)
}

fn isize_to_float(value: isize) -> Float {
    // Safe because an `isize` always converts to a finite `f64`.
    Float::new(value as f64).expect("Conversion from isize to Float should not fail")
}

/// Integer → float with finite saturation.
pub fn saturating_cast_int_to_float<I>(x: I) -> Float
where
    I: NumCast + PrimInt + Zero,
{
    // First, try the straightforward numeric cast.
    let v = NumCast::from(x).unwrap_or_else(|| {
        // If the integer can't be represented at all (e.g., very wide int),
        // pick an extreme based on the sign of x.
        if x < I::zero() { -f64::MAX } else { f64::MAX }
    });

    Float::new_saturating(v)
}

/// Float → integer with saturation.
fn saturating_trunc<I>(x: Float) -> I
where
    I: NumCast + Bounded,
{
    if let Some(v) = NumCast::from(x.into_inner().trunc()) {
        v
    } else if x.is_sign_negative() {
        I::min_value()
    } else {
        I::max_value()
    }
}

fn saturating_trunc_ref(value: &Float) -> Int {
    saturating_trunc::<Int>(*value)
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

fn hash_int(value: Int, state: &mut Hasher) {
    state.write_isize(value);
}

fn hash_float(value: &Float, state: &mut Hasher) {
    state.write_u64(value.into_inner().to_bits());
}

fn equal_float(lhs: &Float, rhs: &Float) -> bool {
    lhs == rhs
}

fn compare_float(lhs: &Float, rhs: &Float) -> Value {
    compare(*lhs, *rhs)
}

fn add_float(lhs: &Float, rhs: &Float) -> Float {
    Float::new_saturating(lhs.into_inner() + rhs.into_inner())
}

fn sub_float(lhs: &Float, rhs: &Float) -> Float {
    Float::new_saturating(lhs.into_inner() - rhs.into_inner())
}

fn mul_float(lhs: &Float, rhs: &Float) -> Float {
    Float::new_saturating(lhs.into_inner() * rhs.into_inner())
}

fn div_float(lhs: &Float, rhs: &Float) -> Result<Float, RuntimeErrorKind> {
    if rhs.into_inner() == 0.0 {
        Err(RuntimeErrorKind::DivisionByZero)
    } else {
        Ok(Float::new_saturating(lhs.into_inner() / rhs.into_inner()))
    }
}

fn sin_float(value: &Float) -> Float {
    saturated_real_result(value.into_inner().sin())
}

fn cos_float(value: &Float) -> Float {
    saturated_real_result(value.into_inner().cos())
}

fn tan_float(value: &Float) -> Float {
    saturated_real_result(value.into_inner().tan())
}

fn asin_float(value: &Float) -> Result<Float, RuntimeErrorKind> {
    let value = value.into_inner();
    Float::new(value.asin()).map_err(|_| {
        invalid_real_argument(format!(
            "Taking the arcsine of {value} is undefined because it is outside [-1, 1]"
        ))
    })
}

fn acos_float(value: &Float) -> Result<Float, RuntimeErrorKind> {
    let value = value.into_inner();
    Float::new(value.acos()).map_err(|_| {
        invalid_real_argument(format!(
            "Taking the arccosine of {value} is undefined because it is outside [-1, 1]"
        ))
    })
}

fn atan_float(value: &Float) -> Float {
    saturated_real_result(value.into_inner().atan())
}

fn atan2_float(y: &Float, x: &Float) -> Float {
    saturated_real_result(y.into_inner().atan2(x.into_inner()))
}

fn sinh_float(value: &Float) -> Float {
    saturated_real_result(value.into_inner().sinh())
}

fn cosh_float(value: &Float) -> Float {
    saturated_real_result(value.into_inner().cosh())
}

fn tanh_float(value: &Float) -> Float {
    saturated_real_result(value.into_inner().tanh())
}

fn asinh_float(value: &Float) -> Float {
    saturated_real_result(value.into_inner().asinh())
}

fn acosh_float(value: &Float) -> Result<Float, RuntimeErrorKind> {
    let value = value.into_inner();
    Float::new(value.acosh()).map_err(|_| {
        invalid_real_argument(format!(
            "Taking the inverse hyperbolic cosine of {value} is undefined because it is less than 1"
        ))
    })
}

fn atanh_float(value: &Float) -> Result<Float, RuntimeErrorKind> {
    let value = value.into_inner();
    Float::new(value.atanh()).map_err(|_| {
        invalid_real_argument(format!(
            "Taking the inverse hyperbolic tangent of {value} is undefined because it is outside (-1, 1)"
        ))
    })
}

fn exp_float(value: &Float) -> Float {
    saturated_real_result(value.into_inner().exp())
}

fn log_float(value: &Float) -> Result<Float, RuntimeErrorKind> {
    let value = value.into_inner();
    Float::new(value.ln()).map_err(|_| {
        invalid_real_argument(format!(
            "Taking the logarithm of {value} is undefined because it is not positive"
        ))
    })
}

fn pow_float(base: &Float, exponent: &Float) -> Result<Float, RuntimeErrorKind> {
    let base = base.into_inner();
    let exponent = exponent.into_inner();
    let result = base.powf(exponent);
    if result.is_nan() {
        Err(invalid_real_argument(format!(
            "Raising {base} to the power {exponent} is undefined as a real number"
        )))
    } else {
        Ok(saturated_real_result(result))
    }
}

fn sqrt_float(value: &Float) -> Result<Float, RuntimeErrorKind> {
    let value = value.into_inner();
    Float::new(value.sqrt()).map_err(|_| {
        invalid_real_argument(format!(
            "Taking the square root of {value} is undefined because it is negative"
        ))
    })
}

fn neg_float(value: &Float) -> Float {
    Float::new(-value.into_inner()).expect("negating a finite float should stay finite")
}

fn abs_float(value: &Float) -> Float {
    value.abs()
}

fn signum_float(value: &Float) -> Float {
    value.signum()
}

fn round_float(value: &Float) -> Int {
    value.round() as Int
}

fn floor_float(value: &Float) -> Int {
    value.floor() as Int
}

fn ceil_float(value: &Float) -> Int {
    value.ceil() as Int
}

fn float_to_string(value: &Float) -> String {
    String::new(&value.to_string())
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
    to.add_concrete_impl_no_locals(
        VALUE_TRAIT.clone(),
        [int_type()],
        [],
        native_layout_associated_consts::<Int>(),
        [
            b(BinaryFn::new(equal::<Int>)) as Function,
            b(UnaryFn::new(|value: Int| String::new(&value.to_string()))) as Function,
            b(BinaryNativeFnNMN::new(hash_int)) as Function,
            native_value_clone_function::<Int>(),
            native_value_drop_function::<Int>(),
        ],
    );
    let num_trait = to.get_trait_str(NUM_TRAIT_NAME).unwrap().clone();
    to.add_native_concrete_impl(
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
    to.add_native_concrete_impl(
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
    to.add_native_concrete_impl(
        ord_trait.clone(),
        [int_type()],
        [],
        [b(BinaryNativeFnNNV::new(compare::<Int>)) as Function],
    );
    to.add_native_concrete_impl(
        DEFAULT_TRAIT.clone(),
        [int_type()],
        [],
        [b(NullaryNativeFnN::new(|| 0isize)) as Function],
    );
    to.add_native_concrete_impl(
        TRIVIAL_COPY_TRAIT.clone(),
        [int_type()],
        [],
        Vec::<Function>::new(),
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
        VALUE_TRAIT.clone(),
        [float_type()],
        [],
        native_layout_associated_consts::<Float>(),
        [
            b(BinaryNativeFnRRN::new(equal_float)) as Function,
            b(UnaryNativeFnRN::new(float_to_string)) as Function,
            b(BinaryNativeFnRMN::new(hash_float)) as Function,
            native_value_clone_function::<Float>(),
            native_value_drop_function::<Float>(),
        ],
    );
    to.add_native_concrete_impl(
        num_trait.clone(),
        [float_type()],
        [],
        [
            b(BinaryNativeFnRRN::new(add_float)) as Function,
            b(BinaryNativeFnRRN::new(sub_float)) as Function,
            b(BinaryNativeFnRRN::new(mul_float)) as Function,
            b(UnaryNativeFnRN::new(neg_float)) as Function,
            b(UnaryNativeFnRN::new(abs_float)) as Function,
            b(UnaryNativeFnRN::new(signum_float)) as Function,
            b(UnaryFn::new(isize_to_float)) as Function,
        ],
    );
    to.add_native_concrete_impl(
        ord_trait.clone(),
        [float_type()],
        [],
        [b(BinaryNativeFnRRV::new(compare_float)) as Function],
    );
    let div_trait = to.get_trait_str(DIV_TRAIT_NAME).unwrap().clone();
    to.add_native_concrete_impl(
        div_trait,
        [float_type()],
        [],
        [b(BinaryNativeFnRRFN::new(div_float)) as Function],
    );
    let real_trait = to.get_trait_str(REAL_TRAIT_NAME).unwrap().clone();
    to.add_native_concrete_impl(
        real_trait,
        [float_type()],
        [],
        [
            b(UnaryNativeFnRN::new(sin_float)) as Function,
            b(UnaryNativeFnRN::new(cos_float)) as Function,
            b(UnaryNativeFnRN::new(tan_float)) as Function,
            b(UnaryNativeFnRFN::new(asin_float)) as Function,
            b(UnaryNativeFnRFN::new(acos_float)) as Function,
            b(UnaryNativeFnRN::new(atan_float)) as Function,
            b(BinaryNativeFnRRN::new(atan2_float)) as Function,
            b(UnaryNativeFnRN::new(sinh_float)) as Function,
            b(UnaryNativeFnRN::new(cosh_float)) as Function,
            b(UnaryNativeFnRN::new(tanh_float)) as Function,
            b(UnaryNativeFnRN::new(asinh_float)) as Function,
            b(UnaryNativeFnRFN::new(acosh_float)) as Function,
            b(UnaryNativeFnRFN::new(atanh_float)) as Function,
            b(UnaryNativeFnRN::new(exp_float)) as Function,
            b(UnaryNativeFnRFN::new(log_float)) as Function,
            b(BinaryNativeFnRRFN::new(pow_float)) as Function,
            b(UnaryNativeFnRFN::new(sqrt_float)) as Function,
        ],
    );
    to.add_native_concrete_impl(
        DEFAULT_TRAIT.clone(),
        [float_type()],
        [],
        [b(NullaryNativeFnN::new(|| Float::new(0.0).unwrap())) as Function],
    );
    to.add_function(
        ustr("round"),
        UnaryNativeFnRN::description_with_default_ty(
            round_float,
            ["value"],
            "Rounds a number to the nearest integer, saturating if necessary.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("floor"),
        UnaryNativeFnRN::description_with_default_ty(
            floor_float,
            ["value"],
            "Rounds a number down to the nearest integer, saturating if necessary.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("ceil"),
        UnaryNativeFnRN::description_with_default_ty(
            ceil_float,
            ["value"],
            "Rounds a number up to the nearest integer, saturating if necessary.",
            no_effects(),
        ),
    );

    // conversions
    to.add_native_concrete_impl(
        CAST_TRAIT.clone(),
        [int_type(), float_type()],
        [],
        [b(UnaryNativeFnNN::new(saturating_cast_int_to_float::<Int>)) as Function],
    );
    to.add_native_concrete_impl(
        CAST_TRAIT.clone(),
        [float_type(), int_type()],
        [],
        [b(UnaryNativeFnRN::new(saturating_trunc_ref)) as Function],
    );
}
