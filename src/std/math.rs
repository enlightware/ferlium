// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{
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
    compiler::error::SourceFailureKind,
    containers::b,
    hir::function::Function,
    hir::native_functions::{
        NativeFallibleOutFnN, NativeFallibleOutFnNN, NativeFn0, NativeFnN, NativeFnNM, NativeFnNN,
        NativeOutFnN,
    },
    hir::value::{LiteralValue, NativeDisplay, Value},
    module::Module,
    std::{
        core_traits_names::{
            BITS_TRAIT_NAME, CAST_TRAIT_NAME, DEFAULT_TRAIT_NAME, DIV_TRAIT_NAME,
            INSPECT_TRAIT_NAME, NUM_TRAIT_NAME, REAL_TRAIT_NAME, TRIVIAL_COPY_TRAIT_NAME,
            VALUE_TRAIT_NAME,
        },
        hash::Hasher,
        ordering::compare,
        string::String,
        value::{
            equal, native_layout_associated_consts, native_value_clone_function,
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

/// A finite floating-point value. The private NotNan field supplies ordering; constructors also
/// exclude infinities. Native arithmetic saturates overflow and reports invalid domains separately.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
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

fn invalid_real_argument(message: StdString) -> SourceFailureKind {
    SourceFailureKind::InvalidArgument(message)
}

fn saturated_real_result(value: f64) -> Float {
    Float::new_saturating(value)
}

extern "C" fn isize_to_float(value: isize) -> Float {
    // An isize always converts to a finite f64.
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

extern "C" fn shift_left(value: Int, shift: Int) -> Int {
    if shift < 0 {
        let shift = clamped_negated_shift_to_u32(shift);
        value.wrapping_shr(shift)
    } else {
        let shift = clamp_to_u32(shift);
        value.wrapping_shl(shift)
    }
}

extern "C" fn shift_right(value: Int, shift: Int) -> Int {
    if shift < 0 {
        let shift = clamped_negated_shift_to_u32(shift);
        value.wrapping_shl(shift)
    } else {
        let shift = clamp_to_u32(shift);
        value.wrapping_shr(shift)
    }
}

extern "C" fn rotate_left(value: Int, shift: Int) -> Int {
    if shift < 0 {
        let shift = clamped_negated_shift_to_u32(shift);
        value.rotate_right(shift)
    } else {
        let shift = clamp_to_u32(shift);
        value.rotate_left(shift)
    }
}

extern "C" fn rotate_right(value: Int, shift: Int) -> Int {
    if shift < 0 {
        let shift = clamped_negated_shift_to_u32(shift);
        value.rotate_left(shift)
    } else {
        let shift = clamp_to_u32(shift);
        value.rotate_right(shift)
    }
}

extern "C" fn count_ones(value: Int) -> Int {
    value.count_ones() as Int
}

extern "C" fn count_zeros(value: Int) -> Int {
    value.count_zeros() as Int
}

extern "C" fn bit(position: Int) -> Int {
    if position < 0 {
        return 0;
    }
    let position = clamp_to_u32(position);
    (1 as Int).checked_shl(position).unwrap_or(0)
}

extern "C" fn set_bit(value: Int, position: Int) -> Int {
    value | bit(position)
}

extern "C" fn clear_bit(value: Int, position: Int) -> Int {
    value & !bit(position)
}

extern "C" fn test_bit(value: Int, position: Int) -> bool {
    (value & bit(position)) != 0
}

fn int_to_string(value: Int) -> String {
    String::new(&value.to_string())
}

extern "C" fn hash_int(value: Int, state: &mut Hasher) {
    state.write_isize(value);
}

extern "C" fn hash_float(value: Float, state: &mut Hasher) {
    state.write_u64(value.into_inner().to_bits());
}

extern "C" fn add_float(lhs: Float, rhs: Float) -> Float {
    Float::new_saturating(lhs.into_inner() + rhs.into_inner())
}

extern "C" fn sub_float(lhs: Float, rhs: Float) -> Float {
    Float::new_saturating(lhs.into_inner() - rhs.into_inner())
}

extern "C" fn mul_float(lhs: Float, rhs: Float) -> Float {
    Float::new_saturating(lhs.into_inner() * rhs.into_inner())
}

fn div_float(lhs: Float, rhs: Float) -> Result<Float, SourceFailureKind> {
    let lhs = lhs.into_inner();
    let rhs = rhs.into_inner();
    if rhs == 0.0 {
        Err(SourceFailureKind::DivisionByZero)
    } else {
        Ok(Float::new_saturating(lhs / rhs))
    }
}

extern "C" fn sin_float(value: Float) -> Float {
    saturated_real_result(value.into_inner().sin())
}

extern "C" fn cos_float(value: Float) -> Float {
    saturated_real_result(value.into_inner().cos())
}

extern "C" fn tan_float(value: Float) -> Float {
    saturated_real_result(value.into_inner().tan())
}

fn asin_float(value: Float) -> Result<Float, SourceFailureKind> {
    let value = value.into_inner();
    Float::new(value.asin()).map_err(|_| {
        invalid_real_argument(format!(
            "Taking the arcsine of {value} is undefined because it is outside [-1, 1]"
        ))
    })
}

fn acos_float(value: Float) -> Result<Float, SourceFailureKind> {
    let value = value.into_inner();
    Float::new(value.acos()).map_err(|_| {
        invalid_real_argument(format!(
            "Taking the arccosine of {value} is undefined because it is outside [-1, 1]"
        ))
    })
}

extern "C" fn atan_float(value: Float) -> Float {
    saturated_real_result(value.into_inner().atan())
}

extern "C" fn atan2_float(y: Float, x: Float) -> Float {
    saturated_real_result(y.into_inner().atan2(x.into_inner()))
}

extern "C" fn sinh_float(value: Float) -> Float {
    saturated_real_result(value.into_inner().sinh())
}

extern "C" fn cosh_float(value: Float) -> Float {
    saturated_real_result(value.into_inner().cosh())
}

extern "C" fn tanh_float(value: Float) -> Float {
    saturated_real_result(value.into_inner().tanh())
}

extern "C" fn asinh_float(value: Float) -> Float {
    saturated_real_result(value.into_inner().asinh())
}

fn acosh_float(value: Float) -> Result<Float, SourceFailureKind> {
    let value = value.into_inner();
    Float::new(value.acosh()).map_err(|_| {
        invalid_real_argument(format!(
            "Taking the inverse hyperbolic cosine of {value} is undefined because it is less than 1"
        ))
    })
}

fn atanh_float(value: Float) -> Result<Float, SourceFailureKind> {
    let value = value.into_inner();
    Float::new(value.atanh()).map_err(|_| {
        invalid_real_argument(format!(
            "Taking the inverse hyperbolic tangent of {value} is undefined because it is outside (-1, 1)"
        ))
    })
}

extern "C" fn exp_float(value: Float) -> Float {
    saturated_real_result(value.into_inner().exp())
}

fn log_float(value: Float) -> Result<Float, SourceFailureKind> {
    let value = value.into_inner();
    Float::new(value.ln()).map_err(|_| {
        invalid_real_argument(format!(
            "Taking the logarithm of {value} is undefined because it is not positive"
        ))
    })
}

fn pow_float(base: Float, exponent: Float) -> Result<Float, SourceFailureKind> {
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

fn sqrt_float(value: Float) -> Result<Float, SourceFailureKind> {
    let value = value.into_inner();
    Float::new(value.sqrt()).map_err(|_| {
        invalid_real_argument(format!(
            "Taking the square root of {value} is undefined because it is negative"
        ))
    })
}

extern "C" fn neg_float(value: Float) -> Float {
    Float::new(-value.into_inner()).expect("negating a finite float should stay finite")
}

extern "C" fn round_float(value: Float) -> Int {
    value.round() as Int
}

extern "C" fn floor_float(value: Float) -> Int {
    value.floor() as Int
}

extern "C" fn ceil_float(value: Float) -> Int {
    value.ceil() as Int
}

fn float_to_string(value: Float) -> String {
    String::new(&value.to_string())
}

fn idiv(lhs: isize, rhs: isize) -> Result<isize, SourceFailureKind> {
    if rhs == 0 {
        Err(SourceFailureKind::DivisionByZero)
    } else {
        Ok(lhs.wrapping_div(rhs))
    }
}

fn idiv_euclid(lhs: isize, rhs: isize) -> Result<isize, SourceFailureKind> {
    if rhs == 0 {
        Err(SourceFailureKind::DivisionByZero)
    } else {
        Ok(lhs.wrapping_div_euclid(rhs))
    }
}

fn rem(lhs: isize, rhs: isize) -> Result<isize, SourceFailureKind> {
    if rhs == 0 {
        Err(SourceFailureKind::RemainderByZero)
    } else {
        Ok(lhs.wrapping_rem(rhs))
    }
}

fn modulo(lhs: isize, rhs: isize) -> Result<isize, SourceFailureKind> {
    if rhs == 0 {
        Err(SourceFailureKind::RemainderByZero)
    } else {
        Ok(lhs.wrapping_rem_euclid(rhs))
    }
}

pub fn add_to_module(to: &mut Module) {
    let value_trait_id = to.expect_std_trait_id_in_current_module(VALUE_TRAIT_NAME);
    let inspect_trait_id = to.expect_std_trait_id_in_current_module(INSPECT_TRAIT_NAME);
    let num_trait_id = to.expect_std_trait_id_in_current_module(NUM_TRAIT_NAME);
    let bits_trait_id = to.expect_std_trait_id_in_current_module(BITS_TRAIT_NAME);
    let default_trait_id = to.expect_std_trait_id_in_current_module(DEFAULT_TRAIT_NAME);
    let trivial_copy_trait_id = to.expect_std_trait_id_in_current_module(TRIVIAL_COPY_TRAIT_NAME);
    let div_trait_id = to.expect_std_trait_id_in_current_module(DIV_TRAIT_NAME);
    let real_trait_id = to.expect_std_trait_id_in_current_module(REAL_TRAIT_NAME);
    let cast_trait_id = to.expect_std_trait_id_in_current_module(CAST_TRAIT_NAME);

    // Types
    // Note: aliases are added in core.rs

    // Trait implementations

    // int
    to.add_concrete_impl_no_locals(
        value_trait_id,
        [int_type()],
        [],
        native_layout_associated_consts::<Int>(),
        [
            b(NativeFnNN::new(equal::<Int>)) as Function,
            b(NativeOutFnN::from_rust(int_to_string)) as Function,
            b(NativeFnNM::new(hash_int)) as Function,
            native_value_clone_function::<Int>(),
            native_value_drop_function::<Int>(),
        ],
    );
    to.add_concrete_impl_no_locals(
        inspect_trait_id,
        [int_type()],
        [],
        [],
        [b(NativeFallibleOutFnN::from_rust_infallible(int_to_string)) as Function],
    );
    to.add_native_concrete_impl(
        num_trait_id,
        [int_type()],
        [],
        [
            b(NativeFnNN::from_rust(Int::wrapping_add)) as Function,
            b(NativeFnNN::from_rust(Int::wrapping_sub)) as Function,
            b(NativeFnNN::from_rust(Int::wrapping_mul)) as Function,
            b(NativeFnN::from_rust(Int::wrapping_neg)) as Function,
            b(NativeFnN::from_rust(Int::wrapping_abs)) as Function,
            b(NativeFnN::from_rust(Int::signum)) as Function,
            b(NativeFnN::from_rust(std::convert::identity::<Int>)) as Function,
        ],
    );
    to.add_native_concrete_impl(
        bits_trait_id,
        [int_type()],
        [],
        [
            b(NativeFnNN::from_rust(<Int as std::ops::BitAnd>::bitand)) as Function,
            b(NativeFnNN::from_rust(<Int as std::ops::BitOr>::bitor)) as Function,
            b(NativeFnNN::from_rust(<Int as std::ops::BitXor>::bitxor)) as Function,
            b(NativeFnN::from_rust(<Int as std::ops::Not>::not)) as Function,
            b(NativeFnNN::new(shift_left)) as Function,
            b(NativeFnNN::new(shift_right)) as Function,
            b(NativeFnNN::new(rotate_left)) as Function,
            b(NativeFnNN::new(rotate_right)) as Function,
            b(NativeFnN::new(count_ones)) as Function,
            b(NativeFnN::new(count_zeros)) as Function,
            b(NativeFnN::new(bit)) as Function,
            b(NativeFnNN::new(set_bit)) as Function,
            b(NativeFnNN::new(clear_bit)) as Function,
            b(NativeFnNN::new(test_bit)) as Function,
        ],
    );
    to.add_function_with_visibility(
        ustr("compare_int_code"),
        NativeFnNN::from_rust_ordering_code(compare::<Int>).description(
            ["left", "right"],
            "Internal comparison code.",
            no_effects(),
        ),
        crate::module::Visibility::Module,
    );
    to.add_native_concrete_impl(
        default_trait_id,
        [int_type()],
        [],
        [b(NativeFn0::from_rust(|| 0isize)) as Function],
    );
    to.add_native_concrete_impl(
        trivial_copy_trait_id,
        [int_type()],
        [],
        Vec::<Function>::new(),
    );
    to.add_function(
        ustr("idiv"),
        NativeFallibleOutFnNN::from_rust(idiv).description(
            ["left", "right"],
            "Divides `left` by `right` and truncates the result.",
            effect(PrimitiveEffect::Fallible),
        ),
    );
    to.add_function(
        ustr("idiv_euclid"),
        NativeFallibleOutFnNN::from_rust(idiv_euclid).description(
            ["left", "right"],
            "Calculates the quotient of the Euclidean division of `left` by `right`.",
            effect(PrimitiveEffect::Fallible),
        ),
    );
    to.add_function(
        ustr("rem"),
        NativeFallibleOutFnNN::from_rust(rem).description(
            ["left", "right"],
            "Calculates the remainder of the division of `left` by `right`.",
            effect(PrimitiveEffect::Fallible),
        ),
    );
    to.add_function(
        ustr("mod"),
        NativeFallibleOutFnNN::from_rust(modulo).description(
            ["left", "right"],
            "Calculates the modulo of the division of `left` by `right`.",
            effect(PrimitiveEffect::Fallible),
        ),
    );

    // float
    to.add_concrete_impl_no_locals(
        value_trait_id,
        [float_type()],
        [],
        native_layout_associated_consts::<Float>(),
        [
            b(NativeFnNN::new(equal::<Float>)) as Function,
            b(NativeOutFnN::from_rust(float_to_string)) as Function,
            b(NativeFnNM::new(hash_float)) as Function,
            native_value_clone_function::<Float>(),
            native_value_drop_function::<Float>(),
        ],
    );
    to.add_concrete_impl_no_locals(
        inspect_trait_id,
        [float_type()],
        [],
        [],
        [b(NativeFallibleOutFnN::from_rust_infallible(float_to_string)) as Function],
    );
    to.add_native_concrete_impl(
        num_trait_id,
        [float_type()],
        [],
        [
            b(NativeFnNN::new(add_float)) as Function,
            b(NativeFnNN::new(sub_float)) as Function,
            b(NativeFnNN::new(mul_float)) as Function,
            b(NativeFnN::new(neg_float)) as Function,
            b(NativeFnN::from_rust(Float::abs)) as Function,
            b(NativeFnN::from_rust(Float::signum)) as Function,
            b(NativeFnN::new(isize_to_float)) as Function,
        ],
    );
    to.add_function_with_visibility(
        ustr("compare_float_code"),
        NativeFnNN::from_rust_ordering_code(compare::<Float>).description(
            ["left", "right"],
            "Internal comparison code.",
            no_effects(),
        ),
        crate::module::Visibility::Module,
    );
    to.add_native_concrete_impl(
        div_trait_id,
        [float_type()],
        [],
        [b(NativeFallibleOutFnNN::from_rust(div_float)) as Function],
    );
    to.add_native_concrete_impl(
        trivial_copy_trait_id,
        [float_type()],
        [],
        Vec::<Function>::new(),
    );
    to.add_concrete_impl_no_locals(
        real_trait_id,
        [float_type()],
        [],
        vec![
            LiteralValue::new_native(Float::new(std::f64::consts::PI).unwrap()),
            LiteralValue::new_native(Float::new(std::f64::consts::TAU).unwrap()),
            LiteralValue::new_native(Float::new(std::f64::consts::E).unwrap()),
        ],
        [
            b(NativeFnN::new(sin_float)) as Function,
            b(NativeFnN::new(cos_float)) as Function,
            b(NativeFnN::new(tan_float)) as Function,
            b(NativeFallibleOutFnN::from_rust(asin_float)) as Function,
            b(NativeFallibleOutFnN::from_rust(acos_float)) as Function,
            b(NativeFnN::new(atan_float)) as Function,
            b(NativeFnNN::new(atan2_float)) as Function,
            b(NativeFnN::new(sinh_float)) as Function,
            b(NativeFnN::new(cosh_float)) as Function,
            b(NativeFnN::new(tanh_float)) as Function,
            b(NativeFnN::new(asinh_float)) as Function,
            b(NativeFallibleOutFnN::from_rust(acosh_float)) as Function,
            b(NativeFallibleOutFnN::from_rust(atanh_float)) as Function,
            b(NativeFnN::new(exp_float)) as Function,
            b(NativeFallibleOutFnN::from_rust(log_float)) as Function,
            b(NativeFallibleOutFnNN::from_rust(pow_float)) as Function,
            b(NativeFallibleOutFnN::from_rust(sqrt_float)) as Function,
        ],
    );
    to.add_native_concrete_impl(
        default_trait_id,
        [float_type()],
        [],
        [b(NativeFn0::from_rust(|| Float::new(0.0).unwrap())) as Function],
    );
    to.add_function(
        ustr("round"),
        NativeFnN::new(round_float).description(
            ["value"],
            "Rounds a number to the nearest integer, saturating if necessary.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("floor"),
        NativeFnN::new(floor_float).description(
            ["value"],
            "Rounds a number down to the nearest integer, saturating if necessary.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("ceil"),
        NativeFnN::new(ceil_float).description(
            ["value"],
            "Rounds a number up to the nearest integer, saturating if necessary.",
            no_effects(),
        ),
    );

    // conversions
    to.add_native_concrete_impl(
        cast_trait_id,
        [int_type(), float_type()],
        [],
        [b(NativeFallibleOutFnN::from_rust_infallible(
            saturating_cast_int_to_float::<Int>,
        )) as Function],
    );
    to.add_native_concrete_impl(
        cast_trait_id,
        [float_type(), int_type()],
        [],
        [b(NativeFallibleOutFnN::from_rust_infallible(
            saturating_trunc::<Int>,
        )) as Function],
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn float_native_bodies_preserve_finiteness_at_boundaries() {
        // Include both signed zeros, subnormals, domain boundaries and their neighbors,
        // transcendental overflow inputs, and the largest finite values. A panic in a C body
        // aborts this test process, so this also exercises the native no-panic contract.
        let values: Vec<_> = [
            0.0,
            f64::from_bits(1),
            f64::MIN_POSITIVE,
            0.5,
            1.0_f64.next_down(),
            1.0,
            1.0_f64.next_up(),
            std::f64::consts::FRAC_PI_2,
            2.0,
            1000.0,
            f64::MAX,
        ]
        .into_iter()
        .flat_map(|value| [-value, value])
        .map(|value| Float::new(value).unwrap())
        .collect();
        let unary: [(_, extern "C" fn(Float) -> Float); 10] = [
            ("sin", sin_float),
            ("cos", cos_float),
            ("tan", tan_float),
            ("atan", atan_float),
            ("sinh", sinh_float),
            ("cosh", cosh_float),
            ("tanh", tanh_float),
            ("asinh", asinh_float),
            ("exp", exp_float),
            ("neg", neg_float),
        ];
        let binary: [(_, extern "C" fn(Float, Float) -> Float); 4] = [
            ("add", add_float),
            ("sub", sub_float),
            ("mul", mul_float),
            ("atan2", atan2_float),
        ];
        type CheckedUnary = fn(Float) -> Result<Float, SourceFailureKind>;
        let checked: [(_, CheckedUnary); 6] = [
            ("asin", asin_float),
            ("acos", acos_float),
            ("acosh", acosh_float),
            ("atanh", atanh_float),
            ("log", log_float),
            ("sqrt", sqrt_float),
        ];
        for &value in &values {
            for (name, function) in unary {
                assert!(function(value).into_inner().is_finite(), "{name}({value})");
            }
            for (name, function) in checked {
                if let Ok(result) = function(value) {
                    assert!(result.into_inner().is_finite(), "{name}({value})");
                }
            }
            assert!(value.abs().into_inner().is_finite());
            assert!(value.signum().into_inner().is_finite());
            for &other in &values {
                for (name, function) in binary {
                    assert!(
                        function(value, other).into_inner().is_finite(),
                        "{name}({value}, {other})"
                    );
                }
                for result in [div_float(value, other), pow_float(value, other)]
                    .into_iter()
                    .flatten()
                {
                    assert!(result.into_inner().is_finite(), "{value}, {other}");
                }
            }
        }
    }
}
