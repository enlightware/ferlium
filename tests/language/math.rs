// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;
use ustr::ustr;

use ferlium::compiler::error::RuntimeErrorKind;

use crate::harness::{TestSession, bool, float, int};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn type_defaulting() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("0"), int(0));
    assert_val_eq!(session.run("1 + 1"), int(2));
    assert_val_eq!(session.run("1 + 1 < 1 + 2"), bool(true));
    assert_val_eq!(session.run("1 / 1"), float(1.0));
    assert_val_eq!(session.run("0.0"), float(0.0));
    assert_val_eq!(session.run("1 + 1.0"), float(2.0));
    assert_val_eq!(session.run("1 + 1 < 1 + 1.5"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn num() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("abs(1)"), int(1));
    assert_val_eq!(session.run("abs(-1)"), int(1));
    assert_val_eq!(session.run("signum(3)"), int(1));
    assert_val_eq!(session.run("signum(0)"), int(0));
    assert_val_eq!(session.run("signum(-3)"), int(-1));
    assert_val_eq!(session.run("abs(1.0)"), float(1.0));
    assert_val_eq!(session.run("abs(-1.0)"), float(1.0));
    assert_val_eq!(session.run("signum(3.0)"), float(1.0));
    assert_val_eq!(session.run("signum(-3.0)"), float(-1.0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_div() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("idiv(7, 2)"), int(3));
    assert_val_eq!(session.run("idiv(-7, 2)"), int(-3));
    assert_val_eq!(session.run("idiv(idiv(12, 3), 2)"), int(2));
    assert_val_eq!(session.run("idiv(12, idiv(3, 2))"), int(12));
    assert_val_eq!(session.run("idiv_euclid(7, 2)"), int(3));
    assert_val_eq!(session.run("idiv_euclid(-7, 2)"), int(-4));
    assert_val_eq!(session.run("rem(0, 3)"), int(0));
    assert_val_eq!(session.run("rem(1, 3)"), int(1));
    assert_val_eq!(session.run("rem(2, 3)"), int(2));
    assert_val_eq!(session.run("rem(3, 3)"), int(0));
    assert_val_eq!(session.run("rem(4, 3)"), int(1));
    assert_val_eq!(session.run("rem(5, 3)"), int(2));
    assert_val_eq!(session.run("rem(-1, 3)"), int(-1));
    assert_val_eq!(session.run("rem(-2, 3)"), int(-2));
    assert_val_eq!(session.run("rem(-3, 3)"), int(-0));
    assert_val_eq!(session.run("rem(-4, 3)"), int(-1));
    assert_val_eq!(session.run("rem(-5, 3)"), int(-2));
    assert_val_eq!(session.run("mod(0, 3)"), int(0));
    assert_val_eq!(session.run("mod(1, 3)"), int(1));
    assert_val_eq!(session.run("mod(2, 3)"), int(2));
    assert_val_eq!(session.run("mod(3, 3)"), int(0));
    assert_val_eq!(session.run("mod(4, 3)"), int(1));
    assert_val_eq!(session.run("mod(5, 3)"), int(2));
    assert_val_eq!(session.run("mod(-1, 3)"), int(2));
    assert_val_eq!(session.run("mod(-2, 3)"), int(1));
    assert_val_eq!(session.run("mod(-3, 3)"), int(0));
    assert_val_eq!(session.run("mod(-4, 3)"), int(2));
    assert_val_eq!(session.run("mod(-5, 3)"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn min() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("min(1, 1)"), int(1));
    assert_val_eq!(session.run("min(1, 2)"), int(1));
    assert_val_eq!(session.run("min(2, 1)"), int(1));
    assert_val_eq!(session.run("min(1.0, 1.0)"), float(1.0));
    assert_val_eq!(session.run("min(1.0, 2.0)"), float(1.0));
    assert_val_eq!(session.run("min(2.0, 1.0)"), float(1.0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn max() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("max(1, 1)"), int(1));
    assert_val_eq!(session.run("max(1, 2)"), int(2));
    assert_val_eq!(session.run("max(2, 1)"), int(2));
    assert_val_eq!(session.run("max(1.0, 1.0)"), float(1.0));
    assert_val_eq!(session.run("max(1.0, 2.0)"), float(2.0));
    assert_val_eq!(session.run("max(2.0, 1.0)"), float(2.0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn clamp() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("clamp(-2, -1, 3)"), int(-1));
    assert_val_eq!(session.run("clamp(-1, -1, 3)"), int(-1));
    assert_val_eq!(session.run("clamp(0, -1, 3)"), int(0));
    assert_val_eq!(session.run("clamp(2, -1, 3)"), int(2));
    assert_val_eq!(session.run("clamp(3, -1, 3)"), int(3));
    assert_val_eq!(session.run("clamp(4, -1, 3)"), int(3));
    assert_val_eq!(session.run("clamp(0, 3, 3)"), int(3));
    assert!(session.fail_run("clamp(0, 3, 2)").is_aborted());
    assert_val_eq!(session.run("clamp(-2.5, -1.5, 3.0)"), float(-1.5));
    assert_val_eq!(session.run("clamp(-1.5, -1.5, 3.0)"), float(-1.5));
    assert_val_eq!(session.run("clamp(0.0, -1.5, 3.0)"), float(0.0));
    assert_val_eq!(session.run("clamp(2.5, -1.5, 3.0)"), float(2.5));
    assert_val_eq!(session.run("clamp(3.0, -1.5, 3.0)"), float(3.0));
    assert_val_eq!(session.run("clamp(4.0, -1.5, 3.0)"), float(3.0));
    assert_val_eq!(session.run("clamp(0.0, 3.0, 3.0)"), float(3.0));
    assert!(session.fail_run("clamp(0.0, 3.0, 2.0)").is_aborted());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn math_conversions() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("round(1.0)"), int(1));
    assert_val_eq!(session.run("round(1.4)"), int(1));
    assert_val_eq!(session.run("round(1.5)"), int(2));
    assert_val_eq!(session.run("round(-1.5)"), int(-2));
    assert_val_eq!(session.run("floor(1.9)"), int(1));
    assert_val_eq!(session.run("floor(-1.1)"), int(-2));
    assert_val_eq!(session.run("ceil(1.1)"), int(2));
    assert_val_eq!(session.run("ceil(-1.9)"), int(-1));
    assert_val_eq!(session.run("(from_int(1): float)"), float(1.0));
    assert_val_eq!(
        session.run("fn round_trip(x) { round(from_int(x)) } round_trip(1)"),
        int(1)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn float_arithmetic_saturates_to_finite_bounds() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(r#"match parse_float("1e308") { Some(x) => x * x, None => 0.0 }"#),
        float(f64::MAX)
    );
    assert_val_eq!(
        session.run(r#"match parse_float("-1e308") { Some(x) => x * x, None => 0.0 }"#),
        float(f64::MAX)
    );
    assert_val_eq!(
        session.run(r#"match parse_float("-1e308") { Some(x) => x / 0.5, None => 0.0 }"#),
        float(-f64::MAX)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn real() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("sin(0.0)"), float(0.0));
    assert_val_eq!(session.run("cos(0.0)"), float(1.0));
    assert_val_eq!(session.run("tan(0.0)"), float(0.0));
    assert_val_eq!(session.run("asin(0.0)"), float(0.0));
    assert_val_eq!(session.run("acos(1.0)"), float(0.0));
    assert_val_eq!(session.run("atan(0.0)"), float(0.0));
    assert_val_eq!(session.run("atan2(0.0, 0.0)"), float(0.0));

    assert_val_eq!(session.run("sinh(0.0)"), float(0.0));
    assert_val_eq!(session.run("cosh(0.0)"), float(1.0));
    assert_val_eq!(session.run("tanh(0.0)"), float(0.0));
    assert_val_eq!(session.run("asinh(0.0)"), float(0.0));
    assert_val_eq!(session.run("acosh(1.0)"), float(0.0));
    assert_val_eq!(session.run("atanh(0.0)"), float(0.0));

    assert_val_eq!(session.run("exp(0.0)"), float(1.0));
    assert_val_eq!(session.run("log(1.0)"), float(0.0));
    assert_val_eq!(session.run("pow(2.0, 3.0)"), float(8.0));
    assert_val_eq!(session.run("sqrt(4.0)"), float(2.0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn real_domain_errors() {
    let mut session = TestSession::new();
    assert_eq!(
        session.fail_run("asin(2.0)"),
        RuntimeErrorKind::InvalidArgument(ustr(
            "Taking the arcsine of 2 is undefined because it is outside [-1, 1]"
        ))
    );
    assert_eq!(
        session.fail_run("acos(2.0)"),
        RuntimeErrorKind::InvalidArgument(ustr(
            "Taking the arccosine of 2 is undefined because it is outside [-1, 1]"
        ))
    );
    assert_eq!(
        session.fail_run("acosh(0.0)"),
        RuntimeErrorKind::InvalidArgument(ustr(
            "Taking the inverse hyperbolic cosine of 0 is undefined because it is less than 1"
        ))
    );
    assert_eq!(
        session.fail_run("atanh(1.0)"),
        RuntimeErrorKind::InvalidArgument(ustr(
            "Taking the inverse hyperbolic tangent of 1 is undefined because it is outside (-1, 1)"
        ))
    );
    assert_eq!(
        session.fail_run("log(0.0)"),
        RuntimeErrorKind::InvalidArgument(ustr(
            "Taking the logarithm of 0 is undefined because it is not positive"
        ))
    );
    assert_eq!(
        session.fail_run("pow(-1.0, 0.5)"),
        RuntimeErrorKind::InvalidArgument(ustr(
            "Raising -1 to the power 0.5 is undefined as a real number"
        ))
    );
    assert_eq!(
        session.fail_run("sqrt(-1.0)"),
        RuntimeErrorKind::InvalidArgument(ustr(
            "Taking the square root of -1 is undefined because it is negative"
        ))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn real_overflow_saturates_to_finite_bounds() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(r#"match parse_float("1000.0") { Some(x) => exp(x), None => 0.0 }"#),
        float(f64::MAX)
    );
    assert_val_eq!(
        session.run(r#"match parse_float("1000.0") { Some(x) => sinh(x), None => 0.0 }"#),
        float(f64::MAX)
    );
    assert_val_eq!(
        session.run(r#"match parse_float("1000.0") { Some(x) => cosh(x), None => 0.0 }"#),
        float(f64::MAX)
    );
    assert_val_eq!(
        session.run(r#"match parse_float("1e308") { Some(x) => pow(x, 2.0), None => 0.0 }"#),
        float(f64::MAX)
    );
}
