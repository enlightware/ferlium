// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;

use crate::common::fail_run;

use super::common::{bool, float, int, run};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn type_defaulting() {
    assert_eq!(run("0"), int(0));
    assert_eq!(run("1 + 1"), int(2));
    assert_eq!(run("1 + 1 < 1 + 2"), bool(true));
    assert_eq!(run("1 / 1"), float(1.0));
    assert_eq!(run("0.0"), float(0.0));
    assert_eq!(run("1 + 1.0"), float(2.0));
    assert_eq!(run("1 + 1 < 1 + 1.5"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn num() {
    assert_eq!(run("abs(1)"), int(1));
    assert_eq!(run("abs(-1)"), int(1));
    assert_eq!(run("signum(3)"), int(1));
    assert_eq!(run("signum(0)"), int(0));
    assert_eq!(run("signum(-3)"), int(-1));
    assert_eq!(run("abs(1.0)"), float(1.0));
    assert_eq!(run("abs(-1.0)"), float(1.0));
    assert_eq!(run("signum(3.0)"), float(1.0));
    assert_eq!(run("signum(-3.0)"), float(-1.0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_div() {
    assert_eq!(run("idiv(7, 2)"), int(3));
    assert_eq!(run("idiv(idiv(12, 3), 2)"), int(2));
    assert_eq!(run("idiv(12, idiv(3, 2))"), int(12));
    assert_eq!(run("rem(0, 3)"), int(0));
    assert_eq!(run("rem(1, 3)"), int(1));
    assert_eq!(run("rem(2, 3)"), int(2));
    assert_eq!(run("rem(3, 3)"), int(0));
    assert_eq!(run("rem(4, 3)"), int(1));
    assert_eq!(run("rem(5, 3)"), int(2));
    assert_eq!(run("rem(-1, 3)"), int(-1));
    assert_eq!(run("rem(-2, 3)"), int(-2));
    assert_eq!(run("rem(-3, 3)"), int(-0));
    assert_eq!(run("rem(-4, 3)"), int(-1));
    assert_eq!(run("rem(-5, 3)"), int(-2));
    assert_eq!(run("mod(0, 3)"), int(0));
    assert_eq!(run("mod(1, 3)"), int(1));
    assert_eq!(run("mod(2, 3)"), int(2));
    assert_eq!(run("mod(3, 3)"), int(0));
    assert_eq!(run("mod(4, 3)"), int(1));
    assert_eq!(run("mod(5, 3)"), int(2));
    assert_eq!(run("mod(-1, 3)"), int(2));
    assert_eq!(run("mod(-2, 3)"), int(1));
    assert_eq!(run("mod(-3, 3)"), int(0));
    assert_eq!(run("mod(-4, 3)"), int(2));
    assert_eq!(run("mod(-5, 3)"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn min() {
    assert_eq!(run("min(1, 1)"), int(1));
    assert_eq!(run("min(1, 2)"), int(1));
    assert_eq!(run("min(2, 1)"), int(1));
    assert_eq!(run("min(1.0, 1.0)"), float(1.0));
    assert_eq!(run("min(1.0, 2.0)"), float(1.0));
    assert_eq!(run("min(2.0, 1.0)"), float(1.0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn max() {
    assert_eq!(run("max(1, 1)"), int(1));
    assert_eq!(run("max(1, 2)"), int(2));
    assert_eq!(run("max(2, 1)"), int(2));
    assert_eq!(run("max(1.0, 1.0)"), float(1.0));
    assert_eq!(run("max(1.0, 2.0)"), float(2.0));
    assert_eq!(run("max(2.0, 1.0)"), float(2.0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn clamp() {
    assert_eq!(run("clamp(-2, -1, 3)"), int(-1));
    assert_eq!(run("clamp(-1, -1, 3)"), int(-1));
    assert_eq!(run("clamp(0, -1, 3)"), int(0));
    assert_eq!(run("clamp(2, -1, 3)"), int(2));
    assert_eq!(run("clamp(3, -1, 3)"), int(3));
    assert_eq!(run("clamp(4, -1, 3)"), int(3));
    assert_eq!(run("clamp(0, 3, 3)"), int(3));
    assert!(fail_run("clamp(0, 3, 2)").is_aborted());
    assert_eq!(run("clamp(-2.5, -1.5, 3.0)"), float(-1.5));
    assert_eq!(run("clamp(-1.5, -1.5, 3.0)"), float(-1.5));
    assert_eq!(run("clamp(0.0, -1.5, 3.0)"), float(0.0));
    assert_eq!(run("clamp(2.5, -1.5, 3.0)"), float(2.5));
    assert_eq!(run("clamp(3.0, -1.5, 3.0)"), float(3.0));
    assert_eq!(run("clamp(4.0, -1.5, 3.0)"), float(3.0));
    assert_eq!(run("clamp(0.0, 3.0, 3.0)"), float(3.0));
    assert!(fail_run("clamp(0.0, 3.0, 2.0)").is_aborted());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn math_conversions() {
    assert_eq!(run("round(1.0)"), int(1));
    assert_eq!(run("(from_int(1): float)"), float(1.0));
    assert_eq!(
        run("fn round_trip(x) { round(from_int(x)) } round_trip(1)"),
        int(1)
    );
}
