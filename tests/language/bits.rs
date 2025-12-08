// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;

use super::common::{TestSession, bool, int};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

// ============================================================================
// Integer Bit Operations
// ============================================================================

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_bit_and() {
    let mut session = TestSession::new();
    assert_eq!(session.run("bit_and(0, 0)"), int(0));
    assert_eq!(session.run("bit_and(0, 1)"), int(0));
    assert_eq!(session.run("bit_and(1, 0)"), int(0));
    assert_eq!(session.run("bit_and(1, 1)"), int(1));
    assert_eq!(session.run("bit_and(5, 3)"), int(1)); // 0b101 & 0b011 = 0b001
    assert_eq!(session.run("bit_and(15, 7)"), int(7)); // 0b1111 & 0b0111 = 0b0111
    assert_eq!(session.run("bit_and(-1, 7)"), int(7)); // all bits set & 0b0111
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_bit_or() {
    let mut session = TestSession::new();
    assert_eq!(session.run("bit_or(0, 0)"), int(0));
    assert_eq!(session.run("bit_or(0, 1)"), int(1));
    assert_eq!(session.run("bit_or(1, 0)"), int(1));
    assert_eq!(session.run("bit_or(1, 1)"), int(1));
    assert_eq!(session.run("bit_or(5, 3)"), int(7)); // 0b101 | 0b011 = 0b111
    assert_eq!(session.run("bit_or(8, 4)"), int(12)); // 0b1000 | 0b0100 = 0b1100
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_bit_xor() {
    let mut session = TestSession::new();
    assert_eq!(session.run("bit_xor(0, 0)"), int(0));
    assert_eq!(session.run("bit_xor(0, 1)"), int(1));
    assert_eq!(session.run("bit_xor(1, 0)"), int(1));
    assert_eq!(session.run("bit_xor(1, 1)"), int(0));
    assert_eq!(session.run("bit_xor(5, 3)"), int(6)); // 0b101 ^ 0b011 = 0b110
    assert_eq!(session.run("bit_xor(15, 7)"), int(8)); // 0b1111 ^ 0b0111 = 0b1000
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_bit_not() {
    let mut session = TestSession::new();
    assert_eq!(session.run("bit_not(0)"), int(-1));
    assert_eq!(session.run("bit_not(-1)"), int(0));
    assert_eq!(session.run("bit_not(1)"), int(-2));
    assert_eq!(session.run("bit_not(-2)"), int(1));
    // Double negation returns original
    assert_eq!(session.run("bit_not(bit_not(42))"), int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_shift_left() {
    let mut session = TestSession::new();
    assert_eq!(session.run("shift_left(1, 0)"), int(1));
    assert_eq!(session.run("shift_left(1, 1)"), int(2));
    assert_eq!(session.run("shift_left(1, 2)"), int(4));
    assert_eq!(session.run("shift_left(1, 3)"), int(8));
    assert_eq!(session.run("shift_left(5, 2)"), int(20)); // 0b101 << 2 = 0b10100
    assert_eq!(session.run("shift_left(7, 4)"), int(112)); // 0b111 << 4 = 0b1110000
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_shift_right() {
    let mut session = TestSession::new();
    assert_eq!(session.run("shift_right(8, 0)"), int(8));
    assert_eq!(session.run("shift_right(8, 1)"), int(4));
    assert_eq!(session.run("shift_right(8, 2)"), int(2));
    assert_eq!(session.run("shift_right(8, 3)"), int(1));
    assert_eq!(session.run("shift_right(8, 4)"), int(0));
    assert_eq!(session.run("shift_right(20, 2)"), int(5)); // 0b10100 >> 2 = 0b101
    assert_eq!(session.run("shift_right(112, 4)"), int(7)); // 0b1110000 >> 4 = 0b111
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_rotate_left() {
    let mut session = TestSession::new();
    // Rotating by 0 returns original
    assert_eq!(session.run("rotate_left(1, 0)"), int(1));
    // Basic rotations
    assert_eq!(session.run("rotate_left(1, 1)"), int(2));
    assert_eq!(session.run("rotate_left(1, 2)"), int(4));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_rotate_right() {
    let mut session = TestSession::new();
    // Rotating by 0 returns original
    assert_eq!(session.run("rotate_right(1, 0)"), int(1));
    // Basic rotations
    assert_eq!(session.run("rotate_right(2, 1)"), int(1));
    assert_eq!(session.run("rotate_right(4, 2)"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_count_ones() {
    let mut session = TestSession::new();
    assert_eq!(session.run("count_ones(0)"), int(0));
    assert_eq!(session.run("count_ones(1)"), int(1));
    assert_eq!(session.run("count_ones(3)"), int(2)); // 0b11
    assert_eq!(session.run("count_ones(7)"), int(3)); // 0b111
    assert_eq!(session.run("count_ones(15)"), int(4)); // 0b1111
    assert_eq!(session.run("count_ones(5)"), int(2)); // 0b101
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_count_zeros() {
    let mut session = TestSession::new();
    assert_eq!(session.run("count_zeros(-1)"), int(0)); // all bits set
    assert_eq!(
        session.run("count_zeros(0)"),
        int(std::mem::size_of::<isize>() as isize * 8)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_bit() {
    let mut session = TestSession::new();
    assert_eq!(session.run("(bit(0): int)"), int(1)); // 2^0
    assert_eq!(session.run("(bit(1): int)"), int(2)); // 2^1
    assert_eq!(session.run("(bit(2): int)"), int(4)); // 2^2
    assert_eq!(session.run("(bit(3): int)"), int(8)); // 2^3
    assert_eq!(session.run("(bit(4): int)"), int(16)); // 2^4
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_set_bit() {
    let mut session = TestSession::new();
    assert_eq!(session.run("set_bit(0, 0)"), int(1)); // set bit 0
    assert_eq!(session.run("set_bit(0, 1)"), int(2)); // set bit 1
    assert_eq!(session.run("set_bit(0, 2)"), int(4)); // set bit 2
    assert_eq!(session.run("set_bit(1, 1)"), int(3)); // 0b01 with bit 1 set = 0b11
    assert_eq!(session.run("set_bit(5, 1)"), int(7)); // 0b101 with bit 1 set = 0b111
    // Setting an already set bit doesn't change it
    assert_eq!(session.run("set_bit(1, 0)"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_clear_bit() {
    let mut session = TestSession::new();
    assert_eq!(session.run("clear_bit(1, 0)"), int(0)); // clear bit 0
    assert_eq!(session.run("clear_bit(2, 1)"), int(0)); // clear bit 1
    assert_eq!(session.run("clear_bit(7, 1)"), int(5)); // 0b111 with bit 1 cleared = 0b101
    assert_eq!(session.run("clear_bit(5, 2)"), int(1)); // 0b101 with bit 2 cleared = 0b001
    // Clearing an already cleared bit doesn't change it
    assert_eq!(session.run("clear_bit(0, 0)"), int(0));
    assert_eq!(session.run("clear_bit(2, 0)"), int(2));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_test_bit() {
    let mut session = TestSession::new();
    assert_eq!(session.run("test_bit(0, 0)"), bool(false));
    assert_eq!(session.run("test_bit(1, 0)"), bool(true));
    assert_eq!(session.run("test_bit(2, 0)"), bool(false));
    assert_eq!(session.run("test_bit(2, 1)"), bool(true));
    assert_eq!(session.run("test_bit(5, 0)"), bool(true)); // 0b101 bit 0 is set
    assert_eq!(session.run("test_bit(5, 1)"), bool(false)); // 0b101 bit 1 is not set
    assert_eq!(session.run("test_bit(5, 2)"), bool(true)); // 0b101 bit 2 is set
    assert_eq!(session.run("test_bit(7, 0)"), bool(true)); // 0b111
    assert_eq!(session.run("test_bit(7, 1)"), bool(true));
    assert_eq!(session.run("test_bit(7, 2)"), bool(true));
}

// ============================================================================
// Boolean Bit Operations
// ============================================================================

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_bit_and() {
    let mut session = TestSession::new();
    assert_eq!(session.run("bit_and(false, false)"), bool(false));
    assert_eq!(session.run("bit_and(false, true)"), bool(false));
    assert_eq!(session.run("bit_and(true, false)"), bool(false));
    assert_eq!(session.run("bit_and(true, true)"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_bit_or() {
    let mut session = TestSession::new();
    assert_eq!(session.run("bit_or(false, false)"), bool(false));
    assert_eq!(session.run("bit_or(false, true)"), bool(true));
    assert_eq!(session.run("bit_or(true, false)"), bool(true));
    assert_eq!(session.run("bit_or(true, true)"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_bit_xor() {
    let mut session = TestSession::new();
    assert_eq!(session.run("bit_xor(false, false)"), bool(false));
    assert_eq!(session.run("bit_xor(false, true)"), bool(true));
    assert_eq!(session.run("bit_xor(true, false)"), bool(true));
    assert_eq!(session.run("bit_xor(true, true)"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_bit_not() {
    let mut session = TestSession::new();
    assert_eq!(session.run("bit_not(false)"), bool(true));
    assert_eq!(session.run("bit_not(true)"), bool(false));
    // Double negation returns original
    assert_eq!(session.run("bit_not(bit_not(true))"), bool(true));
    assert_eq!(session.run("bit_not(bit_not(false))"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_shift_left() {
    let mut session = TestSession::new();
    // For bool, shift_left always returns false (see logic.rs implementation)
    assert_eq!(session.run("shift_left(false, 0)"), bool(false));
    assert_eq!(session.run("shift_left(false, 1)"), bool(false));
    assert_eq!(session.run("shift_left(true, 0)"), bool(false));
    assert_eq!(session.run("shift_left(true, 1)"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_shift_right() {
    let mut session = TestSession::new();
    // For bool, shift_right always returns false (see logic.rs implementation)
    assert_eq!(session.run("shift_right(false, 0)"), bool(false));
    assert_eq!(session.run("shift_right(false, 1)"), bool(false));
    assert_eq!(session.run("shift_right(true, 0)"), bool(false));
    assert_eq!(session.run("shift_right(true, 1)"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_rotate_left() {
    let mut session = TestSession::new();
    // For bool, rotate_left returns the identity (see logic.rs implementation)
    assert_eq!(session.run("rotate_left(false, 0)"), bool(false));
    assert_eq!(session.run("rotate_left(false, 1)"), bool(false));
    assert_eq!(session.run("rotate_left(true, 0)"), bool(true));
    assert_eq!(session.run("rotate_left(true, 1)"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_rotate_right() {
    let mut session = TestSession::new();
    // For bool, rotate_right returns the identity (see logic.rs implementation)
    assert_eq!(session.run("rotate_right(false, 0)"), bool(false));
    assert_eq!(session.run("rotate_right(false, 1)"), bool(false));
    assert_eq!(session.run("rotate_right(true, 0)"), bool(true));
    assert_eq!(session.run("rotate_right(true, 1)"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_count_ones() {
    let mut session = TestSession::new();
    assert_eq!(session.run("count_ones(false)"), int(0));
    assert_eq!(session.run("count_ones(true)"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_count_zeros() {
    let mut session = TestSession::new();
    assert_eq!(session.run("count_zeros(false)"), int(1));
    assert_eq!(session.run("count_zeros(true)"), int(0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_bit() {
    let mut session = TestSession::new();
    // bit(0) returns true, any other position returns false
    assert_eq!(session.run("(bit(0): bool)"), bool(true));
    assert_eq!(session.run("(bit(1): bool)"), bool(false));
    assert_eq!(session.run("(bit(2): bool)"), bool(false));
    assert_eq!(session.run("(bit(-1): bool)"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_set_bit() {
    let mut session = TestSession::new();
    // set_bit at position 0 sets to true, other positions leave unchanged
    assert_eq!(session.run("set_bit(false, 0)"), bool(true));
    assert_eq!(session.run("set_bit(true, 0)"), bool(true));
    assert_eq!(session.run("set_bit(false, 1)"), bool(false));
    assert_eq!(session.run("set_bit(true, 1)"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_clear_bit() {
    let mut session = TestSession::new();
    // clear_bit at position 0 sets to false, other positions leave unchanged
    assert_eq!(session.run("clear_bit(false, 0)"), bool(false));
    assert_eq!(session.run("clear_bit(true, 0)"), bool(false));
    assert_eq!(session.run("clear_bit(false, 1)"), bool(false));
    assert_eq!(session.run("clear_bit(true, 1)"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_test_bit() {
    let mut session = TestSession::new();
    // test_bit at position 0 returns the value, other positions return false
    assert_eq!(session.run("test_bit(false, 0)"), bool(false));
    assert_eq!(session.run("test_bit(true, 0)"), bool(true));
    assert_eq!(session.run("test_bit(false, 1)"), bool(false));
    assert_eq!(session.run("test_bit(true, 1)"), bool(false));
    assert_eq!(session.run("test_bit(false, -1)"), bool(false));
    assert_eq!(session.run("test_bit(true, -1)"), bool(false));
}

// ============================================================================
// Combined Operations
// ============================================================================

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_combined_operations() {
    let mut session = TestSession::new();
    // Combining set_bit and test_bit
    assert_eq!(
        session.run("let x = set_bit(0, 3); test_bit(x, 3)"),
        bool(true)
    );
    assert_eq!(
        session.run("let x = set_bit(0, 3); test_bit(x, 2)"),
        bool(false)
    );

    // Combining clear_bit and test_bit
    assert_eq!(
        session.run("let x = clear_bit(15, 2); test_bit(x, 2)"),
        bool(false)
    );
    assert_eq!(session.run("let x = clear_bit(15, 2); x"), int(11)); // 0b1111 -> 0b1011

    // count_ones with bit operations
    assert_eq!(session.run("count_ones(bit_or(5, 3))"), int(3)); // 0b111 has 3 ones
    assert_eq!(session.run("count_ones(bit_and(5, 3))"), int(1)); // 0b001 has 1 one
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_combined_operations() {
    let mut session = TestSession::new();
    // Combining operations
    assert_eq!(
        session.run("bit_and(bit_or(true, false), true)"),
        bool(true)
    );
    assert_eq!(
        session.run("bit_xor(bit_and(true, true), false)"),
        bool(true)
    );
    assert_eq!(session.run("bit_not(bit_xor(true, true))"), bool(true));

    // count_ones with bit operations
    assert_eq!(session.run("count_ones(bit_or(false, false))"), int(0));
    assert_eq!(session.run("count_ones(bit_or(true, false))"), int(1));
}
