// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use test_log::test;

use crate::harness::{TestSession, bool, int};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

// ============================================================================
// Integer Bit Operations
// ============================================================================

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_bit_and() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("bit_and(0, 0)"), int(0));
    assert_val_eq!(session.run("bit_and(0, 1)"), int(0));
    assert_val_eq!(session.run("bit_and(1, 0)"), int(0));
    assert_val_eq!(session.run("bit_and(1, 1)"), int(1));
    assert_val_eq!(session.run("bit_and(5, 3)"), int(1)); // 0b101 & 0b011 = 0b001
    assert_val_eq!(session.run("bit_and(15, 7)"), int(7)); // 0b1111 & 0b0111 = 0b0111
    assert_val_eq!(session.run("bit_and(-1, 7)"), int(7)); // all bits set & 0b0111
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_bit_or() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("bit_or(0, 0)"), int(0));
    assert_val_eq!(session.run("bit_or(0, 1)"), int(1));
    assert_val_eq!(session.run("bit_or(1, 0)"), int(1));
    assert_val_eq!(session.run("bit_or(1, 1)"), int(1));
    assert_val_eq!(session.run("bit_or(5, 3)"), int(7)); // 0b101 | 0b011 = 0b111
    assert_val_eq!(session.run("bit_or(8, 4)"), int(12)); // 0b1000 | 0b0100 = 0b1100
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_bit_xor() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("bit_xor(0, 0)"), int(0));
    assert_val_eq!(session.run("bit_xor(0, 1)"), int(1));
    assert_val_eq!(session.run("bit_xor(1, 0)"), int(1));
    assert_val_eq!(session.run("bit_xor(1, 1)"), int(0));
    assert_val_eq!(session.run("bit_xor(5, 3)"), int(6)); // 0b101 ^ 0b011 = 0b110
    assert_val_eq!(session.run("bit_xor(15, 7)"), int(8)); // 0b1111 ^ 0b0111 = 0b1000
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_bit_not() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("bit_not(0)"), int(-1));
    assert_val_eq!(session.run("bit_not(-1)"), int(0));
    assert_val_eq!(session.run("bit_not(1)"), int(-2));
    assert_val_eq!(session.run("bit_not(-2)"), int(1));
    // Double negation returns original
    assert_val_eq!(session.run("bit_not(bit_not(42))"), int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_shift_left() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("shift_left(1, 0)"), int(1));
    assert_val_eq!(session.run("shift_left(1, 1)"), int(2));
    assert_val_eq!(session.run("shift_left(1, 2)"), int(4));
    assert_val_eq!(session.run("shift_left(1, 3)"), int(8));
    assert_val_eq!(session.run("shift_left(5, 2)"), int(20)); // 0b101 << 2 = 0b10100
    assert_val_eq!(session.run("shift_left(7, 4)"), int(112)); // 0b111 << 4 = 0b1110000
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_shift_right() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("shift_right(8, 0)"), int(8));
    assert_val_eq!(session.run("shift_right(8, 1)"), int(4));
    assert_val_eq!(session.run("shift_right(8, 2)"), int(2));
    assert_val_eq!(session.run("shift_right(8, 3)"), int(1));
    assert_val_eq!(session.run("shift_right(8, 4)"), int(0));
    assert_val_eq!(session.run("shift_right(20, 2)"), int(5)); // 0b10100 >> 2 = 0b101
    assert_val_eq!(session.run("shift_right(112, 4)"), int(7)); // 0b1110000 >> 4 = 0b111
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_shifts_discard_bits_and_reverse_negative_counts() {
    let mut session = TestSession::new();
    let setup =
        "let bits = count_zeros(0); let imin: int = bit(bits - 1); let imax = bit_not(imin);";
    let mut cases = vec![
        ("-8", "-bits - 1", -1, 0),
        ("-8", "-bits", -1, 0),
        ("-8", "1 - bits", -1, 0),
        ("-8", "-1", -4, -16),
        ("-8", "0", -8, -8),
        ("-8", "1", -16, -4),
        ("-8", "bits - 1", 0, -1),
        ("-8", "bits", 0, -1),
        ("-8", "bits + 1", 0, -1),
        ("-8", "imin", -1, 0),
        ("-8", "imax", 0, -1),
        ("1", "1 - bits", 0, isize::MIN),
        ("1", "bits - 1", isize::MIN, 0),
        ("1", "-bits", 0, 0),
        ("1", "bits", 0, 0),
        ("1", "imin", 0, 0),
        ("1", "imax", 0, 0),
        ("0", "imin", 0, 0),
        ("0", "imax", 0, 0),
        ("imin", "-1", isize::MIN / 2, 0),
        ("imin", "1", 0, isize::MIN / 2),
        ("imin", "imin", -1, 0),
        ("imin", "imax", 0, -1),
    ];
    if isize::BITS > 32 {
        cases.extend([("1", "4294967297", 0, 0), ("1", "-4294967297", 0, 0)]);
    }
    for (value, count, left, right) in cases {
        // Check both constant folding and calls whose operands are only known at runtime.
        for runtime in [false, true] {
            let operands = if runtime {
                format!("let value = black_box({value}); let count = black_box({count});")
            } else {
                format!("let value = {value}; let count = {count};")
            };
            for (operation, expected) in [("shift_left", left), ("shift_right", right)] {
                assert_val_eq!(
                    session.run(&format!("{setup} {operands} {operation}(value, count)")),
                    int(expected)
                );
            }
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_rotate_left() {
    let mut session = TestSession::new();
    // Rotating by 0 returns original
    assert_val_eq!(session.run("rotate_left(1, 0)"), int(1));
    // Basic rotations
    assert_val_eq!(session.run("rotate_left(1, 1)"), int(2));
    assert_val_eq!(session.run("rotate_left(1, 2)"), int(4));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_rotate_right() {
    let mut session = TestSession::new();
    // Rotating by 0 returns original
    assert_val_eq!(session.run("rotate_right(1, 0)"), int(1));
    // Basic rotations
    assert_val_eq!(session.run("rotate_right(2, 1)"), int(1));
    assert_val_eq!(session.run("rotate_right(4, 2)"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_rotations_wrap_signed_counts_modulo_the_width() {
    let mut session = TestSession::new();
    let setup =
        "let bits = count_zeros(0); let imin: int = bit(bits - 1); let imax = bit_not(imin);";
    let mut cases = vec![
        ("5", "-bits - 1", isize::MIN + 2, 10),
        ("5", "-bits", 5, 5),
        ("5", "1 - bits", 10, isize::MIN + 2),
        ("5", "-1", isize::MIN + 2, 10),
        ("5", "0", 5, 5),
        ("5", "1", 10, isize::MIN + 2),
        ("5", "bits - 1", isize::MIN + 2, 10),
        ("5", "bits", 5, 5),
        ("5", "bits + 1", 10, isize::MIN + 2),
        ("5", "imin", 5, 5),
        ("5", "imin + 1", 10, isize::MIN + 2),
        ("5", "imax - 1", -(isize::MIN / 2) + 1, 20),
        ("5", "imax", isize::MIN + 2, 10),
        ("-8", "1", -15, isize::MAX - 3),
        ("-8", "-1", isize::MAX - 3, -15),
        ("-8", "bits", -8, -8),
        ("-8", "imin", -8, -8),
    ];
    if isize::BITS > 32 {
        // Counts wider than u32 still use their actual remainder, without saturation.
        cases.extend([
            ("5", "4294967297", 10, isize::MIN + 2),
            ("5", "-4294967297", isize::MIN + 2, 10),
        ]);
    }
    for (value, count, left, right) in cases {
        for runtime in [false, true] {
            let operands = if runtime {
                format!("let value = black_box({value}); let count = black_box({count});")
            } else {
                format!("let value = {value}; let count = {count};")
            };
            for (operation, expected) in [("rotate_left", left), ("rotate_right", right)] {
                assert_val_eq!(
                    session.run(&format!("{setup} {operands} {operation}(value, count)")),
                    int(expected)
                );
            }
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_count_ones() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("count_ones(0)"), int(0));
    assert_val_eq!(session.run("count_ones(1)"), int(1));
    assert_val_eq!(session.run("count_ones(3)"), int(2)); // 0b11
    assert_val_eq!(session.run("count_ones(7)"), int(3)); // 0b111
    assert_val_eq!(session.run("count_ones(15)"), int(4)); // 0b1111
    assert_val_eq!(session.run("count_ones(5)"), int(2)); // 0b101
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_count_zeros() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("count_zeros(-1)"), int(0)); // all bits set
    assert_val_eq!(
        session.run("count_zeros(0)"),
        int(std::mem::size_of::<isize>() as isize * 8)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_bit() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("(bit(0): int)"), int(1)); // 2^0
    assert_val_eq!(session.run("(bit(1): int)"), int(2)); // 2^1
    assert_val_eq!(session.run("(bit(2): int)"), int(4)); // 2^2
    assert_val_eq!(session.run("(bit(3): int)"), int(8)); // 2^3
    assert_val_eq!(session.run("(bit(4): int)"), int(16)); // 2^4
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_set_bit() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("set_bit(0, 0)"), int(1)); // set bit 0
    assert_val_eq!(session.run("set_bit(0, 1)"), int(2)); // set bit 1
    assert_val_eq!(session.run("set_bit(0, 2)"), int(4)); // set bit 2
    assert_val_eq!(session.run("set_bit(1, 1)"), int(3)); // 0b01 with bit 1 set = 0b11
    assert_val_eq!(session.run("set_bit(5, 1)"), int(7)); // 0b101 with bit 1 set = 0b111
    // Setting an already set bit doesn't change it
    assert_val_eq!(session.run("set_bit(1, 0)"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_clear_bit() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("clear_bit(1, 0)"), int(0)); // clear bit 0
    assert_val_eq!(session.run("clear_bit(2, 1)"), int(0)); // clear bit 1
    assert_val_eq!(session.run("clear_bit(7, 1)"), int(5)); // 0b111 with bit 1 cleared = 0b101
    assert_val_eq!(session.run("clear_bit(5, 2)"), int(1)); // 0b101 with bit 2 cleared = 0b001
    // Clearing an already cleared bit doesn't change it
    assert_val_eq!(session.run("clear_bit(0, 0)"), int(0));
    assert_val_eq!(session.run("clear_bit(2, 0)"), int(2));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_test_bit() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("test_bit(0, 0)"), bool(false));
    assert_val_eq!(session.run("test_bit(1, 0)"), bool(true));
    assert_val_eq!(session.run("test_bit(2, 0)"), bool(false));
    assert_val_eq!(session.run("test_bit(2, 1)"), bool(true));
    assert_val_eq!(session.run("test_bit(5, 0)"), bool(true)); // 0b101 bit 0 is set
    assert_val_eq!(session.run("test_bit(5, 1)"), bool(false)); // 0b101 bit 1 is not set
    assert_val_eq!(session.run("test_bit(5, 2)"), bool(true)); // 0b101 bit 2 is set
    assert_val_eq!(session.run("test_bit(7, 0)"), bool(true)); // 0b111
    assert_val_eq!(session.run("test_bit(7, 1)"), bool(true));
    assert_val_eq!(session.run("test_bit(7, 2)"), bool(true));
}

// ============================================================================
// Boolean Bit Operations
// ============================================================================

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_bit_and() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("bit_and(false, false)"), bool(false));
    assert_val_eq!(session.run("bit_and(false, true)"), bool(false));
    assert_val_eq!(session.run("bit_and(true, false)"), bool(false));
    assert_val_eq!(session.run("bit_and(true, true)"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_bit_or() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("bit_or(false, false)"), bool(false));
    assert_val_eq!(session.run("bit_or(false, true)"), bool(true));
    assert_val_eq!(session.run("bit_or(true, false)"), bool(true));
    assert_val_eq!(session.run("bit_or(true, true)"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_bit_xor() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("bit_xor(false, false)"), bool(false));
    assert_val_eq!(session.run("bit_xor(false, true)"), bool(true));
    assert_val_eq!(session.run("bit_xor(true, false)"), bool(true));
    assert_val_eq!(session.run("bit_xor(true, true)"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_bit_not() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("bit_not(false)"), bool(true));
    assert_val_eq!(session.run("bit_not(true)"), bool(false));
    // Double negation returns original
    assert_val_eq!(session.run("bit_not(bit_not(true))"), bool(true));
    assert_val_eq!(session.run("bit_not(bit_not(false))"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_shift_left() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("shift_left(false, 0)"), bool(false));
    assert_val_eq!(session.run("shift_left(false, 1)"), bool(false));
    assert_val_eq!(session.run("shift_left(true, 0)"), bool(true));
    assert_val_eq!(session.run("shift_left(true, 1)"), bool(false));
    assert_bool_shift_counts(&mut session, "shift_left");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_shift_right() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("shift_right(false, 0)"), bool(false));
    assert_val_eq!(session.run("shift_right(false, 1)"), bool(false));
    assert_val_eq!(session.run("shift_right(true, 0)"), bool(true));
    assert_val_eq!(session.run("shift_right(true, 1)"), bool(false));
    assert_bool_shift_counts(&mut session, "shift_right");
}

fn assert_bool_shift_counts(session: &mut TestSession, operation: &str) {
    for (count, expected_true) in [
        ("0", true),
        ("1", false),
        ("-1", false),
        ("bit(count_zeros(0) - 1)", false),
        ("bit_not(bit(count_zeros(0) - 1))", false),
    ] {
        for runtime in [false, true] {
            for (value, expected) in [(true, expected_true), (false, false)] {
                let operands = if runtime {
                    format!("let value = black_box({value}); let count = black_box({count});")
                } else {
                    format!("let value = {value}; let count = {count};")
                };
                assert_val_eq!(
                    session.run(&format!("{operands} {operation}(value, count)")),
                    bool(expected)
                );
            }
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_rotate_left() {
    let mut session = TestSession::new();
    // For bool, rotate_left returns the identity (see logic.rs implementation)
    assert_val_eq!(session.run("rotate_left(false, 0)"), bool(false));
    assert_val_eq!(session.run("rotate_left(false, 1)"), bool(false));
    assert_val_eq!(session.run("rotate_left(true, 0)"), bool(true));
    assert_val_eq!(session.run("rotate_left(true, 1)"), bool(true));
    assert_val_eq!(session.run("rotate_left(true, -1)"), bool(true));
    assert_val_eq!(session.run("rotate_left(false, -1)"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_rotate_right() {
    let mut session = TestSession::new();
    // For bool, rotate_right returns the identity (see logic.rs implementation)
    assert_val_eq!(session.run("rotate_right(false, 0)"), bool(false));
    assert_val_eq!(session.run("rotate_right(false, 1)"), bool(false));
    assert_val_eq!(session.run("rotate_right(true, 0)"), bool(true));
    assert_val_eq!(session.run("rotate_right(true, 1)"), bool(true));
    assert_val_eq!(session.run("rotate_right(true, -1)"), bool(true));
    assert_val_eq!(session.run("rotate_right(false, -1)"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_count_ones() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("count_ones(false)"), int(0));
    assert_val_eq!(session.run("count_ones(true)"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_count_zeros() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("count_zeros(false)"), int(1));
    assert_val_eq!(session.run("count_zeros(true)"), int(0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_bit() {
    let mut session = TestSession::new();
    // bit(0) returns true, any other position returns false
    assert_val_eq!(session.run("(bit(0): bool)"), bool(true));
    assert_val_eq!(session.run("(bit(1): bool)"), bool(false));
    assert_val_eq!(session.run("(bit(2): bool)"), bool(false));
    assert_val_eq!(session.run("(bit(-1): bool)"), bool(false));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_set_bit() {
    let mut session = TestSession::new();
    // set_bit at position 0 sets to true, other positions leave unchanged
    assert_val_eq!(session.run("set_bit(false, 0)"), bool(true));
    assert_val_eq!(session.run("set_bit(true, 0)"), bool(true));
    assert_val_eq!(session.run("set_bit(false, 1)"), bool(false));
    assert_val_eq!(session.run("set_bit(true, 1)"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_clear_bit() {
    let mut session = TestSession::new();
    // clear_bit at position 0 sets to false, other positions leave unchanged
    assert_val_eq!(session.run("clear_bit(false, 0)"), bool(false));
    assert_val_eq!(session.run("clear_bit(true, 0)"), bool(false));
    assert_val_eq!(session.run("clear_bit(false, 1)"), bool(false));
    assert_val_eq!(session.run("clear_bit(true, 1)"), bool(true));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_test_bit() {
    let mut session = TestSession::new();
    // test_bit at position 0 returns the value, other positions return false
    assert_val_eq!(session.run("test_bit(false, 0)"), bool(false));
    assert_val_eq!(session.run("test_bit(true, 0)"), bool(true));
    assert_val_eq!(session.run("test_bit(false, 1)"), bool(false));
    assert_val_eq!(session.run("test_bit(true, 1)"), bool(false));
    assert_val_eq!(session.run("test_bit(false, -1)"), bool(false));
    assert_val_eq!(session.run("test_bit(true, -1)"), bool(false));
}

// ============================================================================
// Combined Operations
// ============================================================================

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn int_combined_operations() {
    let mut session = TestSession::new();
    // Combining set_bit and test_bit
    assert_val_eq!(
        session.run("let x = set_bit(0, 3); test_bit(x, 3)"),
        bool(true)
    );
    assert_val_eq!(
        session.run("let x = set_bit(0, 3); test_bit(x, 2)"),
        bool(false)
    );

    // Combining clear_bit and test_bit
    assert_val_eq!(
        session.run("let x = clear_bit(15, 2); test_bit(x, 2)"),
        bool(false)
    );
    assert_val_eq!(session.run("let x = clear_bit(15, 2); x"), int(11)); // 0b1111 -> 0b1011

    // count_ones with bit operations
    assert_val_eq!(session.run("count_ones(bit_or(5, 3))"), int(3)); // 0b111 has 3 ones
    assert_val_eq!(session.run("count_ones(bit_and(5, 3))"), int(1)); // 0b001 has 1 one
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bool_combined_operations() {
    let mut session = TestSession::new();
    // Combining operations
    assert_val_eq!(
        session.run("bit_and(bit_or(true, false), true)"),
        bool(true)
    );
    assert_val_eq!(
        session.run("bit_xor(bit_and(true, true), false)"),
        bool(true)
    );
    assert_val_eq!(session.run("bit_not(bit_xor(true, true))"), bool(true));

    // count_ones with bit operations
    assert_val_eq!(session.run("count_ones(bit_or(false, false))"), int(0));
    assert_val_eq!(session.run("count_ones(bit_or(true, false))"), int(1));
}
