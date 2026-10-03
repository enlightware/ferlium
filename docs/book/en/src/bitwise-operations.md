# Bitwise Operations

Ferlium provides bitwise operations through the `Bits` trait. They are useful for low-level encoding, flag sets, and packed representations. The standard library implements `Bits` for `int` and `bool`, so the same function names work on both.

## Logical operations

`bit_and`, `bit_or`, `bit_xor`, and `bit_not` perform the usual boolean operations bit by bit:

```ferlium
bit_and(0b1101, 0b1011)
```

```ferlium
bit_or(0b1100, 0b0011)
```

```ferlium
bit_xor(0b1010, 0b1100)
```

```ferlium
bit_not(0)
```

`bit_not(0)` evaluates to `-1` because `int` is a signed two's-complement integer.

On `bool`, these collapse to the matching logical operators:

```ferlium
(bit_and(true, false), bit_or(true, false), bit_xor(true, true), bit_not(true))
```

## Shifts and rotations

On `int`, `shift_left` and `shift_right` move bits along the word, discarding bits that leave it.
Left shifts introduce zeros; right shifts repeat the sign bit, preserving the sign:

```ferlium
shift_left(1, 4)
```

```ferlium
shift_right(0b10100, 2)
```

For example, `shift_right(-8, 1)` returns `-4`.
Negative counts reverse direction: `shift_left(8, -1)` returns `4`, and `shift_right(8, -1)` returns `16`.

Shift counts do not wrap.
When the count's magnitude is at least the integer width, a left shift returns `0`, and a right shift returns `0` for nonnegative values or `-1` for negative values.

`rotate_left` and `rotate_right` move bits without losing them: bits that fall off one end re-enter at the other.

```ferlium
rotate_left(1, 3)
```

Negative rotation counts also reverse direction.
Rotation counts wrap modulo the integer width, so a rotation by the width returns the original value.

```ferlium
rotate_left(5, -1) == rotate_right(5, 1)
```

This returns `true`.

## Counting bits

`count_ones` and `count_zeros` return the number of set and unset bits:

```ferlium
count_ones(0b10110)
```

```ferlium
count_ones(true)
```

For `int`, `count_zeros` uses the full machine width (typically 64 bits), so `count_zeros(0)` returns the integer width. For `bool`, the width is 1.

## Single-bit helpers

`bit(position)` constructs a value with only the bit at `position` set. Because the result type cannot be inferred from arguments alone, you usually need a type annotation:

```ferlium
(bit(3): int)
```

`set_bit`, `clear_bit`, and `test_bit` operate on a single bit of an existing value:

```ferlium
set_bit(0b1000, 1)
```

```ferlium
clear_bit(0b1111, 2)
```

```ferlium
test_bit(0b1010, 1)
```

These compose naturally:

```ferlium
let flags = set_bit(set_bit(0, 0), 3);
(test_bit(flags, 0), test_bit(flags, 1), test_bit(flags, 3))
```

## Notes on `bool`

For bit operations, `bool` behaves like a single unsigned bit:

- `shift_left` and `shift_right` preserve the value for a zero count; any nonzero count returns `false`.
- `rotate_left` and `rotate_right` are the identity, since there is nowhere for the bit to move.
- `bit(0)` is `true`; `bit(n)` for any other `n` is `false`.
- `set_bit`, `clear_bit`, and `test_bit` only affect position `0`; other positions leave the value unchanged or return `false`.

This lets generic code over `Bits` work uniformly on both types without special casing.

## What comes next

The next chapter shows how Ferlium values can be converted to JSON and plain text, through (de)serialization.
