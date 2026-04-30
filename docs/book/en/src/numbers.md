# Numbers

Ferlium has two numeric types: `int` for whole numbers and `float` for floating-point numbers. This chapter covers the literal forms they accept, how they convert, and the small differences that affect arithmetic.

## The two numeric types

`int` is a signed integer using the machine word width (typically 64 bits).
`float` is an [IEEE 754](https://en.wikipedia.org/wiki/IEEE_754) double-precision number that excludes `NaN`, so equality and ordering on `float` always behave consistently.

```ferlium
let i: int = 42;
let f: float = 3.14;
(i, f)
```

## Integer literals

Integer literals are written in three bases. All of them produce values of type `int`:

```ferlium
(42, 0b1010, 0xff)
```

- decimal: `42`
- binary: `0b1010` (digits `0` and `1`)
- hexadecimal: `0xff` (digits `0`–`9`, `a`–`f`, `A`–`F`; case-insensitive)

Negative literals use a leading `-`, which works with any base:

```ferlium
(-7, -0b101, -0xff)
```

Binary and hexadecimal forms are most useful for bit patterns, masks, and packed values; the next chapter on bitwise operations builds on them.

## Float literals

Float literals contain a decimal point:

```ferlium
(0.5, 3.14, -2.0)
```

There is no scientific-notation literal yet; build large or small floats with arithmetic if you need them.

## Mixing `int` and `float`

Integer and float values do not silently mix.
However, an integer *literal* is unconstrained until context fixes its type, so it adapts to the surrounding expression:

```ferlium
1 + 2.0
```

Here `1` is treated as `float` because the other operand is `float`, so the result is a `float`.

When a numeric expression has no context to constrain it, Ferlium defaults it to `int`:

```ferlium
let x = 1 + 2;
x
```

`x` has type `int`.

## Converting between `int` and `float`

Use `as` to convert explicitly:

```ferlium
let i = 5;
let f = i as float;
let j = 5.7 as int;
(f, j)
```

Float-to-int truncates toward zero, and both directions saturate at the target type's bounds rather than wrapping or producing `NaN`.

## Division and integer arithmetic

The `/` operator returns a `float`, even on integer operands:

```ferlium
10 / 3
```

This evaluates to `3.333…: float` because `/` only has a `float` implementation, and the integer literals default to `float` to satisfy it.

For integer division, use the dedicated functions:

- `idiv(left, right)` truncates toward zero
- `idiv_euclid(left, right)` rounds toward negative infinity
- `rem(left, right)` returns the remainder of `idiv`
- `mod(left, right)` returns the Euclidean remainder

```ferlium
(idiv(10, 3), rem(10, 3), mod(-7, 3))
```

Both `/` on `float` and the integer division functions are fallible: dividing by zero produces a runtime error rather than `inf` or `NaN`. The chapter on effects explains how Ferlium tracks fallibility.

## What comes next

The next chapter covers bitwise operations on integers and booleans through the `Bits` trait, where binary and hexadecimal literals are most at home.
