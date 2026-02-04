# Arrays, Ranges, and Iteration

Ferlium provides compact tools for working with sequences of values: arrays, ranges, and `for` loops. This chapter introduces how to create and read arrays, describe numeric sequences with ranges, and iterate over both forms in an expression-oriented style.

## Arrays

Arrays store ordered values of a single element type.

### Array literals

Array literals use square brackets:

```ferlium
let a = [1, 2, 3];
let b = [true, false, true];
let c = ["a", "b"];
```

A trailing comma is allowed:

```ferlium
let xs = [1, 2, 3,];
```

`[]` is valid syntax, but by itself its element type is unknown, so it needs context:

```ferlium
let empty: [int] = [];
```

### Indexing

Use `array[index]` to access elements:

```ferlium
let xs = [10, 20, 30];
let first = xs[0];
let second = xs[1];
```

Negative indices count from the end:

```ferlium
let xs = [10, 20, 30];
let last = xs[-1];
let before_last = xs[-2];
```

Indexing out of bounds is a runtime error.

### Arrays are values with one element type

Arrays are regular values: you can bind them, pass them around, and return them from expressions.

```ferlium
let xs = [1, 2, 3];
let ys = xs;
ys[0]
```

All elements must have the same type.
Mixing multiple element types is a type error:

```ferlium,compile_fail
[1, true]   // type error
```

### Element type inference

Ferlium infers the element type from array contents:

```ferlium
let ints = [1, 2, 3];      // inferred as [int]
let floats = [1.0, 2.5];   // inferred as [float]
```

For an empty array, add context with an annotation:

```ferlium
let mut out: [int] = [];
```

## Ranges

Ranges are a compact way to describe integer sequences.

### Exclusive and inclusive ranges

Use `start..end` for an exclusive upper bound:

```ferlium
let r = 1..4;   // 1, 2, 3
```

Use `start..=end` for an inclusive upper bound:

```ferlium
let r = 1..=4;  // 1, 2, 3, 4
```

Ranges also work in downward direction:

```ferlium
let r = 5..2;   // 5, 4, 3
let r = 5..=2;  // 5, 4, 3, 2
```

## Iteration with `for`

`for` loops iterate over a sequence and execute a body for each element.

### Iterating over ranges and arrays

Iteration works the same way for ranges and arrays:

```ferlium
for i in 0..3 { /* ... */ };
for x in [10, 20, 30] { /* ... */ };
```

### Accumulating with `let mut`

A common pattern is to keep mutable state outside the loop and update it inside:

```ferlium
let mut sum = 0;
for i in 1..=4 {
    sum = sum + i;
};
sum
```

Collecting values works the same way:

```ferlium
let mut out: [int] = [];
for i in 2..5 {
    array_append(out, i);
};
out
```

### Loop variable scope and expression result

The loop variable is local to the loop body. The `for` expression itself evaluates to `()`.

```ferlium
let mut count = 0;
for n in [1, 2, 3] {
    count = count + 1;
};
count
```

## What comes next

The next chapters expand structured data beyond arrays and introduce richer pattern matching for structured values.
