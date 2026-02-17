# Values and Types

Every Ferlium expression produces a value. Values are the runtime results of evaluating expressions, and the language is built around composing these values to form larger computations. This chapter explains what values are, the basic built-in types, and how Ferlium assigns and checks types.

## What is a value?

A value is the result of evaluating an expression. Literals like `1` and `"hello"` are values, and so are the results of computations like `1 + 2` or `abs(-3)`. Because Ferlium is expression-based, constructs such as blocks and conditionals also produce values.

Bindings name values:

```ferlium
let a = 1;
let b = a + 2;
b
```

Here, `b` evaluates to the value `3`.

## Static typing and inference

Ferlium is [statically typed](https://en.wikipedia.org/wiki/Type_system#Static_type_checking). The compiler determines a type for every expression and checks that types are used consistently. Most of the time you don’t need to write types explicitly because Ferlium infers them from how values are used.

You can still add type annotations to guide or clarify inference using `:`:

```ferlium
let n: int = 42;
let x = (1: int);
```

Type annotations can also be used in function signatures to specify parameter types:

```ferlium
fn add_int(x: int, y: int) {
    x + y
}
```

or return types, using `->`:

```ferlium
fn add_int(x, y) -> int {
    x + y
}
```

If an expression cannot be assigned a consistent type, compilation fails with a type error.
For example, this function has inconsistent types between its parameters and its return value:

```ferlium,compile_fail
fn bad(x: int) -> float {
    x
}
```

as `int` and `float` are different types.

## Basic built-in types

These are the core, always-available types in Ferlium:

- [`unit`](https://en.wikipedia.org/wiki/Unit_type), written `()`, a type with a single value representing “no meaningful result”
- [`bool`](https://en.wikipedia.org/wiki/Boolean_data_type) with values `true` and `false`
- [`int`](https://en.wikipedia.org/wiki/Integer_(computer_science)) representing whole numbers
- [`float`](https://en.wikipedia.org/wiki/Floating-point_arithmetic) representing floating-point numbers
- [`string`](https://en.wikipedia.org/wiki/String_(computer_science)) representing text

Literals for these types look like this:

```ferlium
let u = ();        // unit
let b = true;      // bool
let i = 42;        // int
let f = 3.14;      // float
let s = "hello";   // string
```

Formatted strings use `f"..."` and evaluate to a `string`:

```ferlium
let a = 1;
let ok = true;
f"a = {a}, ok = {ok}"
```

## Composite values

Ferlium also includes a few composite value forms that you can use immediately.

### Tuples

A tuple groups multiple values together. A single-element tuple requires a trailing comma.

```ferlium
let p = (1, true);
let single = (1,);
```

The corresponding types are written as `(int, bool)` and `(int,)`.

### Arrays

An array is written with brackets. All elements must have the same type.

```ferlium
let xs = [1, 2, 3];
let empty: [int] = [];
```

The type `[int]` means “array of integers”.
Arrays can be composed of any type, including other arrays:

```ferlium
let matrix = [[1, 2], [3, 4]];
```

The type of `matrix` is `[[int]]`, an array of arrays of integers.

### Records

Records are field-based values with named entries.

```ferlium
let user = { name: "Ada", age: 36 };
```

The type of `user` is written `{ name: string, age: int }`.
Field order does not matter.
Records can contain any types, including other records, tuples and arrays:

```ferlium
let cfg = { host: "localhost", port: 8080, paths: ["/", "/api"] };
```

The type of `cfg` is `{ host: string, port: int, paths: [string] }`.

### Variants

A variant is a value composed of a name with optional payload data.
Each variant belongs to a sum type, which defines the possible alternatives.

```ferlium
let a = None;
let b = Some(1);
```

The corresponding type is written `None | Some(int)`, a sum type with two alternatives: `None` and `Some`.

## Unit and “no meaningful result”

The [unit](https://en.wikipedia.org/wiki/Unit_type) value `()` represents the absence of a meaningful result.
It is equivalent to the empty tuple, and is the only value of type `unit`.
It is used when you do something only for its effect (like assigning to a mutable variable) or when a block ends with a semicolon.

```ferlium
let mut v = 0;
let x = {
    let y = 1;
    v = y;
};

(x, v)
```

The block returns `()` because the last expression ends with `;`. The tuple `(x, v)` evaluates to `((), 1)`.

## How expressions are typed

Every expression has a type, and the compiler checks that they fit together:

- Literals have fixed types (`1.1` is `float`, `"hi"` is `string`).
- An exception is integer literals, which can be used as any number type depending on context.
- Operators require compatible operand types (for example, `+` on numbers of the same type).
- In `if` expressions, both branches must have the same type.
- In arrays, all elements must share a single element type.
- In tuples and records, each position or field has its own type.
- In function calls, argument types must match the function’s parameter types.

Type annotations can help when the compiler needs guidance:

```ferlium
let values: [int] = [];
let total = ((1 + 2): float);
```

## Type errors and what they mean

A type error means the compiler could not make the types consistent. Common causes include:

- Using an operator with incompatible types.
- Combining branches that return different types.
- Passing a value of the wrong type to a function.

For example:

```ferlium,compile_fail
1 + true                     // type error: int + bool
if true { 1 } else { "no" }  // type error: branches differ
```

Type errors are reported at compile time, before any code runs. Fixing them usually means making the types line up—by changing a value, adding an annotation, or restructuring the expression.

## What comes next

The next chapter explores bindings, scope, and mutability in more detail, including how to create and work with mutable state.
