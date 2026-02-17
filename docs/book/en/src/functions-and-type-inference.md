# Functions and Type Inference

Ferlium infers function types from their definitions and uses a whole-module view to keep types consistent. This chapter explains how inference works, why functions get the most general type possible, and how constraints arise from the operations inside function bodies.

## Function types are inferred from bodies

When you define a function, Ferlium infers its input and output types by analyzing the body. You do not need to write a type signature to get a well-typed function.

```ferlium
fn abs1(x) {
    if x < 0 {
        -x
    } else {
        x
    }
}

abs1(-3)
```

Here, the comparison and negation determine that `x` must be a number, and the result has the same type as `x`.

## Automatic generalization

At the module level, Ferlium generalizes function types to be as general as possible. Intuitively, a function that does not depend on a specific concrete type becomes usable with many types.

```ferlium
fn id(x) { x }

(id(1), id(true), id("hi"))
```

`id` is inferred once, and the compiler makes it as general as it can be so that all valid uses can share the same definition.

## Constraints from operations

Operations inside a function body create requirements on the types involved. For example, `+` requires a numeric type, and comparisons like `<` require an ordered type. Ferlium records these requirements as constraints during inference.

```ferlium
fn inc(x) { x + 1 }

(inc(41), inc(41.5))
```

The function `inc` is inferred with the constraint that its argument supports addition with a numeric literal. This is why it works for numeric types but not for `bool` or `string`.

## Whole-module inference

Ferlium infers types for all functions in a module together. Functions can refer to each other regardless of their order, including mutual recursion.

```ferlium
fn is_even(n) {
    if n == 0 { true } else { is_odd(n - 1) }
}

fn is_odd(n) {
    if n == 0 { false } else { is_even(n - 1) }
}

is_even(10)
```

The compiler resolves `is_even` and `is_odd` as a pair, so each function influences the inferred type of the other.

## How annotations interact with inference

Type annotations restrict the inferred type and are checked for consistency.

```ferlium
fn add_one(x: int) -> int { x + 1 }

add_one(10)
```

Annotations are most useful when you want to fix a type to a specific one, or when you want to document intent.
In all cases, the inferred type must agree with the annotation.

## Recursive functions

A function in Ferlium can call itself.
This is called [recursion](https://en.wikipedia.org/wiki/Recursion_(computer_science)).
Recursive functions are commonly used when a problem can be broken into smaller instances of the same problem.

For example, factorial can be defined recursively:

```ferlium
fn fact(n) {
    if n <= 1 {
        1
    } else {
        n * fact(n - 1)
    }
}
```

Here, `fact` calls itself with a smaller argument until it reaches the base case `n <= 1`.

Recursion works naturally with type inference. The compiler infers one type for the function and checks that all recursive calls are consistent with that type.

Ferlium cannot enforce at compile time that recursive functions terminate.
If a function calls itself indefinitely, execution will fail at runtime.
It is the programmer's responsibility to ensure that recursion progresses toward a base case.

## What comes next

In some cases, inference leaves certain types ambiguous.
Later chapters explain how Ferlium resolves such ambiguities automatically, and explain explicit generics and the constraint system in more depth.
The next chapter covers control flow.