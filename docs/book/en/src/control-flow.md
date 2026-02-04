# Control Flow and Pattern Matching

Control flow in Ferlium is expression-based: `if` and `match` both produce values. This chapter explains how their types are determined and how to use them safely and clearly.

## `if` is an expression

An `if` expression always produces a value. When both branches are present, the result is the value of the selected branch.

```ferlium
let x = if 1 < 2 { 10 } else { 20 };
x
```

The condition must be a `bool`. Both branches must produce compatible types, because the whole `if` has a single type.

```ferlium,ignore
if true { 1 } else { 2 }        // ok: int
if true { "yes" } else { "no" } // ok: string
```

### Branch types must agree

If the branches have different types, the program does not type check:

```ferlium,compile_fail
if true { 1 } else { "no" }   // type error
```

### `if` without `else`

An `if` without `else` is allowed when it is used for its effect. In that case, its result type is `()`.

```ferlium
let mut a = 0;
if true { a = 1 };
a
```

Trying to use a value-producing branch without an `else` is a type error:

```ferlium,compile_fail
// type error: missing else for a non-unit branch
fn f() { if true { 1 } }
```

## `match` is an expression

A `match` expression selects one of several branches based on a value. Like `if`, it produces a value.

In this chapter, we only use literal patterns and the wildcard `_`.

```ferlium
let a = 0;
match a {
    0 => 1,
    1 => 2,
    _ => 3,
}
```

An entry `LITERAL => EXPRESSION` is called an **arm**.

### All arms must have compatible types

Every arm in a `match` must produce a value of the same type, because the whole `match` has a single type:

```ferlium
match 0 {
    0 => 1,
    _ => 2,
}
```

This is a type error:

```ferlium,compile_fail
match 0 {
    0 => 1,
    _ => "no",
}
```

### Exhaustiveness with `_`

When matching on literals, use `_` as the default case unless you explicitly cover all possible values. For example, matching on `bool` can list both cases:

```ferlium
match true {
    true => 1,
    false => 0,
}
```

## What comes next

Later chapters expand pattern matching to structured data and more powerful patterns. For now, you can use literals and `_` to write clear, type-safe control flow.
