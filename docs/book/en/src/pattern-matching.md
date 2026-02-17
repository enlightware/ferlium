# Pattern Matching

Pattern matching lets you branch on the shape or value of data.
In Ferlium, `match` is an expression and is statically type-checked.

## Match is an expression

A `match` expression selects one arm and returns that arm’s value.

```ferlium
let score = match true {
    true => 100,
    _ => 0,
};

score
```

Like `if`, a `match` expression has a single result type.

## Basic patterns

### Literal patterns

Literal patterns compare the matched value against a literal.

```ferlium
match 0 {
    -1 => "negative one",
    0 => "zero",
    _ => "other",
}
```

Ferlium supports the following scalar literal patterns: `()`, `bool`, `int`, and `string`.

### Wildcard `_`

`_` is the default pattern of a `match`.
It matches any value not matched by earlier arms.

```ferlium
match 5 {
    0 => "zero",
    1 => "one",
    _ => "many",
}
```

## Matching structured data

### Product types

Tuple values can be matched using tuple patterns:

```ferlium
match (true, false) {
    (true, true) => 1,
    (true, false) => 2,
    (false, true) => 3,
    (false, false) => 4,
}
```

Nested tuple patterns are supported:

```ferlium
match (true, (false, true)) {
    (true, (false, true)) => 1,
    _ => 0,
}
```

Matching record values is not yet supported.

### Sum types

Ferlium supports matching on sum types using constructor patterns.
These patterns match on specific alternatives and bind their payload to variables:

```ferlium
match Some(10) {
    Some(x) => x + 1,
    None => 0,
}
```

You can match all three forms of alternatives: nullary (unit-like), tuple-style, and record-style:

```ferlium
enum Action {
    Quit,
    Jump(float),
    Move { x: float, y: float },
}

fn f(a) {
    match a {
        Quit => 0.0,
        Jump(h) => h,
        Move { y, x } => x - y,
    }
}

f(Action::Move { x: 30.0, y: 40.0 })
```

In record-style patterns, `..` can be used to ignore remaining fields.

```ferlium
match (Some { x: 1, y: 2, z: 3 }) {
    Some { x, .. } => x + 10,
}
```

`..` must appear as the last entry in the record pattern.
If it appears earlier, compilation fails.

## Typing rules

### All arms must have compatible result types

A `match` expression has a single result type, so all arms must produce compatible values.

```ferlium
let n = match false {
    true => 1,
    _ => 2,
};

n
```

If arm results are incompatible, type checking fails.

### Binding types come from the matched value

For sum types, bindings introduced by a pattern take their types from the matched constructor’s payload.

```ferlium
let v: None | Some(int) = Some(1);

match v {
    Some(x) => x + 1,
    None => 0,
}
```

Here `x` is inferred from `Some`’s payload type.

A mismatch between the matched value and pattern constructors is rejected:

```ferlium,compile_fail
let v: None | Some(int) = Some(0);

match v {
    None => 0,
}
```

This fails because `v` has type `None | Some(int)`, but the match only constrains it to `None`.

## Exhaustiveness and defaults

### Literal matches

Without `_`, literal matching is considered exhaustive only when Ferlium can enumerate all possible values of the matched type.
In practice, this works for finite enumerable domains (for example `bool`, and tuples built from enumerable element types).

```ferlium
match true {
    true => 1,
    false => 0,
}
```

For non-enumerable domains (for example `int`), omitting `_` is rejected.

```ferlium,compile_fail
let a = 0;
match a {
    0 => 1,
}
```

### Sum type matches

For constructor patterns, omitting `_` means that the listed alternatives must cover the matched sum type completely.
This code is correct:
```ferlium
let v: None | Some(int) = Some(0);

match v {
    Some(x) => x,
    None => -1
}
```

But an incomplete set is rejected:

```ferlium,compile_fail
let v: None | Some(int) = Some(0);

match v {
    Some(x) => x,
}
```

Use all alternatives (or a default arm `_`) to cover the full sum type.

## Current limitations

- A match arm cannot consist solely of a variable pattern. Use a literal, a constructor pattern, or `_` as the default arm.
- Destructuring plain tuples or records into variable bindings (e.g. `(x, y)`) is not yet supported; tuple patterns currently only work with literal and wildcard sub-patterns.
- `..` is not supported in tuple-style constructor patterns.
- In record-style constructor patterns, `..` is allowed only at the end.
- Pattern guards (extra `if` conditions on patterns) are not available.

## What comes next

The next chapter treats functions as first-class values, showing how to pass them as arguments, return them from functions, and create closures.
