# Bindings, Scope, and Mutability

Ferlium lets you name values, limit where those names are visible, and decide which names refer to values that can be modified.
This chapter explains `let` and `let mut`, how scopes work, and the intuitive model behind Ferlium’s mutable value semantics.

## `let` bindings

A `let` [binding](https://en.wikipedia.org/wiki/Name_binding) introduces a new name for a value:

```ferlium
let x = 1;
let y = x + 2;
y
```

Bindings are immutable by default.
That means you can read `x`, but you cannot modify the value of `x` later.

## `let mut` bindings

Use `let mut` when you want a variable that can be modified after it is defined:

```ferlium
let mut counter = 0;
counter = counter + 1;
counter
```

Assignment itself produces the unit value `()`:

```ferlium
let mut a = 1;
a = 2;   // value is ()
a
```

## Scope

Every block introduces a new [scope](https://en.wikipedia.org/wiki/Scope_(computer_science)).
A name is visible from its definition to the end of the block where it is defined.

```ferlium
let x = 1;
{
    let y = x + 1;
    y
}
```

Here, `y` exists only inside the block. The value of the block is the value of its last expression.

## Shadowing

You can reuse a name in an inner scope.
The new binding temporarily hides the outer one.
This is called shadowing.

```ferlium
let x = 1;
{
    let x = 2;
    x
}
```

The inner `x` does not change the outer `x`.
When the block ends, the outer `x` is visible again.

You can also shadow a name in the same scope:

```ferlium
let x = 1;
let x = x + 1;
x
```

In this case, the first `x` is not accessible after the second `x` is defined.
The type of the new `x` can be different from the old one.
For example, you can shadow an integer with a string:

```ferlium
let x = 1;
let x = f"number {x}";
x
```

Shadowing can be done even though the binding is not mutable, because the new binding is a different name that happens to shadow the old one.

## Function-local variables

Function parameters behave like local bindings and are scoped to the function body. Whether a function can modify a value depends on how that value is passed, which will be discussed later. Function parameters can also be shadowed:

```ferlium
fn add_one(n) {
    let n = n + 1;
    n
}

add_one(10)
```

This uses a new local `n` that shadows the parameter inside the function body.

## Mutable value semantics

Think of a binding as a named cell that holds a value. With `let`, the cell is read-only. With `let mut`, the cell is writable. Reassigning a mutable binding replaces the value stored in that cell.

In Ferlium, values are not implicitly shared between bindings. Reassigning a mutable binding replaces the value stored in that binding, and updates to compound values (such as tuples or arrays) affect only that binding unless the value was explicitly passed in a mutable way. This model avoids hidden aliasing: two separate bindings do not unexpectedly refer to the same mutable storage.

Compound values can be updated through a mutable binding:

```ferlium
let mut p = (1, 2);
p.0 = 3;

let mut xs = [1, 2];
xs[0] = 3;

(p, xs)
```

If the binding is not mutable, these updates are rejected at compile time.

## What comes next

The next chapter introduces functions and type inference, showing how Ferlium automatically determines types for your code.