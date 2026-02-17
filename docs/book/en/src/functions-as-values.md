# Functions as Values

In earlier chapters, you used named functions and relied on inference to keep code concise.
In this chapter, we treat functions as ordinary values: you can create them inline, pass them around, return them, and close over surrounding data.

## Anonymous functions

An [anonymous function](https://en.wikipedia.org/wiki/Anonymous_function) (lambda) is written with pipes around its parameters:

```ferlium
|x| x + 1
```

You can bind it to a name and call it like any other function value:

```ferlium
let inc = |x| x + 1;
inc(41)
```

Lambdas can have zero, one, or many parameters:

```ferlium
let one = || 1;
let id = |x| x;
let add = |x, y| x + y;

(one(), id(10), add(2, 3))
```

Like other expressions, lambda bodies can be single expressions or blocks.

## Functions are values

A function value can be stored anywhere a value can be stored: in bindings, tuples, arrays, and match arms.

```ferlium
let ops = [|x| x + 1, |x| x * x];
ops[0](ops[1](3))
```

```ferlium
let transform = match 0 {
    0 => |x| x * 2,
    _ => |x| x * x,
};

transform(3)
```

This is the key shift: functions are first-class values.
They are not special syntax that only works at declaration sites.

## Passing functions as arguments

You can pass a function value to another function:

```ferlium
fn apply_twice(f, x) {
    f(f(x))
}

apply_twice(|n| n + 1, 5)
```

This pattern is common when working with collections and iterators:

```ferlium
array_map([1, 2, 3], |x| x + 10)
```

The receiving function constrains what the passed function must accept and return.

## Returning functions from functions

A function can also produce and return another function:

```ferlium
fn make_adder(base) {
    |x| x + base
}

let add10 = make_adder(10);
add10(5)
```

This is useful when you want to configure behavior once and apply it later.

## Closures capture surrounding values

When a lambda refers to names from an outer scope, it forms a [closure](https://en.wikipedia.org/wiki/Closure_(computer_programming)).
In Ferlium, captures are by value.
This means the closure receives its own copy of the captured values at the time it is created.

```ferlium
let a = 3.3;
let f = || a;
f()
```

Here `f` stores its own captured copy of `a`.

### Capture is independent from later outer changes

Changing the outer variable after creating the closure does not change the captured value:

```ferlium
let mut a = 1;
let f = || a;
a = 2;
f()
```

This evaluates to `1`.

### Mutating inside a closure does not mutate the outer binding

Because capture is by value, mutating a captured variable inside the closure updates the closure’s private copy, not the outer binding:

```ferlium
let mut a = 1;
let f = || { a = 2; a };
f();
a
```

This evaluates to `1` for the outer `a`.

The same idea applies to mutable structures such as arrays: the closure captures its own value, not a shared outer cell.

## Type inference for lambdas

Lambda parameters and results are inferred from how the lambda is used.

```ferlium
let add1 = |x| x + 1;
add1(41)
```

Here, the type of `add1` is inferred to be a function that takes an `int` and returns an `int`, because of how it is called.
Its type would be different if it were called with a `float`:

```ferlium
let add1 = |x| x + 1;
add1(3.14)
```

### Lambdas bound with `let` are not generalized

A `let`-bound lambda is inferred once and then retains that single inferred type within its scope.

```ferlium,compile_fail
let id = |x| x;
id(1);
id(true)
```

This fails because `id` is not re-generalized per call.

If you need behavior that works uniformly across many types, use a named function definition, as discussed in [Functions and Type Inference](functions-and-type-inference.html).

## Summary

Anonymous functions let you write behavior inline. Because functions are values, you can store, pass, and return them naturally. Closures make lambdas practical by capturing surrounding values, and in Ferlium those captures are by value, which keeps mutation behavior predictable. Inference keeps lambda syntax light, while `let`-bound lambdas stay at a single inferred type per scope.

## What comes next

The next chapter explores type abstraction, showing how Ferlium infers polymorphic types, tracks trait constraints, and applies sensible defaults.