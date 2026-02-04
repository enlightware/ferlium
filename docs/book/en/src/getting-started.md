# Getting Started

In this chapter you will run Ferlium code for the first time, evaluate a few expressions, and see how the different execution methods report results and errors.

## Run Ferlium

You can interact with Ferlium in three common ways:

- **Online playground**: visit the [Ferlium playground](https://enlightware.github.io/ferlium/playground/) and type code in the editor; results appear on the bottom.
- **REPL**: start the interactive prompt with `cargo run --example ferlium`, then type expressions and see their results.
- **Local execution**: put code in a file and run it locally with `cat FILENAME | cargo run --example ferlium` (Unix shell).

This chapter focuses on what to type once you are able to run Ferlium code using one of these methods.

## Your first expression

Enter a simple expression and observe its value.

```ferlium
1 + 2
```

Result: `3`

## A small script

A multi-line script can build a value step by step. The last expression is the result of the script.

```ferlium
let mut total = 0;
total = total + 1;
total = total + 2;
total
```

Result: `3`

## A simple function

Define a function and call it.

```ferlium
fn double(x) { x * 2 }

double(21)
```

Result: `42`

You can use the same function, and pass a floating-point number.

```ferlium
# fn double(x) { x * 2 }
double(1.5)
```

Result: `3.0`

## Seeing results

Ferlium always produces a value. What you see depends on how you run the code.

In the playground and the REPL, the value of the last expression is shown immediately.
When running a local script, the value of the last expression in the file is the result produced by the script.

When reading examples in this book, focus on the value of the final expression.

## A first error

If the types do not line up, Ferlium reports a compile-time error and points to the relevant spans. For example:

```ferlium,compile_fail
let x: int = true;
x
```

You will see a type-mismatch error stating that the `true` value has type `bool`, which does not match the `int` annotation, along with location information for both parts of the code.

## What comes next

Continue with the next chapter on the core language to build on these basics.
