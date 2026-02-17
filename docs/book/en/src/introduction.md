# Introduction

Ferlium is a small, [statically-typed](https://en.wikipedia.org/wiki/Type_system#Static_type_checking) programming language designed for education and embedding. It aims to combine the expressiveness of Haskell with a syntax inspired by [Rust](https://www.rust-lang.org/) and other [C-style languages](https://en.wikipedia.org/wiki/List_of_C-family_programming_languages), while remaining approachable like [JavaScript](https://en.wikipedia.org/wiki/JavaScript) and [Python](https://www.python.org/). Ferlium is expression-based, uses [Hindley–Milner](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system) style type inference, and supports pattern matching and mutable value semantics.

This book introduces the Ferlium language and its features. It is intended for both new users who want to learn the language and experienced programmers who want to understand its design and capabilities.

This introduction provides a brief overview of Ferlium's syntax and core concepts; later chapters explore the language in more depth, covering the core language, structured data and abstraction, the type system, and effects and mutability.


## A first taste

```ferlium
fn sign(n) {
	if n < 0 {
		-1
	} else if n > 0 {
		1
	} else {
		0
	}
}

let x = 3;
sign(x)
```

Ferlium programs are [expressions](https://en.wikipedia.org/wiki/Expression_(computer_science)).
This means that constructs such as blocks, conditionals, and function bodies always produce a value.
The value of a block is the value of its last expression; when there is no meaningful result, the value is the [unit value](https://en.wikipedia.org/wiki/Unit_type), equivalent to the empty tuple `()`.
For this reason, functions in Ferlium always return a value.

## Comments

Ferlium supports C-style single-line and block comments:
```ferlium
// Single-line comment
/* Block comment */
```

## Values and basic literals

Ferlium has the following basic literal forms:

```ferlium
let i = 42;        // int
let f = 3.14;      // float
let b = true;      // bool
let s = "hello";   // string
let u = ();        // unit
```

Formatted strings use `f"..."` and can refer to [bindings](https://en.wikipedia.org/wiki/Name_binding) in scope:

```ferlium
let a = 1;
let b = true;
f"hello {a} world {b}"
```

## Bindings and mutability

Use `let` for immutable bindings and `let mut` for mutable bindings.
You can think of a binding as a named cell: `let` creates a read-only cell to a value, `let mut` a mutable cell to a value, that is, one that can be modified after creation:

```ferlium
let a = 1;
let mut b = 0;
b = b + 1;
b
```

## Blocks and sequencing

Blocks are delimited by `{}` and are composed of a sequence of statements, each ending with a semicolon, optionally followed by an expression.
A statement is either a binding or an expression whose value is discarded.
The value of a block is the value of its optional last expression:

```ferlium
{
	let x = 1;
	let y = 2;
	x + y
}
```

or `()` if the block ends with a statement:

```ferlium
{
	let x = 1;
	let y = 2;
}
```

## Functions

Define a function with `fn`.
Arguments are comma-separated.
A function body is a block, and its value is the return value.

```ferlium
fn add(a, b) {
	a + b
}

add(1, 2)
```

Functions have static types that are [inferred](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system).
Ferlium may automatically generalize functions when possible. For example, a function like `add` may be inferred as taking any numeric type, not just `int`.
The details of generics and constraints are explained later in this book.

If you want to limit the function to specific types, you can add type annotations to arguments and return types:

```ferlium
fn add(a: int, b: int) -> int {
	a + b
}
```


## How to read and use the examples

This book contains many small Ferlium code examples. They are written to illustrate specific concepts and are not all meant to be run as complete programs.

Some examples show standalone expressions, such as:

```ferlium
1 + 2 * 3
```

Others show script-style code with bindings and sequencing, such as:
```ferlium
let x = 10;
let y = 20;
x + y
```

Not all examples are runnable as-is. Some omit surrounding context for clarity, and some show multiple expressions without separators to emphasize their individual results. Runnable examples are explicitly marked when relevant.

You can run the examples in Ferlium's [playground](https://enlightware.github.io/ferlium/playground/) or in a local Ferlium REPL, as explained in the [README](https://github.com/enlightware/ferlium#getting-started). Running directly in this document is not supported at this time.

As you read, focus on what each example is meant to illustrate, rather than treating every code block as a complete program.

## What comes next

The next chapter walks you through running your first Ferlium code and seeing how the language executes.