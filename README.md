# Painturscript

Painturscript is a small functional scripting language with generics and static typing (à la Standard ML).
It aims at being lightweight and interfacing nicely with Rust.
In particular, it tries hard not to duplicate existing Rust types and functions when not strictly necessary (e.g., it doesn't have a boolean type distinct of Rust's `bool`).

## Key features

### For users

* Functional statically-typed scripting language
* Parametric polymorphism (generics)
* Ad hoc polymorphism through type classes (traits)
* Row polymorphism (subtyping for records and tuples)
* Algebraic data types (including tagged unions)
* Pattern matching
* Type inference (Hindley-Milner style)
* Compile-time code validation (somehow similar to Rust's procedural macro system)

### For developers and integrators

* Intermediate representation (IR) as close as possible to a textbook functional language (for readability and correctness)
* But access necessary extensions for performance reasons (e.g., special case for functions not as values)
* Avoid native code in the IR when not necessary (i.e., no int, bool, etc. explicit there)
* Smooth binding with native code (to bring int, bool, etc. on demand)
* Rich integration possibilities with the native platform (e.g. for platform-managed values)

## Inspirations

* ML: basic functional concepts (especially [this course](https://pauillac.inria.fr/~remy/mpri/))
* Rust: syntax and type system

## Why the name painturscript?

Why this name? Several reasons:

1. `painturscript` is not used on the web so far,
2. It sounds like "paint your script", which invites to arty action.
3. And, by design, it "covers the Rust".
