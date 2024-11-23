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
* Mutable value semantics
* Type inference (Hindley-Milner style)
* Compile-time code validation (somehow similar to Rust's procedural macro system)

### For developers and integrators

* Intermediate representation (IR) as close as possible to a textbook functional language (for readability and correctness)
* But be pragmatic about it: e.g. provides a mutable value semantics
* Avoid native code in the IR when not necessary (i.e., no int, bool, etc. explicit there)
* Smooth binding with native code (to bring int, bool, etc. on demand)
* Rich integration possibilities with the native platform (e.g. for platform-managed values)

## Inspirations

* ML: basic functional concepts (especially [this course](https://pauillac.inria.fr/~remy/mpri/) and [this one](https://cs3110.github.io/textbook/chapters/interp/inference.html))
* Rust: syntax and type system
* HM(X) approach to type inference ([this paper](https://www.researchgate.net/profile/Martin-Sulzmann/publication/220346751_Type_Inference_with_Constrained_Types/links/5ab00c0b0f7e9b4897c1d25b/Type-Inference-with-Constrained-Types.pdf))
* Mutable Value Semantics (especially [this paper](https://www.jot.fm/issues/issue_2022_02/article2.pdf))
* This [series of blog posts](https://thunderseethe.dev/posts/type-inference/)

## Why the name painturscript?

Why this name? Several reasons:

1. `painturscript` is not used on the web so far,
2. It sounds like "paint your script", which invites to arty action.
3. And, by design, it "covers the Rust".

## Limitations

Currently the compiler can only be used from a single thread to avoid deadlocks when accessing the internized type universe. Currently the compiler will panic if the corresponding lock is held when being accessed in write.