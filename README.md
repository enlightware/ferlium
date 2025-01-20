# Scriptli

Scriptli is a small functional scripting language with generics and static typing (à la Standard ML).
It aims at bringing the convenience of writing of Python, the safety of Rust, and the expressiveness of Haskell.

Scriptli aims at being lightweight and interfacing nicely with Rust.
In particular, it tries hard not to duplicate existing Rust types and functions when not strictly necessary (e.g., it doesn't have a boolean type distinct of Rust's `bool`).

## Key features

### For users

* Functional statically-typed scripting language
* Type inference (Hindley-Milner style, HM(X) flavor)
* Parametric polymorphism (generics)
* Ad hoc polymorphism through type classes (traits)
* Row polymorphism (subtyping for records and tuples)
* Algebraic data types (including tagged unions)
* Pattern matching
* Mutable value semantics (a simplified version of Rust's ownership system)
* Modules

### For developers and integrators

* A pragmatic language: e.g. provides a mutable value semantics
* Avoid native code in the IR when not necessary (i.e., no int, bool, etc. explicit there)
* Smooth binding with native code (to bring int, bool, etc. on demand)
* Rich integration possibilities with the native platform (e.g. for platform-managed values)

### Scope and non-scope

The [roadmap](doc/roadmap.md) lists the planned features.

The following features are out of scope:
* Dynamic dispatch

## Inspirations

* ML: basic functional concepts (especially [this course](https://pauillac.inria.fr/~remy/mpri/) and [this one](https://cs3110.github.io/textbook/chapters/interp/inference.html))
* Rust: syntax
* Haskel: type system
* HM(X) approach to type inference ([this paper](https://www.researchgate.net/profile/Martin-Sulzmann/publication/220346751_Type_Inference_with_Constrained_Types/links/5ab00c0b0f7e9b4897c1d25b/Type-Inference-with-Constrained-Types.pdf))
* Mutable Value Semantics (especially [this paper](https://www.jot.fm/issues/issue_2022_02/article2.pdf))
* This [series of blog posts](https://thunderseethe.dev/posts/type-inference/)

## Limitations

Currently the compiler can only be used from a single thread to avoid deadlocks when accessing the internized type universe. Currently the compiler will panic if the corresponding lock is held when being accessed in write.