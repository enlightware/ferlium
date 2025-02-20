# Ferlium

[![Build Status][ci-badge]][ci-url]

[ci-badge]: https://github.com/enlightware/ferlium/actions/workflows/ci.yml/badge.svg
[ci-url]: https://github.com/enlightware/ferlium/actions

Created by [Enlightware GmbH](https://enlightware.ch) for use in [Candli](https://cand.li).

**Our mission: To bring the power of Haskell to the users of Python and Javascript**

Ferlium is a small functional scripting language with generics and static typing (à la Standard ML).
It aims at bringing the convenience of writing of Python, the safety of Rust, and the expressiveness of Haskell.
It achieves so by borrowing the type system from Haskell, the syntax from Rust, and a simple mutable value semantics from [recent academic research](https://www.jot.fm/issues/issue_2022_02/article2.pdf).
With that semantics, a function argument is either a value or a mutable reference to a value on the stack, and a simple borrow checker ensures memory safety.
Functions always return values.

Ferlium aims at being lightweight and interfacing nicely with Rust.
In particular, it tries hard not to duplicate existing Rust types and functions when not strictly necessary (e.g., it doesn't have a boolean type distinct of Rust's `bool`).


## Getting started

We provide a playground [here](https://enlightware.github.io/ferlium/playground/).

We also provide a REPL to play locally with the language:
```
cargo run --example ferlium
```

You can reach us on Zulip: [ferlium.zulipchat.com](https://ferlium.zulipchat.com)

## Key features

### For users

* Functional statically-typed scripting language
* Algebraic structural data types (including tagged unions)
* Type inference ([Hindley-Milner style, HM(X) flavor](https://www.researchgate.net/profile/Martin-Sulzmann/publication/220346751_Type_Inference_with_Constrained_Types/links/5ab00c0b0f7e9b4897c1d25b/Type-Inference-with-Constrained-Types.pdf))
* Parametric polymorphism (generics)
* Ad hoc polymorphism through type classes (traits)
* Row polymorphism (for algebraic data types)
* Optional type annotations, including `_` placeholders for type inference
* First-class and anonymous functions
* Pattern matching
* Function pipelining with the `|>` operator
* Mutable value semantics (a simplified version of Rust's ownership system)
* Modules
* Simple copy-on-write optimisation on arrays to maintain acceptable performance

### For developers and integrators

* A pragmatic language: e.g. provides a mutable value semantics
* Avoid re-implementing native types in the IR (i.e., no int, bool, etc. explicit there)
* Smooth binding with native Rust code
* Rich integration possibilities with the native platform (e.g. for platform-managed values)

### Scope and non-scope

The [issues](https://github.com/enlightware/ferlium/issues?q=is%3Aissue+is%3Aopen+label%3Aenhancement) list the planned features.

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

Currently the compiler can only be used from a single thread to avoid deadlocks when accessing the internized type universe.
Currently the compiler will panic if the corresponding lock is held when being accessed in write.

## License

Ferlium is copyrighted by Enlightware GmbH and licensed under the [Apache 2.0 license](LICENSE).
See [CONTRIBUTING.md](CONTRIBUTING.md) for details.