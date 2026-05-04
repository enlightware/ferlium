# Ferlium

[![Build Status][ci-badge]][ci-url]

[ci-badge]: https://github.com/enlightware/ferlium/actions/workflows/ci.yml/badge.svg
[ci-url]: https://github.com/enlightware/ferlium/actions

**A small, statically-typed functional scripting language for Rust hosts. Whole-module type inference, Rust-style syntax, no ambient I/O.**

Created by [Enlightware GmbH](https://enlightware.ch) for use in [Candli](https://cand.li), an educational game engine that teaches children STEAM through visual programming.
Ferlium powers Candli's advanced script blocks: end users write logic the game engine loads, compiles, and runs.

## Quick look

A small Ferlium program:

```ferlium
fn classify(n) {
    if n < 0 {
        "negative"
    } else if n == 0 {
        "zero"
    } else {
        "positive"
    }
}

[-1, 0, 1, 2] |> map(classify)
```

`classify` has no type annotations; Ferlium infers `(int) -> string`, generalising or specialising as needed.
The `|>` operator pipes the array into `map`.
`map` lives in the pre-imported `std` module.

Embedding it from a Rust host:

```rust
use ferlium::{CompilerSession, Path, run_fn_native};

let mut session = CompilerSession::new();
let module_id = session
    .compile(
        "fn answer() -> int { 42 }",
        "demo.fer",
        Path::single_str("demo"),
    )
    .unwrap()
    .module_id;

let result: isize = run_fn_native!(&session, module_id, "answer", [] -> isize).unwrap();
assert_eq!(result, 42);
```

The same `CompilerSession` API is what powers the [Playground](https://enlightware.github.io/ferlium/playground/), the [REPL](examples/ferlium.rs), the benchmark suite (`benches/benches.rs`), and the WebAssembly playground (`playground/`).

## Why Ferlium

* **Type inference with generics.** Functions are automatically generalised — write `fn add(a, b) { a + b }` and Ferlium infers a polymorphic numeric signature; you get parametric polymorphism for free, with no annotations required. The engine is [Hindley–Milner-style with constrained types](https://www.researchgate.net/profile/Martin-Sulzmann/publication/220346751_Type_Inference_with_Constrained_Types/links/5ab00c0b0f7e9b4897c1d25b/Type-Inference-with-Constrained-Types.pdf), and partial annotations with `_` holes are supported where they aid readability.
* **Mutable value semantics.** A simplified version of Rust's ownership model, based on [recent academic work](https://www.jot.fm/issues/issue_2022_02/article2.pdf): function arguments are either values or mutable references to values on the stack, and a small borrow checker keeps mutation memory-safe. No garbage collector, no Rust-level lifetime annotations.
* **Algebraic data, traits, modules.** Structural records and tagged unions, Rust-style new types over them, traits (type classes) with multi-parameter and associated-type support, row polymorphism, and a `module::name` / `use module::*;` system.
* **Functional core.** First-class and anonymous functions with closures (capture by value), pattern matching for destructuring data, and `|>` pipelining for chained transformations.
* **Host-controlled capabilities.** The language has no I/O, no FFI, no filesystem, and no network of its own. Every function a script can call is one the embedding application has explicitly registered. There is no `eval`, no dynamic loader — the host is the security boundary.
* **Compile-time effect tracking.** Effects (`read`, `write`, `fallible`) are inferred per function and propagate through call chains. They show up in inferred signatures and diagnostics, so a reviewer can see at a glance whether a function only computes, touches host state, or might fail. Effects are compile-time information, not a runtime sandbox; runtime isolation is the host's responsibility.

## Getting started

* **Online playground:** <https://enlightware.github.io/ferlium/playground/>
* **REPL:** `cargo run --example ferlium`
* **Book:** <https://enlightware.github.io/ferlium/book/>
* **Chat:** [ferlium.zulipchat.com](https://ferlium.zulipchat.com)

## How Ferlium compares

Ferlium occupies a niche similar to Lua, Rhai, Rune, or Boa as a script engine for Rust applications, but it is the only one in that group with **full Hindley–Milner type inference and a compile-time effect system**.
Other engines in this space are dynamically typed (Lua, Rhai, Rune, Boa); some offer optional gradual typing.
If your host application benefits from catching type errors before the script runs — and from being able to read at a glance whether a function is pure, reads host state, writes host state, or can fail — Ferlium's tradeoffs are aimed at that case.

### Embedding approach

The integration story also differs from other Rust-embedded scripting engines:

* **No native-type duplication.** Ferlium's intermediate representation does not re-declare primitives like `int` and `bool` as language constructs — they remain native Rust types throughout, which keeps host bindings lean.
* **Direct binding to Rust functions.** Native Rust functions are exposed as Ferlium-callable functions through direct binding (interpreted today, with a small [ABI](doc/abi.md) planned alongside the SSA/WASM backend) — no value-conversion ritual, no generated glue.
* **Native value handles for host objects.** Host-owned objects can be wrapped as opaque Ferlium values and threaded through scripts — useful for game-engine entities, GPU resources, file descriptors, and the like — without copying.

### Performance roadmap

Today Ferlium is a tree-walking interpreter. A [Gungraun](https://gungraun.github.io/gungraun/latest/html/index.html)-based benchmark suite tracks instruction counts to catch regressions reliably.
SSA lowering is currently in progress; a WebAssembly backend is planned on top of it, with the goal of calling Rust-compiled-to-WebAssembly hosts with no FFI overhead.

### Current limitations

Ferlium is pre-1.0; expect breaking changes in syntax, APIs, and standard library.

* The interpreter is tree-walking; SSA lowering and a WebAssembly backend are planned but not implemented.
* The compiler is single-threaded — it currently panics if its interned type-universe lock is contended.
* Dynamic dispatch is out of scope.
* No file-based module discovery from script source: module organisation is the host's responsibility (see the [Modules chapter](https://enlightware.github.io/ferlium/book/modules.html) of the book).

The [issue tracker](https://github.com/enlightware/ferlium/issues?q=is%3Aissue+is%3Aopen+type%3AFeature) lists planned features.

### Design philosophy

Design intent: bring the expressive power of ML-family type systems to people who reach for Python or JavaScript — without asking them to learn category theory first.
Its inspirations are:

* ML: basic functional concepts (especially [this course](https://pauillac.inria.fr/~remy/mpri/) and [this one](https://cs3110.github.io/textbook/chapters/interp/inference.html))
* Rust: syntax
* Haskell: type system
* HM(X) approach to type inference ([paper](https://www.researchgate.net/profile/Martin-Sulzmann/publication/220346751_Type_Inference_with_Constrained_Types/links/5ab00c0b0f7e9b4897c1d25b/Type-Inference-with-Constrained-Types.pdf))
* Mutable Value Semantics (especially [this paper](https://www.jot.fm/issues/issue_2022_02/article2.pdf))
* This [series of blog posts](https://thunderseethe.dev/posts/type-inference/)

## Developing Ferlium

### Running tests

`make test-local` runs the suite via [`nextest`](https://nexte.st/), which is significantly faster than `cargo test`.

### Running benchmarks

Install the dependencies once with `make install-deps` (Valgrind + the Gungraun runner), then run `cargo bench`. Gungraun measures instruction counts and other Valgrind-based metrics, which catch small optimisations and regressions reliably even in noisy environments.

### Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for how to contribute.

## License and trademark

Ferlium is copyright Enlightware GmbH and licensed under the [Apache 2.0 license](LICENSE).

"Ferlium" is a trademark of Enlightware GmbH; see [TRADEMARK.md](TRADEMARK.md) for permitted uses.

The tests in `tests/language/` constitute the official [Ferlium Conformance Suite](CONFORMANCE.md).
