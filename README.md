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

Embedding it from a Rust host (see [minimal example](examples/minimal.rs)):

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

* **Type inference with generics.** Ferlium infers generic function signatures across a whole module, so `fn add(a, b) { a + b }` needs no annotations. Its inference is [Hindley–Milner-style with constrained types](https://www.researchgate.net/profile/Martin-Sulzmann/publication/220346751_Type_Inference_with_Constrained_Types/links/5ab00c0b0f7e9b4897c1d25b/Type-Inference-with-Constrained-Types.pdf); partial annotations can use `_`.
* **Mutable value semantics.** [Values can be safely mutated with the help of a small borrow checker](https://www.jot.fm/issues/issue_2022_02/article2.pdf), without a garbage collector or explicit lifetime annotations.
* **Algebraic data types.** Records, tuples and tagged unions can be open to additional fields or variants through row polymorphism, or closed. Independently, each can remain structural or gain nominal identity through a Rust-style newtype.
* **Traits and modules.** Traits (type classes) support multiple parameters and associated types, while `module::name` and `use module::*;` organize code.
* **Functional core.** First-class and anonymous functions with closures, pattern matching for destructuring data, and `|>` pipelining for chained transformations.
* **Subscripts and custom projections.** Array indexing and custom projections use subscripts to read or update places; scoped subscripts can run code around an access with `yield`.
* **Compile-time effect tracking.** Ferlium infers `read`, `write`, and `fallible` effects and shows them in signatures and diagnostics, so you can see which functions touch host state or may fail before running them.
* **Optimizing compiler with WebAssembly output.** Ferlium [optimizes its intermediate representation](doc/mir-optimization.md) before generating WebAssembly for browser and Node hosts.

## Getting started

* **Online playground:** <https://enlightware.github.io/ferlium/playground/>
* **REPL:** `cargo run --example ferlium` (use `print(string)` in REPL to print to console).
  Pass `--allow-experimental` to the example REPL or pipe mode to try safe, [experimental language features](docs/book/en/src/experimental.md).
* **Book:** <https://enlightware.github.io/ferlium/book/>
* **Chat:** [ferlium.zulipchat.com](https://ferlium.zulipchat.com)

## How Ferlium compares

Ferlium occupies a niche similar to Lua, Rhai, Rune, or Boa as a script engine for Rust applications, but it is the only one in that group with **full Hindley–Milner type inference and a compile-time effect system**.
Other engines in this space are dynamically typed (Lua, Rhai, Rune, Boa); some offer optional gradual typing.
If your host application benefits from catching type errors before the script runs — and from being able to read at a glance whether a function is pure, reads host state, writes host state, or can fail — Ferlium's tradeoffs are aimed at that case.

### Embedding approach

The integration story also differs from other Rust-embedded scripting engines:

* **No native-type duplication.** Ferlium's intermediate representation does not re-declare primitives like `int` and `bool` as language constructs — they remain native Rust types throughout, which keeps host bindings lean.
* **Direct binding to Rust functions.** Native Rust functions are exposed as Ferlium-callable functions through direct binding in the interpreters and a shared [ABI](doc/abi.md) for generated WebAssembly — no value-conversion ritual, no generated glue. The host chooses which functions scripts can call; scripts have no ambient I/O.
* **Native value handles for host objects.** Host-owned objects can be wrapped as opaque Ferlium values and threaded through scripts — useful for game-engine entities, GPU resources, file descriptors, and the like — without copying.

### Current limitations

Ferlium is pre-1.0; expect breaking changes in syntax, APIs, and standard library.

* The compiler is single-threaded — it currently panics if its interned type-universe lock is contended.
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

Run `make bench` for instruction counts, `make profile-mir` for a quick optimizer comparison, or `make bench-wasm` for WebAssembly timings.
Setup, Callgrind measurements, options, and caveats are in the [benchmark guide](doc/benchmarks.md).

### Fuzzing

Crash-oriented fuzz targets live in `fuzz/` and are run explicitly with `cargo-fuzz`; see [doc/fuzzing.md](doc/fuzzing.md).

### Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for how to contribute.

## License and trademark

Ferlium is copyright Enlightware GmbH and licensed under the [Apache 2.0 license](LICENSE).

"Ferlium" is a trademark of Enlightware GmbH; see [TRADEMARK.md](TRADEMARK.md) for permitted uses.

The tests in `tests/language/` constitute the official [Ferlium Conformance Suite](CONFORMANCE.md).
