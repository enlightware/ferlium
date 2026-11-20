# Compiler Controls

Compiler controls let you influence how Ferlium compiles your program without changing its source-level behavior or type.
They are intended for cases where the compiler's default choices need to be adjusted.
This chapter also describes the limit that the compiler places on how deeply source code nests, and what it means for a host that embeds Ferlium.

## Preventing function inlining

The optimizer normally decides whether to copy a function body into each call site.
You can keep a function as a separate call with the Rust-compatible `#[inline(never)]` attribute:

```ferlium
#[inline(never)]
fn add_one(x: int) -> int { x + 1 }
```

This does not change the function's source-level behavior or type; it only prevents MIR inlining.
Currently, `never` is the only accepted argument to `inline`.

## Hiding values from optimization

The safe `std::black_box(value)` function returns `value` unchanged while preventing the compiler
from reasoning about its contents across that call. It is mainly useful for benchmarks; it is not a
security boundary and does not prevent optimization of unrelated code.

## Nesting limit

Expressions, patterns, types and `use` declarations can each nest at most 128 levels deep; deeper code is a compilation error.
Every block, call, operator and branch is a level, so `a + b + c` takes one level per `+`, and a nested `if` takes two: the `if` and its block.
This keeps deeply nested source from exhausting the compiler's stack.

## Embedding Ferlium

A Rust host compiles and runs Ferlium source through a `CompilerSession`, as `examples/minimal.rs` in the repository shows.
The host should compile on a thread with a generous stack, for instance 4 MiB in a release build and 32 MiB in a debug build.
Rust gives a spawned thread 2 MiB by default, and Windows gives a main thread 1 MiB.
To check a stack size, run the test `nesting_at_the_limit_compiles` with `RUST_MIN_STACK` set to it.
