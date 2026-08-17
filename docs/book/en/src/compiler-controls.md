# Compiler Controls

Compiler controls let you influence how Ferlium compiles your program without changing its source-level behavior or type.
They are intended for cases where the compiler's default choices need to be adjusted.

## Preventing function inlining

The optimizer normally decides whether to copy a function body into each call site.
You can keep a function as a separate call with the Rust-compatible `#[inline(never)]` attribute:

```ferlium
#[inline(never)]
fn add_one(x: int) -> int { x + 1 }
```

This does not change the function's source-level behavior or type; it only prevents MIR inlining.
Currently, `never` is the only accepted argument to `inline`.
