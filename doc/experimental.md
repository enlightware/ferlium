# Experimental Features

Ferlium has a small experimental feature gate for safe language features whose syntax or exact semantics are still being evaluated. The example REPL and pipe mode enable these features with `--allow-experimental`; embedding applications can opt in through the compiler session capability.

Experimental features are not part of the stable source language. They may be renamed, moved, or removed without compatibility guarantees.

## Named Subscripts

Named subscripts are an experimental projection mechanism for places that need bracketed access:

1. run accessor prologue code,
2. `yield` a place,
3. run caller code against that place,
4. run accessor epilogue code.

The temporary use-site syntax is receiver-first:

```ferlium
value->[name]
value->[name](arg1, arg2)
```

This is intentionally provisional. It means "call the named subscript `name` with the receiver as the first argument".

Subscripts are declared as a single signature with one or two member bodies:

```ferlium
subscript cell(slot: &mut int) -> int {
    ref {
        let local = slot;
        yield local
    }

    mut {
        let mut local = slot;
        yield local;
        slot = local
    }
}
```

`ref` is selected for reads. `mut` is selected for assignment and compound assignment. A single shared member can serve both roles:

```ferlium
subscript cell(slot: &mut int) -> int {
    ref mut {
        let mut local = slot;
        yield local;
        slot = local
    }
}
```

When `ref mut` is used, it is the whole bundle body: it cannot be combined with separate `ref` or `mut` members.

Each member must contain exactly one reachable `yield`, and that `yield` must yield a place. A `mut` member must yield a mutable place. For now, the `yield` path must be block-structured: the yield may be nested in blocks, but not inside conditionals, matches, or loops.

Named subscript access is currently accepted only when experimental features are enabled. The syntax is intended for standard-library work, tests, and design experiments such as generalized record-like projections.
