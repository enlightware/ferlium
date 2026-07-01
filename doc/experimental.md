# Experimental Features

Ferlium has a small experimental feature gate for safe language features whose syntax or exact semantics are still being evaluated. The example REPL and pipe mode enable these features with `--allow-experimental`; embedding applications can opt in through the compiler session capability.

Experimental features are not part of the stable source language. They may be renamed, moved, or removed without compatibility guarantees.

## Named Subscripts

Named subscripts are an experimental projection mechanism. They give a name to
place access that can either be a direct addressor projection or a scoped
acquire/yield/release operation.

The temporary use-site syntax is receiver-first:

```ferlium
value->[name]
value->[name](arg1, arg2)
```

This is intentionally provisional. It means "call the named subscript `name` with the receiver as the first argument".
Array indexing is implemented as a standard-library subscript, and it composes with named subscripts:

```ferlium
rows->[row](0)[1]
```

Subscript names are first-class values, distinct from functions:

```ferlium
let first_slot = first;
values->[first_slot]
```

Inside `->[name]`, a visible local named `name` is treated as a subscript value. Otherwise `name` is resolved as a named subscript in the module environment.
Unannotated function parameters used this way infer a first-class subscript capability type.
Abstract first-class subscript use is driven through the yielded interface; addressor-place subscripts are adapted with empty brackets when passed to that interface.
Generic projections also pass hidden first-class subscript evidence and select the `ref` or `mut` member required by the use site; if the receiver later resolves to a concrete structural field, elaboration collapses back to the direct/addressor path.
Source-named subscript values capture the hidden generic evidence needed by their selected type.

If the subscript result itself should be called as a function, parenthesize the subscript access:

```ferlium
(value->[name])(arg)
```

Subscripts are declared as a single signature with one or two member bodies:

```ferlium
subscript first(values: &mut [int]) -> int {
    ref {
        values[0]
    }

    mut {
        values[0]
    }
}
```

Subscripts can also be registered as dot projections for a named receiver type:

```ferlium
subscript Secret.value(self) -> int {
    ref mut {
        self.items[0]
    }
}
```

This makes `secret.value` resolve through the subscript. The qualified receiver (`Secret.value`) provides the projected type; `self` is only the receiver binding name and must not repeat the type. Generic receivers name the receiver type's own parameters in declaration order:

```ferlium
subscript Pair<A, B>.left(self) -> A {
    ref mut {
        self.left
    }
}
```

Explicit projections are rejected when they duplicate an accessible structural field. They are allowed for `#[private_repr]` types, where the representation field is an implementation detail.

`ref` is selected for reads. `mut` is selected for assignment and compound assignment. A single shared member can serve both roles:

```ferlium
subscript first(values: &mut [int]) -> int {
    ref mut {
        values[0]
    }
}
```

When `ref mut` is used, it is the whole bundle body: it cannot be combined with separate `ref` or `mut` members.

A member without `yield` is an addressor subscript. Its tail expression must be a place in existing caller-visible storage; explicit `return place` is also accepted. This is the shape used by standard array indexing and simple field-like projections.

A member with `yield` is a scoped subscript:

```ferlium
subscript cell(slot: &mut int) -> int {
    ref mut {
        let mut local = slot;
        yield local;
        slot = local
    }
}
```

The code before `yield` is the accessor prologue, and the code after `yield` is the epilogue. The caller uses the yielded place between those two parts. Scoped members must contain exactly one reachable `yield`, and that `yield` must yield a place. A `mut` member must yield a mutable place. For now, the `yield` path must be block-structured: the yield may be nested in blocks, but not inside conditionals, matches, or loops.

Named subscript access is currently accepted only when experimental features are enabled. The syntax is intended for standard-library work, tests, and design experiments such as generalized record-like projections.
