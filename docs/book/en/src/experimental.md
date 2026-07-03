# Experimental Features

This chapter describes language features that are available behind the experimental feature gate.
They are useful for trying current designs, writing standard-library code, and exploring patterns that may become part of the stable language later.
Their syntax or exact behavior may still change.

In the command-line REPL and pipe mode, enable them with `--allow-experimental`.
The playground enables them.

## Custom projections

Custom projections let a named type decide how a field-like access such as `.x` is implemented.
This is useful when the public projection should not be the same as the type's stored representation.

For example, `Pixel` stores its coordinates in an array, but exposes `x` and `y` as ordinary projections:

```ferlium,experimental
struct Pixel {
    coords: [int],
}

subscript Pixel.x(self) -> int {
    ref mut {
        self.coords[0]
    }
}

subscript Pixel.y(self) -> int {
    ref mut {
        self.coords[1]
    }
}

let mut pixel = Pixel { coords: [5, 12] };
pixel.x += 1;

(pixel.x, pixel.y)
```

After these declarations, `pixel.x` and `pixel.y` can be used like ordinary field access.
The `self` parameter names the value being projected; its type is already given by `Pixel`, so it is not written again.

In these projection bodies, the final expression is the stored place that should be exposed.
That is why reads and assignments through `pixel.x` affect `pixel.coords[0]`.

An explicit custom projection is rejected if it duplicates an accessible structural field.
For types whose representation is private, a custom projection can expose a public field-like view without exposing the stored fields directly.

## Direct subscript access

Custom projections are used through dot syntax.
A subscript can also be used directly with the current receiver-first syntax:

```text
value->[name]
value->[name](arg)
```

This means: use the subscript named `name`, passing `value` as the first argument.
The syntax is provisional, and is useful when experimenting with subscripts outside of dot projection syntax.

A subscript declaration has one shared signature and one or two access bodies.
`ref` is used for reads.
`mut` is used for writes and compound assignment.
If the same body supports both, write `ref mut`:

```ferlium,experimental
subscript first(values: &mut [int]) -> int {
    ref mut {
        values[0]
    }
}

let mut values = [10, 20];
values->[first] += 1;
values->[first]
```

When reads and writes need different implementations, write separate `ref` and `mut` bodies.
As with functions, ordinary subscript parameter and result types may be inferred, and `_` can be used as a placeholder annotation.

Array indexing is implemented through the same subscript mechanism, and it composes with custom and named subscripts.

## Scoped subscripts

Some projections cannot return a place directly.
They need to acquire a resource, expose a temporary place, then release or commit after the access.
Those subscripts use `yield`:

```ferlium,experimental
subscript cell(slot: &mut int) -> int {
    ref mut {
        let mut local = slot;
        yield local;
        slot = local
    }
}

let mut value = 1;
value->[cell] += 2;
value
```

The code before `yield` is the prologue.
The code after `yield` is the epilogue.
The caller uses the yielded place between those two parts.

Scoped members must contain exactly one reachable `yield`, and that `yield` must yield a place.
A `mut` member must yield a mutable place.
For now, the `yield` path must be block-structured: the `yield` may be nested in blocks, but not inside conditionals, matches, or loops.

## First-class subscripts

Subscripts can be stored in variables and passed around as values.
The receiving code can then decide which place to access:

```ferlium,experimental
subscript first(values: &mut [int]) -> int {
    ref mut {
        values[0]
    }
}

subscript second(values: &mut [int]) -> int {
    ref mut {
        values[1]
    }
}

fn bump_chosen(values: &mut [int], left, right, use_left) {
    if use_left {
        values->[left] += 1
    } else {
        values->[right] += 1
    }
}

let mut values = [5, 12];
bump_chosen(values, first, second, false);
values
```

Here, `bump_chosen` receives two subscripts and chooses which one to use.
The subscript value is still distinct from a function value: it describes place access, not an ordinary call that returns a value.
