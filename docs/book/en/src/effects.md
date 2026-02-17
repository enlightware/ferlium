# Effects

[Effects](https://en.wikipedia.org/wiki/Side_effect_(computer_science)) describe how a function can interact with its environment beyond pure value computation.
In Ferlium, effects are inferred automatically and make a function’s behavior explicit: whether it may read environment state, write environment state, or fail at runtime.

## What effects mean in Ferlium

A function’s effect set is part of its function type.

- No effects means the function is pure (it only computes from its inputs).
- `read` means the function may read from environment-provided state.
- `write` means the function may modify environment-provided state.
- `fallible` means the function may fail at runtime (for example, division by zero or `panic`).

Effects describe environment interaction and failure behavior; they do not describe mutation of Ferlium-owned state.

## Effect kinds available today

The implemented primitive effects are:

- `read`
- `write`
- `fallible`

These names are visible in inferred function signatures and diagnostics.

## Where you can see effects today

Ferlium shows effects in function type displays when the effect set is non-empty:

- Pure function: `(int) -> int`
- Effectful function: `(int, int) -> int ! fallible`
- Multiple effects: `() -> () ! read, write`

This `! …` suffix appears in inferred function signatures and IDE annotations.
Effect-related compilation errors also report effect sets (for example, incompatible effect dependencies).

Ferlium currently does not provide user syntax to manually write effect constraints; effects are inferred from code.

## Effects are inferred and propagate through calls

You do not declare effects manually. Ferlium infers them from what a function does.

If a function calls another function, the caller inherits the callee’s effects.
This propagation is transitive: effects flow through chains of calls.

## Examples

### Pure function

```ferlium
fn add1(x: int) {
    x + 1
}
```

Inferred signature shape: `(int) -> int` (no effect suffix).

### Function that reads from the environment

```ferlium,ignore
fn current_counter() {
    @props::my_scope.my_var
}
```

Inferred signature shape: `() -> int ! read`.

This uses environment property access. Reading such a property contributes a `read` effect.

### Function that writes to the environment

```ferlium,ignore
fn reset_counter() {
    @props::my_scope.my_var = 0
}
```

Inferred signature shape: `() -> () ! write`.

Writing environment-backed state contributes a `write` effect.

### Fallible function and fallibility propagation

```ferlium
fn quotient(a, b) {
    idiv(a, b)
}

fn quotient_plus_one(a, b) {
    quotient(a, b) + 1
}
```

`idiv` is fallible (for example when `b == 0`), so any function that calls it is also inferred as fallible:

- `quotient` is inferred as fallible.
- `quotient_plus_one` is also inferred as fallible because it calls `quotient`.

Signature shapes:

- `(int, int) -> int ! fallible`
- `(int, int) -> int ! fallible`

## Why effects are useful

Effects make behavior easier to reason about: you can quickly see whether a [function is pure](https://en.wikipedia.org/wiki/Pure_function), interacts with external state, or can fail.

They also support optimization, because pure and less-effectful code can be analyzed and transformed more aggressively than code with broader effects.

## Future direction: async

Ferlium’s current effect system is a base for future execution models.
In particular, async can be layered on top of this effect tracking later, without changing the core idea that effects are inferred and propagated.

## What comes next

The next chapter covers evaluation and mutable state, explaining how Ferlium handles mutation through mutable references and the rules that keep it safe.
