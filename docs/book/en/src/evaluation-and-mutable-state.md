# Evaluation and Mutable State

This chapter builds the runtime mental model for mutation in Ferlium.
The key idea is simple: arguments are passed by value unless a function requires mutable access, in which case a mutable reference is passed and checked for safety.

## Values vs mutable references

Ferlium calls can behave in two different ways, depending on the callee’s parameter mutability:

- **By value**: the callee receives a value and cannot update the caller’s binding through that parameter.
- **By mutable reference**: the callee receives mutable access to the caller’s place, and assignments in the callee update the caller’s value.

A practical way to read this is:

- if the function only reads its parameter, treat it as value passing;
- if the function writes to its parameter, the call requires mutable passing.

```ferlium
fn plus_one(x) {
    x + 1
}

fn set_1(a) {
    a = 1
}

let mut n = 0;
let r = plus_one(n);
set_1(n);

(r, n)
```

The function `plus_one` computes a new value and does not mutate `n`.
On the contrary, because `set_1` assigns to its parameter, the call requires mutable passing.

## Creating and using a mutable reference

Short reminder: only mutable bindings can be updated. For call passing, this means mutable references are created from mutable bindings when needed.

In Ferlium today, you do not write a separate expression like `&mut x` at the call site. Instead:

- the callee’s parameter mutability (inferred or annotated as `&mut` in function types) determines that mutable passing is required;
- passing a mutable binding supplies that mutable reference;
- passing an immutable binding is rejected.

```ferlium
let mut a = [1];
array_append(a, 2);
a
```

```ferlium,compile_fail
let a = [1];
array_append(a, 2);
a
```

The first program works; the second is rejected because `a` is not mutable.

You can also see mutable references in function type syntax. `&mut` is supported in function argument positions:

```ferlium
fn push_zero(xs: &mut [int]) {
    array_append(xs, 0)
}

let mut data = [1, 2];
push_zero(data);
data
```

## Passing mutable references through helper functions

A mutable reference can be forwarded through multiple calls. This is what makes in-place helper-function design work, including recursive call chains.

```ferlium
fn set_1(a) {
    a = 1
}

fn call_set_1(a) {
    set_1(a)
}

let mut a = 0;
call_set_1(a);
a
```

`call_set_1` does not copy `a`; it forwards the same mutable access, so `set_1` still updates the original binding.

This forwarding model is exactly what recursive in-place algorithms rely on: each recursive step receives mutable access to the same underlying structure (or a non-overlapping part of it).

## Quicksort example

Here is the canonical in-place quicksort algorithm, implemented in Ferlium using mutable references:

```ferlium
fn swap(a, i, j) {
    let temp = a[i];
    a[i] = a[j];
    a[j] = temp
}

fn quicksort(a, lo, hi) {
    if lo >= hi or lo < 0 {
        ()
    } else {
        let p = partition(a, lo, hi);
        quicksort(a, lo, p - 1);
        quicksort(a, p + 1, hi)
    }
}

fn partition(a, lo, hi) {
    let pivot = a[hi];
    let mut i = lo;

    for j in lo..hi {
        if a[j] < pivot {
            swap(a, i, j);
            i = i + 1
        }
    };

    swap(a, i, hi);

    i
}

let mut a = [5, 4, 11, 3, 2, 1, 0, 7];
quicksort(a, 0, array_len(a) - 1);
a
```

How to read this operationally:

- `a` is mutable in the caller (`let mut a = ...`).
- `quicksort` and `partition` receive mutable access to that array through calls.
- `swap` performs writes (`a[i] = ...`) that are visible to all callers in the current call chain.
- No intermediate copies of the array are created; all updates apply to the original binding.

### Aliasing rules enforced today

Ferlium enforces rules to avoid confusing mutable aliasing:

- mutable passing requires mutable places (not immutable bindings);
- overlapping mutable paths in the same call are rejected.

In other words, a single call cannot pass two mutable arguments that point to the same storage region.
This is checked by the compiler and reported as an overlap error.
For example, passing the same array twice as two mutable parameters to a function is rejected.

## Mutation is independent of effects

The effect system from the previous chapter tracks environment interaction and fallibility (`read`, `write`, `fallible`).

Mutable updates to Ferlium-owned values via mutable references are a separate mechanism from environment effects.
A function can be pure with respect to environment effects and still perform in-place mutation on values passed to it.
