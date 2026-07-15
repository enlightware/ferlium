# SSA storage initialization and drop tracking

SSA registers always contain values. Addressable storage is different: a local, temporary, return
slot, or aggregate field may be absent because it has not been initialized yet, has been moved, or
has already been dropped. Cleanup must test that state so every live value is dropped exactly once.

This is an ownership property of storage, not a source-language `Option<T>`, and absence is not an
`ssa::Value` operand. The SSA instructions make the relevant transitions explicit:

- `alloca` creates absent storage;
- `store` initializes absent storage;
- `memcpy` preserves its source and initializes its destination;
- `move` initializes its destination and makes its source absent;
- `drop` acts only on present storage and then makes it absent;
- `clear` makes already-resource-free storage absent without running semantic drop.

A machine backend may realize this model with drop flags and eliminate flags proved constant by
data-flow analysis. The SSA interpreter uses `hir::Value::Uninit` inside its boxed memory model as
the concrete representation of an absent leaf. That interpreter detail is not an SSA value kind.

## Aggregate storage is recursive

The SSA lowering constructs, moves, and drops aggregates field by field. Consequently an aggregate
slot can be partially initialized: some fields are present while others are absent. Initialization
and cleanup are therefore recursive rather than one bit per whole aggregate.

The interpreter calls storage with nothing left to drop a *husk*:

- a flat `Value::Uninit` is a husk;
- a non-empty tuple-backed aggregate is a husk iff every field is recursively a husk;
- anything else is present.

Tuple-backed storage covers tuples, records, and named product types. A guarded `drop` skips a husk;
after dropping a live aggregate it leaves a husk skeleton of the same non-empty shape so its fields
remain addressable for later reinitialization.

Variants and arrays also contain recursively initialized storage, but retain their runtime shell:
variant payloads and array elements may be absent independently. They are not `TrivialCopy`, and
their ownership operations remain explicit.

## Empty aggregates

A zero-field aggregate has no leaf from which to infer presence. The interpreter therefore uses a
single representation convention:

> A present empty aggregate is `Tuple([])`; an absent empty aggregate is flat `Value::Uninit`.

Every husk builder routes through `aggregate_husk`, which collapses an empty skeleton to
`Value::Uninit`. Construction explicitly stores `Tuple([])`. This prevents an unconstructed empty
aggregate from being dropped while ensuring a constructed one receives its semantic drop.

Unit `()` is not an empty aggregate. It is the native scalar `Native(())`, stored in an ordinary
cell like `bool` or `int`; lowering an immediate `()` initializes that cell normally.

## Call boundaries and unwinding

The same storage state is part of the SSA call contract:

- a return out-pointer is absent on entry and present after a normal value return;
- a `let` argument is a present snapshot/borrow that the callee does not consume;
- a mutable-reference argument is present before and after the call;
- an unwind path leaves an unproduced return slot absent and runs guarded cleanup for every live
  local and temporary.

Fallible calls and runtime fuel/call-depth checks use explicit unwind edges when cleanup is pending.
See `doc/ssa-ir.md` for the instruction and boundary contracts.

## Validation

The interpreter asserts that storage-only operations do not hide ownership mistakes: overwriting,
clearing, or reclaiming a cell that still owns resources is a lowering bug. Language tests then run
each compiled expression through both the HIR and SSA interpreters and compare successful values or
runtime-error kinds. Dedicated SSA tests additionally cover partial initialization, empty aggregates,
and cleanup on runtime-resource exhaustion.
