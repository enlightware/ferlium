# SSA storage initialization and drop tracking

SSA registers always contain values. Addressable storage is different: a local, temporary, return
slot, or aggregate field may be absent because it has not been initialized yet, has been moved, or
has already been dropped. Cleanup must test that state so every live value is dropped at most once
and, when semantic unwind completes, every still-live value is dropped.

This is an ownership property of storage, not a source-language `Option<T>`, and absence is not an
`ssa::Value` operand. The SSA instructions make the relevant transitions explicit:

- `alloca` creates absent storage;
- `store` initializes absent storage;
- `memcpy` preserves its source and initializes its destination;
- `move` initializes its destination and makes its source absent;
- `drop` acts only on present storage and then makes it absent;
- `clear` makes storage with no live semantic drop obligation absent without running semantic drop.

The verifier derives this state for identifiable local places and product fields across normal and
unwind edges. It joins ordinary ownership facts, while keeping different allocation frontiers and
path-dependent stack-marker snapshots as separate alternatives. The state is analysis data, not part
of `ssa::Function`.

A machine backend may use that analysis to realize genuinely dynamic states with drop flags or
bitsets, while eliminating flags proved constant. The SSA interpreter instead uses
`hir::Value::Uninit` inside its temporary boxed memory model as the concrete representation of an
absent leaf. That interpreter detail is neither an SSA value kind nor part of the future dense-memory
representation.

## Aggregate and empty storage

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

Variants and arrays retain opaque runtime shells, so the verifier tracks their nearest known
enclosing storage rather than inspecting interpreter values.

A zero-field aggregate has no leaf from which to infer presence. The interpreter therefore uses a
single representation convention:

> A present empty aggregate is `Tuple([])`; an absent empty aggregate is flat `Value::Uninit`.

Every husk builder routes through `aggregate_husk`, which collapses an empty skeleton to
`Value::Uninit`. Construction explicitly stores `Tuple([])`. This prevents an unconstructed empty
aggregate from being dropped while ensuring a constructed one receives its semantic drop.

Unit `()` is not an empty aggregate. It is the native scalar `Native(())`, stored in an ordinary
cell like `bool` or `int`; lowering an immediate `()` initializes that cell normally.

## Validation

`ssa::verify` rejects identifiable overwrites, clears, moves, and stack restoration inconsistent
with the derived state. See `doc/ssa-ir.md` for the complete verifier and call-boundary contracts.

Physical allocation leak detection is a separate runtime concern. A future dense-memory
implementation should account allocations in its runtime arena/allocator so instance teardown can
prove that bytes and host resources were reclaimed. That complements this verifier: allocator
accounting cannot prove that a required user-defined semantic drop ran, while SSA ownership analysis
cannot see arbitrary nested allocations made by a native runtime value.
