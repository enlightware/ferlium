# Runtime Memory Limits

Ferlium's HIR and SSA reference interpreters share a boxed evaluation environment. Their
`ReferenceInterpreterLimits::environment_cell_limit` bounds simultaneously-live entries in that
environment. It is a useful guard against runaway frame and temporary storage, but it is not a
memory quota: one cell may indirectly own a large string, buffer, closure environment, or other
native value.

Exceeding this cell limit aborts the current reference-interpreter execution with
`EnvironmentCellLimitExceeded`. HIR unwinding and SSA exceptional edges run the ordinary semantic
cleanup representable at the failure point, and frame teardown then reclaims the Rust-owned backing
storage. The executor remains usable if this semantic unwind succeeds. Cleanup remains subject to
the same cell limit: if a user-defined drop itself needs unavailable environment storage, Ferlium
can no longer complete the unwind reliably. The executor hard-aborts, becomes poisoned, and performs
only host-controlled storage reclamation from that point. Arbitrary user code must not receive an
unbounded quota exemption merely because it runs during cleanup.

This is host-enforced execution cancellation, not the source-language `Fallible` effect. It does not
change function signatures or the normal status-return ABI. A compiled backend that offers the same
recoverable behavior needs an out-of-band cancellation channel as described in `doc/abi.md`.
The three-level failure policy and future host-resource revocation model are specified in
[runtime-sandboxing.md](runtime-sandboxing.md).

## Shared Wasm failure model

The intended Wasm integration places compiled Ferlium code and the Rust engine in one Wasm instance
and linear memory. The Wasm memory maximum is therefore a last-resort containment boundary, not a
safe script quota. If script-driven allocation exhausts that memory, Rust's allocator may abort or
trap the whole instance, interrupting engine code and potentially leaving the engine unusable.

Before relying on this configuration for robust execution, Ferlium should enforce a lower,
runtime quota while retaining enough uncharged memory for the engine, recoverable unwinding,
hard-abort reclamation, and error reporting:

```text
Wasm linear-memory maximum
├── engine and error-handling reserve
└── Ferlium runtime quota
```

## Proposed direction

Memory accounting should belong to a runtime or sandbox instance rather than to one evaluation.
Values can escape an evaluation, remain in engine state, and enter later evaluations, so a per-call
account cannot assign their lifetime correctly.

A runtime-scoped `MemoryAccount` should provide fallible reserve and release operations. Ferlium
heap objects should retain an RAII charge against that account for the lifetime of their allocation.
Growth should reserve the capacity delta before allocating, use fallible Rust allocation APIs, and
roll the charge back if allocation fails. Reference-counted storage should be charged once for the
underlying allocation rather than once per reference.

The first target should be `Buffer`, because its capacity is directly script-controlled and it
currently allocates a `Vec<Value>` infallibly. Strings and other growable native containers should
follow. Native extensions that own significant external memory will eventually need an accounting
contract of their own.

Allocator bookkeeping, fragmentation, and allocations outside Ferlium-owned containers make exact
prediction impractical. The runtime quota should therefore remain comfortably below the Wasm memory
maximum, and allocation paths should still handle fallible allocation even after successfully
charging the logical budget.

## Non-goals of environment-cell limiting

The environment-cell limit remains useful alongside memory accounting: it cheaply bounds reference
interpreter bookkeeping and catches failures in frame or loop-region reclamation. It should not be
renamed or documented as a general storage or memory limit.

A process-wide Rust global allocator is not the intended accounting mechanism. Ferlium is an
embeddable library, and global or thread-local interception cannot reliably attribute allocations
that outlive an evaluation, move between threads, or originate in host engine code.
