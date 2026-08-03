# Runtime memory limits

The HIR and SSA reference interpreters share a boxed evaluation environment.
`ReferenceInterpreterLimits::environment_cell_limit` bounds its simultaneously live entries. This
is useful for containing runaway frames and temporaries, but is not a memory quota: one cell can own
a large string, buffer, closure environment, or native value.

Exceeding the cell limit produces `SandboxViolationKind::EnvironmentCellLimitExceeded`. The
executor is poisoned immediately, Ferlium semantic cleanup stops, and the reference interpreter
reclaims its known backing-storage roots using non-guest logic. This does not add the `Fallible`
effect or alter a function's source ABI. See [runtime-sandboxing.md](runtime-sandboxing.md) for the
complete failure policy.

## Browser Wasm boundary

The intended browser integration places compiled Ferlium and Rust engine code in one Wasm instance
and linear memory. Exhausting the Wasm memory maximum may abort the whole instance, so Ferlium must
enforce a lower runtime quota and reserve host headroom:

```text
Wasm linear-memory maximum
├── engine, diagnostics, revocation, and reset reserve
└── Ferlium runtime quota
```

## Accounted runtime memory

Memory accounting belongs to a runtime generation rather than one call because values can escape an
evaluation and enter later evaluations. A runtime-scoped `MemoryAccount` should reserve before
allocation, release when allocation storage is reclaimed, and account shared storage once.

The first target should be `Buffer`, whose capacity is directly script-controlled. Strings,
closures, and other growable native containers should follow. Significant external allocations and
host resources require registry integration as well as byte accounting.

Logical accounting cannot exactly predict allocator metadata, fragmentation, or allocations that
escape Ferlium's allocator. The quota must remain below the Wasm maximum, and allocation paths must
still use fallible allocation after successfully charging the account.

The environment-cell guard remains useful alongside byte accounting, but must not be presented as a
general storage limit. A process-global allocator hook is also unsuitable: Ferlium is embeddable,
and global or thread-local interception cannot reliably distinguish runtime-owned allocations from
host engine allocations.
