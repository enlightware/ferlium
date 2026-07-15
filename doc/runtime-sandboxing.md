# Runtime sandboxing and cancellation

This document defines how Ferlium executions fail under program errors and host-enforced limits. It
focuses on runtime state and host-resource safety. The concrete SSA cleanup control flow is described
in [ssa-error-propagation.md](ssa-error-propagation.md), while quota accounting is described in
[runtime-memory-limits.md](runtime-memory-limits.md).

## Three failure levels

Ferlium distinguishes three increasingly severe outcomes:

1. A **language failure** is declared by the source `Fallible` effect. It follows normal language
   semantics, including semantic drops, and is represented by the status-bearing function ABI.
2. A **recoverable execution cancellation** is imposed by the host, for example after fuel,
   call-depth, environment-cell, or future accounted-memory exhaustion. It is not catchable by
   Ferlium code. The runtime runs the same semantic cleanup as for a language failure. The executor
   remains reusable only if that unwind completes successfully.
3. A **hard abort** occurs when another failure is raised while a language failure or execution
   cancellation is already unwinding. At that point Ferlium cleanup semantics cannot be completed
   reliably. The executor is poisoned, no more Ferlium code or semantic drops may run, and runtime
   storage must be reclaimed by host-controlled mechanisms.

The current reference interpreters represent level 3 as `RuntimeError::HardAbort`, retaining both
the initial error and the failure raised during cleanup. Re-entering the poisoned interpreter
returns that hard abort without executing Ferlium code.

A failure raised by cleanup during an otherwise successful return is still a primary failure. It
may unwind enclosing scopes normally. Escalation happens only when a second failure interrupts an
unwind already in progress.

## Semantic drop, storage reclamation, and revocation

These are separate operations:

- **Semantic drop** is Ferlium code. It may maintain language-visible invariants or perform effects,
  and may itself fail or exhaust a limit.
- **Storage reclamation** releases memory without running Ferlium code. It must be infallible from
  the guest's perspective and safe for partially initialized or partially dropped values.
- **Host-resource revocation** releases capabilities such as engine handles, browser resources, or
  external allocations. Its correctness must not depend on finding a value in a partially unwound
  Ferlium heap or successfully running its semantic drop.

The boxed reference-interpreter `Value` representation is temporary, but already follows this
separation: a hard abort stops semantic cleanup and walks the interpreters' known environment,
register, closure-temporary, and suspended-frame roots to discard their remaining Rust backing
storage. This is the reference implementation of abort reclamation, not the intended compiled
representation. Because `Value` uses `ManuallyDrop`, the current walk is regression-tested but not a
structural guarantee: a future owning root omitted from the walk could leak until the interpreter is
destroyed, and host resources still need the registry described below.

Host resources should ultimately live in a runtime-owned registry. Ferlium values contain opaque
handles; normal semantic drop releases an entry with take-once semantics, while hard abort revokes
all remaining entries directly. Revocation must be non-reentrant, bounded, and unable to invoke
Ferlium code. The take-once registry makes normal drop, cleanup, and abort revocation mutually
idempotent instead of relying on every backend to prevent double release dynamically.

## Runtime ownership and Candli integration

Compiled Ferlium values stored in Candli objects should be opaque, owning, rooted handles into a
Ferlium-managed runtime compartment. Ferlium's mutable value semantics does not require a separate
borrowed host handle: host access can copy, move, or mutate through the owning handle according to
the language boundary API. Handles must carry enough runtime identity—typically a runtime reference
and generation—to reject use after their compartment has been poisoned.

A hard abort poisons the mutable Ferlium runtime generation, not immutable compiler artifacts.
Compiled code and type metadata may be reused to create a fresh runtime. Candli objects containing
handles from the poisoned generation must either be discarded with the script execution state or
explicitly reset before the engine resumes. Candli's own data structures remain sound because
Ferlium handles are opaque and validate their generation rather than exposing raw pointers that can
silently dangle.

The intended browser deployment places Rust engine code and compiled Ferlium code in the same Wasm
instance and linear memory. Reaching the Wasm memory maximum may abort or trap the whole instance,
so it is not a recoverable script limit. Ferlium quotas must fire below that boundary, leaving
headroom to construct an error, capture a stack trace, revoke host resources, and reclaim or reset
the Ferlium runtime compartment.

## Arena-backed compiled runtimes

A compiled backend can make hard-abort reclamation structural by placing all Ferlium-owned runtime
allocations in a runtime-scoped arena or accounted allocator. This may include backing storage for
Rust-implemented strings, buffers, closures, and other native values—not only the outer Ferlium
object—provided every allocation path is audited and routed through that allocator. Resetting the
arena then reclaims the entire guest allocation domain without traversing guest objects.

An arena does not by itself cover allocations that escape to Rust's global allocator, reference
counts shared outside the runtime, or external host/browser resources. Such values need allocator
integration, a runtime-owned registry, or both. The desired invariant is a closed ownership domain:
after revoking registered capabilities and resetting the runtime allocator, no allocation or host
resource owned by that runtime generation remains.

## Current scope and future work

The current implementation establishes the three-level state machine in both reference
interpreters, preserves both causes of a hard abort, stops semantic cleanup after escalation, and
rejects executor reuse. It does not yet provide:

- a runtime-wide resource registry or abort-revocation API;
- generation-checked host value handles;
- an accounted allocator or arena reset;
- an eagerly maintained shadow call stack for failures that cannot unwind normally;
- a distinct cleanup reserve for recoverable cancellation.

Those facilities belong to a future runtime/sandbox instance shared by interpreter and compiled
backends. They should strengthen level-3 reclamation without changing language failure semantics or
making execution limits part of Ferlium function types.
