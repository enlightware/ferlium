# Runtime sandboxing

Ferlium separates source failures from host-enforced sandbox limits. MIR cleanup control flow is
described in [mir-error-propagation.md](mir-error-propagation.md); memory accounting is described in
[runtime-memory-limits.md](runtime-memory-limits.md).

## Runtime outcomes

There are three outcomes besides successful return:

1. A **source failure** is declared by the `Fallible` effect. It follows semantic cleanup and uses
   the status-bearing function ABI. If cleanup succeeds, the executor remains reusable.
2. A **sandbox violation** means that fuel, call depth, interpreter environment, or a future
   accounted-memory limit was exceeded. It is not a source effect and cannot be caught by Ferlium
   code. It immediately poisons the affected execution domain; no further Ferlium cleanup runs.
3. A **failure during cleanup** means a second source failure was raised while propagating an
   earlier source failure. Both causes are retained, the execution domain is poisoned, and guest
   cleanup stops.

The Rust representation makes these cases distinct through `RuntimeError::SourceFailure`,
`RuntimeError::SandboxViolation`, and `RuntimeError::FailureDuringCleanup`. A poisoned interpreter
rejects re-entry. `CompilerSession` owns immutable compiler artifacts rather than an executor
generation, so the REPL, IDE, and other interactive hosts recover by reporting the violation and
creating a fresh executor for the next evaluation.

A cleanup failure during an otherwise successful return is initially a source failure and may
propagate through enclosing cleanup scopes. Escalation happens only if another source failure was
already in flight. A sandbox violation always takes the sandbox path, including when it interrupts
source-failure cleanup; it may retain the interrupted source failure for diagnostics.

## Cleanup, reclamation, and revocation

These operations have separate contracts:

- **Semantic cleanup** runs Ferlium cleanup actions, including `Value::drop` and accessor slides, and
  can have language-visible effects.
- **Storage reclamation** releases a poisoned domain's memory without running Ferlium code.
- **Host-resource revocation** releases engine or browser capabilities independently of guest heap
  traversal and guest cleanup.

The boxed reference interpreters currently reclaim known environment, register, closure-temporary,
and suspended-frame roots explicitly. This is bounded host logic, but `Value` uses `ManuallyDrop`,
so a forgotten owning root could still leak. A compiled runtime should instead make reclamation a
property of its runtime-owned allocation domain, while a take-once registry owns external
capabilities. Poisoning revokes the registry and resets the allocation domain without executing
Ferlium code. Memory accounting and allocator requirements are specified in
[runtime-memory-limits.md](runtime-memory-limits.md).

## Candli integration

Candli objects should hold opaque owning handles into a Ferlium runtime generation. Handles carry
runtime identity and generation information so values from a poisoned generation are rejected.
Ferlium's mutable value semantics does not require a distinct borrowed host handle.

Immutable compiled code and type metadata remain reusable after a runtime reset; mutable Ferlium
handles from the poisoned generation do not. Browser Wasm memory boundaries and the required host
headroom are specified in [runtime-memory-limits.md](runtime-memory-limits.md).

## Future runtime work

The reference interpreters implement the outcome state machine and best-effort bounded reclamation.
The shared compiled/interpreted runtime still needs:

- generation-checked host handles;
- a runtime-owned resource registry;
- an accounted allocator or resettable arena covering native-value allocations;
- an eager shadow call stack for non-unwinding violations; and
- an explicit poisoning/revocation domain shared by all execution backends.
