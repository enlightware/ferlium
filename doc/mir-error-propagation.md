# MIR source-error propagation

This document covers failures declared by Ferlium's `Fallible` effect. Sandbox violations instead
poison the executor and leave the MIR CFG; see [runtime-sandboxing.md](runtime-sandboxing.md).

## Explicit error CFG

Source cleanup is language semantics, so MIR represents it without Rust unwinding or interpreter
side tables:

- `invoke <operation> -> bN error bM` executes a source-fallible operation;
- the normal successor receives any operation result;
- the error successor runs reverse-declaration-order cleanup and branches to an enclosing cleanup
  block; and
- the outermost cleanup terminates with `propagate_error`.

Even a cleanup-free fallible operation uses `invoke`, with `propagate_error` as its error successor.
Calls and projections retain their instantiated `CallImplType`, allowing the emitter and verifier to
derive `Invoke` eligibility from the same effect row. An unresolved effect variable is conservatively
fallible. A source-fallible accessor slide is likewise an invoked `end_project`; its effects come
from the consumed open projection.

The interpreter carries the pending error while traversing these blocks. The payload can later be
lowered to an explicit target status/error ABI without changing MIR cleanup structure.

## Cleanup and escalation

Cleanup operations observe the derived initialization state, so moved or already-dropped storage is
skipped. When cleanup itself does not raise, a completed source-error path discharges every tracked
local drop and open-projection obligation exactly once.

`Value::drop` is source-infallible by contract. Accessor slides are currently the cleanup actions
that may raise a source failure:

- if a slide fails during normal scope exit, that failure becomes the primary source failure;
  a dedicated error continuation runs the cleanup actions that have not started yet in the same
  scope, followed by enclosing scopes, without retrying the failed slide;
- if it fails while another source failure is pending, its error successor is
  `failure_during_cleanup`; both failures are retained, the executor is poisoned, and no further
  guest cleanup runs.

A sandbox violation during either ordinary execution or cleanup bypasses all MIR successors. If it
interrupts source cleanup, the pending source failure is retained as diagnostic context.

## Verification

The verifier checks that:

- fallible operations occur only in `invoke` and infallible operations do not;
- invoked results dominate only the normal successor;
- normal and source-error paths do not silently rejoin;
- `return`, `propagate_error`, and `failure_during_cleanup` receive the appropriate error state; and
- ownership state is transferred separately along normal and error edges.

The HIR interpreter performs the equivalent cleanup traversal imperatively. Language tests execute
the same programs through both reference interpreters and compare results and structured errors.
