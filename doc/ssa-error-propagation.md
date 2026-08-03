# SSA source-error propagation and cleanup pads

This document describes cleanup for failures declared by Ferlium's `Fallible` effect. Sandbox
violations do not enter this control flow: they poison the executor and transfer to bounded runtime
reclamation outside the SSA CFG. See [runtime-sandboxing.md](runtime-sandboxing.md).

## Why cleanup is explicit

Source-failure cleanup is language semantics, so the SSA emitter represents it with ordinary drop
instructions and exceptional CFG edges. A backend must not depend on interpreter-only Rust
unwinding. The HIR interpreter performs the equivalent traversal imperatively.

The current transitional SSA representation uses:

- `invoke callee(args) -> bN unwind bM` for a source-fallible call with live cleanup obligations;
- a sparse implicit-unwind table for source-fallible operations that are not represented by the
  call-shaped `invoke` instruction;
- landing-pad blocks that execute lexical cleanup in reverse declaration order and branch to an
  enclosing pad; and
- `resume` to propagate the already-active source failure to the caller after cleanup succeeds.

Plain sandbox guards (`check_fuel` and `check_call_depth`) have no unwind successor. A sandbox
violation raised by any operation bypasses both explicit and implicit cleanup edges.

The planned canonical MIR refactor replaces instruction ranges and the sparse table with basic
blocks containing operations plus one explicit terminator. It also retains instantiated call and
accessor effect metadata so `Invoke` eligibility can be verified from MIR itself; see
[mir-refactor.md](mir-refactor.md).

## Cleanup and escalation rules

Landing pads use the same initialization-aware cleanup operations as normal scope exit. Moved or
already-dropped places are absent and are not dropped again. A completed source-error path therefore
discharges each remaining ownership obligation exactly once. `Value::drop` is source-infallible by
contract; accessor slides are the current cleanup actions that may raise a source failure.

If a second source failure occurs while a source failure is pending, the interpreter constructs
`RuntimeError::FailureDuringCleanup`, retains both failures, poisons the executor, and stops guest
cleanup. If a sandbox violation occurs at any time, it remains a `SandboxViolation` and takes the
same immediate poisoning path; when it interrupted source cleanup, that source failure can be kept
as diagnostic context.

If an accessor body completed normally but its slide raises, the slide error becomes the primary
source failure. Enclosing scopes then run their cleanup normally. Cleanup actions scheduled after
the slide in the same projection scope are currently abandoned; continuing them requires the
explicit per-action continuation edges planned for canonical MIR.

If a source failure was already being propagated when the slide raised, the result is instead
`FailureDuringCleanup`. The executor is poisoned and no remaining Ferlium cleanup runs, including in
enclosing scopes.

## Interpreter and tests

The SSA interpreter stores a source failure while executing its cleanup pads; `resume` returns that
failure to the caller. `CompilerSession::run_entry` returns `Result<Value, RuntimeError>` for both
reference backends. The test harness compares their structural error summaries and, for failures
during cleanup, both retained causes.

Ownership and drop-order tests in `tests/language/value.rs` cover normal and source-error cleanup.
Limit tests cover executor poisoning, rejection of re-entry, and recovery through a fresh executor.

## Transitional limitations

- Some anonymous partial temporaries are reclaimed without semantic drop on a source error; making
  all such lifetimes explicit remains lowering work.
- Unresolved effect variables conservatively produce source-error edges.
- The sparse implicit-unwind classification over-approximates while accessor metadata is not yet
  retained directly in SSA.
- Reference-interpreter reclamation enumerates known boxed roots rather than resetting a structurally
  owned arena.
