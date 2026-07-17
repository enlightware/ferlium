# SSA error propagation and cleanup pads

How a language failure or host-enforced execution cancellation unwinds through the SSA form,
attempting each live local's `Value::drop` exactly once on the way out. Cleanup bodies and their
exceptional edges are part of the SSA function rather than behavior invented by the interpreter.
If cleanup itself raises, hard abort stops the remaining semantic drops.

## Failure domains and escalation

Ferlium distinguishes failures declared by the program from cancellation imposed by its executor:

- A **language failure** is represented by the source `Fallible` effect. It is part of the normal
  call contract and uses the status-bearing ABI described in [abi.md](abi.md).
- **Execution cancellation** includes fuel, call-depth, interpreter-environment, and future
  accounted-memory exhaustion. It is not a source effect and is not catchable by Ferlium code. A
  compiled backend propagates it out of band from the normal function result while following the
  same cleanup pads.

The current Rust interpreters use `RuntimeError` as the common internal carrier for both domains.
That implementation convenience does not make execution limits part of a function's effect row or
ordinary return ABI.

Either primary failure follows the cleanup edges described below. If another failure occurs while
that unwind is already running, the executor **hard-aborts**: it preserves both errors, becomes
poisoned, bypasses all remaining semantic cleanup, and performs only host-controlled backing-storage
reclamation. This escalation policy is shared by HIR and SSA and is described in
[runtime-sandboxing.md](runtime-sandboxing.md).

## Why explicit control flow, and not an interpreter-side unwind

The SSA interpreter exists to validate that `emit_ssa` lowers HIR to *semantically correct* SSA that a
real code generator could target. Cleanup on the error path is part of that lowering: a backend needs
the drops-on-unwind expressed as instructions it can emit, not as a runtime convenience hidden inside
the interpreter. So the emitter materializes cleanup as **landing-pad blocks** and records the
instructions that unwind to them. The interpreter merely follows those edges and executes those
blocks — the same division of labour as for normal-path scope-exit drops.

Contrast the HIR interpreter, which manipulates whole frames and unwinds imperatively in Rust
(`drop_frame_owned_locals_on_error`, `src/eval.rs`). The SSA path cannot do that and still be a
faithful lowering oracle: the cleanup has to live in the IR.

## The four pieces

- **`invoke callee(args) -> bN unwind bM`** — a *fallible* call. A terminator with two successors: on
  normal completion control falls to the continuation `bN`; on a raised `RuntimeError` it transfers to
  the cleanup pad `bM`. Operand layout and callee contract are identical to `call`; only the two
  successor blocks are extra. Infallible calls (and fallible calls with nothing to clean up in their
  frame) stay plain `call`s whose error simply propagates to the caller.
- **implicit unwind table** — a sparse function-level table mapping a potentially raising
  instruction to its cleanup pad. It represents exceptional edges for operations without explicit
  successor operands: reference-interpreter allocation, semantically infallible calls that can still
  exhaust a resource quota, and `project` / `end_project` accessor ramps and slides. Keeping this as
  function metadata avoids enlarging every instruction while leaving the edge available to any
  backend. An instruction outside a live cleanup scope has no entry and propagates directly. The
  table can carry either a language failure from a non-call-shaped operation or execution
  cancellation; it does not conflate their source-level ABI contracts. Instructions emitted inside
  an active landing pad deliberately have no further cleanup edge: a second failure hard-aborts
  rather than beginning a replacement unwind.
- **landing pad** — an ordinary block that drops one lexical scope's obligations (reverse declaration
  order, init-guarded) and then `br`s to the pad of the nearest enclosing scope with obligations, or,
  if none, `resume`s. If all cleanup succeeds, chained inner-to-outer pads drop every live frame
  local exactly once.
- **`resume`** — a terminator with no successors that *continues* the unwind the pad interrupted,
  handing the in-flight error back to the caller. It is not a fresh throw: the error was already
  raised by the originating failure or cancellation and merely paused while the pad ran the frame's
  drops; `resume`
  lifts that pause (the name is LLVM's). The caller's explicit `invoke` or implicit call-site unwind
  edge routes the resumed error into the caller's own pad — giving the cross-frame unwind, one frame
  at a time.

## Exactly-once drops during a completed unwind

Pad drops are the *same* init-guarded `drop` instructions the emitter already places on the normal
path. The structural husk rule (see [ssa-uninit-tracking.md](ssa-uninit-tracking.md);
`is_drop_husk`) skips storage that is already dropped or moved out, so a pad drops **unconditionally**
and a value is still dropped at most once: a local dropped on the normal path before a later call
raises reads back as a husk and is skipped by the pad; a local still live when the call raised is
dropped by the pad; a moved-out local is a husk and skipped (matching the HIR interpreter's
`place_contains_uninit` skip). No drop-flag bookkeeping is needed.

If one of those drop instructions raises while the original error is pending, the unwind does not
complete: the executor hard-aborts and reclaims remaining backing storage without running more
Ferlium drops.

## Which calls become `invoke`

A call is lowered as `invoke` iff its HIR node's effects mark it fallible
(`PrimitiveEffect::Fallible`, or — conservatively — an unresolved effect variable) **and** some
enclosing scope has drop obligations (so there is a pad to run). This mirrors real codegen, where only
calls that can throw and have cleanup use `invoke`, and keeps the lowering of the common
(infallible, or cleanup-free) case unchanged.

An infallible `call` nested under live cleanup can still carry a sparse implicit unwind edge,
because backend resource exhaustion is independent of the source effect row. `project` and
`end_project` use the same mechanism: a fallible custom subscript ramp or slide therefore unwinds
the caller even though those instructions are not call-shaped terminators.

## Emitter mechanics: pads are filled last

A block is a contiguous range in a shared instruction arena, so a pad's body cannot be emitted in the
middle of lowering another block — that would splice the pad's drops into the block under
construction. The emitter therefore *allocates* a pad block (empty) the moment an `invoke` needs to
name it, capturing the scope's drop obligations and the outer pad it chains to, and **fills all
pending pads at function finalization**, after the body's last block is terminated. Each pad is then a
clean, contiguous range. See `allocate_pad` / `fill_pending_pads` in `src/emit_ssa.rs`.

## Interpreter mechanics

`run_function` interprets a script callee by recursing in Rust. Explicit checks enforce the same
call-depth and fuel limits as the HIR interpreter. Within a frame, an `invoke` or sparse exceptional
edge stashes the error in a frame-local `pending` and transfers to the unwind pad; the pad's drops
run as ordinary instructions; `resume` returns `Err(pending)` to the caller. If any instruction
raises while `pending` is set, the interpreter constructs a hard abort from the initial and
secondary errors and returns immediately without entering another pad. Cleanup remains subject to
execution limits and does not receive an unbounded resource exemption.

A drop that raises during normal return cleanup is different: no error was previously in flight, so
it becomes the primary error and may unwind enclosing scopes normally. The failed drop's target is
invalidated because its lifetime has ended, but the remaining sibling actions in that same inline
cleanup sequence are currently abandoned; only enclosing scopes continue unwinding. Continuing the
same cleanup sequence after its first failure would require explicit per-action continuation edges
and remains future work.

## Surfacing and testing

`Interpreter::run_entry`, its no-argument `run_main` convenience wrapper, and
`CompilerSession::run_entry_via_ssa` return `Result<Value, RuntimeError>`, so the SSA backend reports
errors instead of panicking. The test harness runs failing snippets through *both* backends under
`Backend::Both` and asserts outcome parity: equal values, matching ordinary error kinds, or matching
hard-abort summaries and both retained cause kinds. The drop-count tests in `tests/language/value.rs`
(e.g.
`lexical_drop_runs_on_runtime_error`, `nested_scope_drops_run_innermost_first_on_runtime_error`,
`cross_frame_drops_run_callee_first_on_runtime_error`) pin that the SSA landing-pad chain drops the
right locals, in the right order, exactly once — checked against the HIR interpreter automatically.

## Known limitations

- Per-iteration / anonymous temporaries are dropped inline today, not via scope obligations; a raise
  mid-temporary-region relies on the HIR interpreter also only unwinding frame-owned locals (parity
  confirmed by tests, not assumed).
- An unresolved effect variable is treated as potentially fallible, which can emit a never-taken
  unwind edge (harmless dead block) in generic code; a later pass can tighten this via the resolved
  effect row.
- If an inline cleanup action raises as the primary error, later sibling actions in that same
  cleanup sequence are skipped. The failed target is invalidated and enclosing scopes still unwind,
  so values are not retried or leaked, but those skipped siblings do not receive semantic drop.
- Register-owned partial values abandoned by an ordinary SSA error are reclaimed without semantic
  drop, matching the HIR interpreter's treatment of anonymous partial results. Making every such
  temporary's cleanup explicit in the IR remains future lowering work.
- Hard abort currently walks the reference interpreters' known environment, register, closure-temp,
  and suspended-frame roots and reclaims their boxed backing storage directly. Because the boxed
  `Value` representation uses `ManuallyDrop`, this is not yet a structural guarantee against future
  forgotten roots. A compiled sandbox still needs the runtime-owned arena, host-resource registry,
  and generation invalidation described in [runtime-sandboxing.md](runtime-sandboxing.md).
