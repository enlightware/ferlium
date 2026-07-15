# SSA IR: Structure, Calling Conventions, and Per-Instruction Invariants

This is the reference for the **invariants** a well-formed Ferlium SSA function must satisfy: the
shape of a function, the calling conventions on its boundary, and the contract of each instruction.
It is the specification the interpreter's verifier checks and that a backend may rely on.

Related documents — this one is the structural/contract reference; those are the deep dives:

- `doc/abi.md` — the *physical* ABI (sizes, alignment, register/stack lowering). SSA records the
  high-level convention; the backend realizes it per `abi.md`.
- `doc/hir-ownership.md` — the HIR ownership model (clone / copy / move / drop) that these
  instructions realize.
- `doc/ssa-uninit-tracking.md` — the liveness / husk model that defines what "initialized" means
  (referenced throughout §4.3).
- `doc/ssa-error-propagation.md` — `invoke` / landing pad / `resume` unwinding (referenced in §5).

Two classes of invariant appear below:

- **Structural** invariants are machine-checked: `Instruction::verify` (per-instruction, §6) and
  `Interpreter::verify_function` (per-function, §6) assert them in debug builds before execution.
- **Semantic** invariants (operand *roles* in §3, the storage-state contracts in §4.3) are not
  recoverable from the IR alone; they are upheld by lowering and checked at the point of use by the
  interpreter's operand resolvers, or relied upon as a contract.

## 1. Model

A function is an ordered list of **parameters** (its signature) plus a set of **basic blocks**, each
a sequence of **instructions** drawn from a shared per-function arena. Values are referenced as:

- `%pN` — parameter `N` (a `ssa::Value::Parameter`), in signature order;
- `%rN` — the register defined by an instruction (a `ssa::Value::Register`);
- `bN` — a block (not a value: block ids appear only as branch targets);
- `@cN` — a reference into the function-local typed constant pool. Each entry is a concrete,
  `TrivialCopy` HIR immediate representation; constants such as `StaticStr` remain opaque until a
  backend lowers the pool for its target. Field indices and tags use the same typed `int` pool
  entries. Symbolic dictionaries/subscripts and function identities are represented directly.

Compile-time match patterns are separate operands, not runtime constants: they may describe an owned
source-language value such as `string` even though the corresponding HIR immediate representation is
`StaticStr`.

SSA is single-assignment: each instruction defines **at most one** result register (its
`InstructionResult`; `Nothing` means it defines none). A result-less instruction's slot must never be
read. Values live in registers or in storage reached through a *place*.

## 2. Function structure (structural invariants)

**Signature ordering.** Parameters occupy the leading `%p` slots in this fixed order (`ParameterTag`):

1. `@extra` — `Dictionary`: generic evidence (a trait dictionary, or a first-class subscript
   value), one per dictionary requirement, in requirement order.
2. `@arg` — `Parameter(ArgConvention)`: the runtime arguments. For a lowered closure (lambda)
   the captured-environment slots come first (they are leading `@arg`s, not part of the surface
   argument list), then the visible source arguments.
3. `@ret` — `Return`: the caller-allocated return out-pointer (see §4.2). Always last when present.

**Blocks.**

- The first block is the **entry**.
- **Every block is non-empty and ends in exactly one terminator**, which appears *only* as the
  block's last instruction. The emitter allocates a block before filling it — to get an identity to
  branch to ahead of emitting its body, for the forward references a `condbr`/`br`/`invoke` or a
  match/loop join needs — but it always fills it (with code, a fall-through `br`, or the trailing
  `ret` at finalization). An empty block is therefore a malformed CFG, not a tolerated state. (A block
  may still be *unreachable* — e.g. the join after a match whose every arm diverges — but it is
  non-empty and terminated; reachability is a separate, unchecked property.)
- The terminators are `ret`, `br`, `condbr`, `invoke`, `resume`, and the unwind-capable forms of the
  runtime checks (classified exhaustively by `InstructionKind::is_terminator`).
- Every branch target (`br`/`condbr`/`invoke` successor, runtime-check successor, and sparse
  implicit-unwind-table target) names an existing block of the same function.

These are exactly what `verify_function` asserts (every block non-empty; terminator-iff-last; targets
valid), in addition to running each instruction's own `verify`.

## 3. Operand roles (semantic invariant)

Each instruction carries a flat `operands: Vec<ssa::Value>` whose length and per-position meaning are
fixed by its kind (§5). Each position expects one of four **roles**, which is part of the contract but
is **not** recoverable from the `ssa::Value` variant (a `Register`/`Parameter` can bind any role).
The role is therefore enforced where the operand is *consumed*, by the interpreter's resolvers:

| Role | Produced by | Consumed by | Resolver |
|------|-------------|-------------|----------|
| **place** | `alloca*`, `subfield`, `dict_entry`, `project`, by-pointer parameter | `load`, `store`, `memcpy`, `move`, `subfield`, `drop`, `call` callee, … | `place_operand` |
| **value** | `load`, `compare_eq`, `variant`, `extract_tag`, `build_closure`, `clone_closure_env`, a constant | `store` value, `compare_eq`, `condbr` cond, … | `value_operand` |
| **dictionary** | `Dictionary`/`Subscript` constant, forwarded `@extra` | `dict_entry`, `subscript_member`, `call`/`project` evidence args | `dict_operand` / `subscript_operand` |
| **stack marker** | `stack_save` | `stack_restore` | `stack_marker_operand` |

A non-trivially-copyable **value** has *exactly one* consuming use (reading it again after it is moved
out is a mis-lowering the interpreter catches). A **place** may be read any number of times.

## 4. Calling conventions

### 4.1 Inputs — argument convention (`ParameterTag::Parameter(ArgConvention)`)

Final HIR has two semantic argument conventions. SSA records the same convention on the parameter;
its current storage-explicit form passes both as places. A physical ABI may later materialize an
already-fresh `Let` value directly when its representation permits that, without changing the
source semantics:

- `MutableRef` — exclusive mutable access to the caller's place for the duration of the call.
- `Let` — immutable, non-escaping access to the argument value for the duration of the call.

Any snapshot required by evaluation order or aliasing is explicit in final HIR before SSA lowering.
`Let` therefore never means “re-read whatever the caller's mutable storage contains”; it observes the
already selected argument value. Whether producing that value uses a representation copy, a semantic
clone, or an ownership transfer is likewise explicit before the call.

### 4.2 Outputs — return conventions (`FnReturnConvention`)

The result type is always `ret`; the convention controls *how* the immediate result is produced and
may be consumed as a place.

- **`Value`** — the function writes its result through the `@ret` out-pointer and `ret`s with no
  operand. This is the default and covers unit returns (which write the live `()` marker — §4.3).
- **`AddressorPlace`** — the function returns a *caller-rooted place*. Its body is `never`-typed and
  ends in `return <place>`, which stores the place **pointer** (`*T`) into the `@ret` slot (an
  `alloca_place`, i.e. `**T`). The caller `load`s the pointer back. Used by addressor subscript
  members (e.g. array indexing).
- **`YieldedOnce`** — a *scoped, callee-rooted yielded place*. The accessor produces **no value
  through `@ret`**; it is entered with `project` (which exposes the yielded place as its own result
  register), suspends at `yield`, and is resumed by `end_project` (§5). It must be consumed through a
  `WithYielded` driver and cannot escape. (A `@ret` slot is still present in the signature for ABI
  uniformity but is unused on the yielded path.)

Provenance ordering: `AddressorPlace` is the strongest borrow-returning convention and can satisfy a
`Value` or `YieldedOnce` consumer; `YieldedOnce` satisfies only a yield driver.

### 4.3 Storage-state invariants at the call boundary

These are the semantic contracts on what the pointee of each by-pointer parameter looks like before
and after a call. "Initialized / live" and "husk" are the recursive, per-field notions defined in
`doc/ssa-uninit-tracking.md` (a live empty aggregate is `Tuple([])`; an absent empty aggregate is
flat `Uninit`, while non-empty aggregates retain a recursive husk skeleton).

- **`@ret` (out-pointer):** points to **husk** (uninitialized) storage on entry. On **normal** return
  it is **fully initialized** — every leaf live. On an **error/unwind** exit (the callee raised before
  producing a result) it is left **husk**, and the caller must not read it — this is what lets a
  "returned" local that was never actually produced read back as a husk so its drop is skipped.
  *Unit / empty-aggregate* returns are no exception — the `@ret` starts a husk and the body must write
  the live marker (`Value::unit()` / `Tuple([])`), so a body that forgets is caught here just like a
  missing scalar result. (`AddressorPlace`'s `@ret` holds a place *pointer*, likewise written on return.)
- **`&mut` (`MutableRef`) argument:** the pointee is **live before and after** the call. The callee
  borrows it exclusively and may overwrite it, but does not own it and so cannot move it out leaving a
  husk.
- **`Let` argument:** the pointee is **live before** and is not mutated or consumed by the callee.

Units flow through real cells (there is no unit-place sentinel), so a unit `@ret`/value is an ordinary
cell obeying the invariants above with no special case. The recursive husk/liveness check
(`is_drop_husk`) is what makes "fully initialized on exit" well-defined for aggregates.

> These boundary storage-state contracts are *semantic* (not yet machine-checked by `verify`). The
> structural arity/terminator invariants in §2 and §6 are.

## 5. Per-instruction reference

Operand arity and roles, the result, and the core invariant of each instruction. `n` is the operand
count. Roles: **p** = place, **v** = value, **d** = dictionary, **m** = stack marker. ★ = terminator.

### Memory

| Instr | Operands | Result | Invariant |
|-------|----------|--------|-----------|
| `alloca ty` | — (or `[witness:d-like place]` if `ty` is not statically sized) | place `*ty` | `n ≤ 1`; the witness is present iff `ty`'s layout is run-time (a generic `Value` dictionary place). |
| `alloca_place ty` | — | place `**ty` | `n == 0`; a slot holding a *pointer* to a `ty` (used for `AddressorPlace`/`project` out-slots). |
| `load` | `[src:p]` | value | `n == 1`; source-preserving load of a representation-copyable pointee into a register (currently used for internal place pointers). Ownership transfer is always an explicit `move`, never a run-time decision made by `load`. |
| `store` | `[v, dst:p]` | — | `n == 2`; writes `v` into `dst`. **Drops nothing:** `dst` must own no live resource (a husk, or a resource-free in-place overwrite) — a resource-owning pointee needs an explicit `drop` first. |
| `clear` | `[dst:p]` | — | `n == 1`; marks already-resource-free storage absent. It is initialization bookkeeping, never a substitute for semantic `drop`. |
| `memcpy` | `[src:p, dst:p]` | — | `n == 2`; a **source-preserving** place-to-place copy of an **owns-nothing**, statically-sized pointee (a scalar, a bare function, or an aggregate of such). A resource-owning value is never `memcpy`d — copying one is a `Value::clone` (a `call`), transferring one is a `move`. |
| `move` | `[src:p, dst:p]` (or `+[witness:p]` if `src`'s layout is run-time) | — | `n ∈ {2,3}`; a **source-consuming** place-to-place ownership transfer of the pointee, leaving the source moved-out. Unlike `memcpy` it consumes the source; unlike a copy it needs no `Value::clone`. The witness (a generic `Value` dictionary place carrying `SIZE`/`ALIGN`) is present iff the pointee's layout is run-time, exactly as for `alloca` — the interpreter moves shape-agnostically and ignores it, a backend sizes the copy from it. The dynamic form prints `move … using {witness}`. |

### Aggregates & variants

| Instr | Operands | Result | Invariant |
|-------|----------|--------|-----------|
| `subfield` | `[agg:p, index:v(int)]` | place `*field` | `n == 2`; place of the field at the `int` index — a constant for a static field, a register for a row-polymorphic run-time offset. Does not read/move the aggregate. |
| `variant tag` | — | value (shell) | `n == 0`; builds a tagged variant *shell* with an uninitialized payload, filled in place via a `subfield` of its destination. |
| `extract_tag` | `[variant:p]` | value (int) | `n == 1`; reads the tag without consuming the variant. |

### Dictionaries (evidence)

| Instr | Operands | Result | Invariant |
|-------|----------|--------|-----------|
| `dict_entry N` | `[dict:d]` | place | `n == 1`; the symbolic analog of `subfield`: the place of function entry `N` in the symbolic dictionary. Trait methods and associated-constant getters are uniformly zero or more-argument functions. A later tuple-lowering pass rewrites it to a `subfield` of a materialized witness table. |
| `subscript_member ref\|mut` | `[subscript:d]` | place | `n == 1`; the member-resolving analog of `dict_entry` for a first-class subscript: the place of the selected `ref`/`mut` member's function value, bundling the subscript's captured hidden evidence — so a `call`/`project` consumes it exactly like a closure callee (prepending that evidence). |

### Calls & control flow

| Instr | Operands | Result | Invariant |
|-------|----------|--------|-----------|
| `call` | `[callee, args.., ret-out?]` | — | `n ≥ 1`. Callee is a constant `Function` or the **place** of a function value, always read *by reference* (never loaded — so a closure environment is never copied). Result goes through the `ret-out` pointer. |
| `invoke … -> bN unwind bM` ★ | as `call` | — | `n ≥ 1`. A *fallible* call: normal completion falls to `bN`, a raised error to the cleanup pad `bM`. Only fallible calls with cleanup to run become `invoke` (see `ssa-error-propagation.md`). |
| `check_call_depth` | — | — | `n == 0`; enforces the runtime's maximum active script-frame depth. With pending cleanup it is a terminator written `check_call_depth -> bN unwind bM`. |
| `check_fuel` | — | — | `n == 0`; consumes one unit of optional execution fuel at a loop/back-edge guard. With pending cleanup it is a terminator written `check_fuel -> bN unwind bM`. |
| `ret` ★ | — | — | `n == 0`; the result is already in `@ret`. |
| `br bN` ★ | — | — | `n == 0`; unconditional branch. |
| `condbr cond, bN, bM` ★ | `[cond:v(bool)]` | — | `n == 1`. |
| `resume` ★ | — | — | `n == 0`; continues the unwind a cleanup pad interrupted, handing the in-flight error to the caller (not a fresh throw). Terminates an outermost pad. |

Instructions without explicit unwind successors may have an entry in the function's sparse
implicit unwind table. The entry is an exceptional CFG edge to a cleanup pad; it covers
resource failures and fallible scoped-accessor ramps/slides without adding fields to every
instruction. Cleanup instructions inside a landing pad have no further unwind entry: if one raises
while the original error is pending, execution hard-aborts. See
[ssa-error-propagation.md](ssa-error-propagation.md).

### Scoped (`YieldedOnce`) subscripts

| Instr | Operands | Result | Invariant |
|-------|----------|--------|-----------|
| `project` | `[callee, args..]` (as `call`, **no** ret-out) | place `*ty` (the yielded place) | `n ≥ 1`; runs the accessor ramp to its `yield`, keeping the frame suspended, and exposes the yielded place as its result register. A ramp error follows the instruction's sparse unwind edge when caller cleanup is live. |
| `yield` | `[place:p]` | — | `n == 1`; inside the accessor body — exposes the place to the driving `project` and suspends the frame. The instructions after it are the *slide* (epilogue), reached only on resume. |
| `end_project` | `[place:p]` (the `project` result) | — | `n == 1`; resumes the suspended accessor's slide and reclaims its frame. Distinct from the unwind `resume`. Runs on the normal exit **and** in the cleanup pad (slide-on-error). A primary slide error follows its sparse unwind edge; a slide error during an active unwind hard-aborts. |

### Cleanup

| Instr | Operands | Result | Invariant |
|-------|----------|--------|-----------|
| `drop` | `[target:p, callee]` | — | `n == 2`; init-guarded — runs the `Value::drop` callee (same callee contract as `call`) only if `target`'s pointee is live, then leaves a husk skeleton. Runs each `Value::drop` at most once. |
| `stack_save` | — | marker | `n == 0`; captures the current stack top. |
| `stack_restore` | `[marker:m]` | — | `n == 1`; reclaims every cell allocated since `marker`. Stack discipline: no live place points above `marker`. |

### Closures

| Instr | Operands | Result | Invariant |
|-------|----------|--------|-----------|
| `build_closure fn(..)` | `[hidden_dicts.., captures.., env_dict?]` | value | `n ≥ num_hidden_dicts + has_env_dict`; bundles `fn` with its hidden evidence and owned value captures; the trailing `Value`-dictionary (iff `has_env_dict`) clones/drops the captured environment. |
| `clone_closure_env` | `[closure:p]` | value | `n == 1`; deep-clones the captured environment, yielding a fresh closure value. |
| `drop_closure_env` | `[closure:p]` | — | `n == 1`; drops the owned captured environment of a closure. |

### Logic

| Instr | Operands | Result | Invariant |
|-------|----------|--------|-----------|
| `compare_eq` | `[a, pattern]` | value (bool) | `n == 2`; matches compile-time literal-pattern metadata against a runtime value, reading the scrutinee **non-consumingly** (a scrutinee place is borrowed, never moved). An incompatible representation shape is an internal lowering error, not a failed match. |

## 6. Verification

Two layers, both run in debug builds before a function executes:

- **`InstructionKind::verify(&self, whole)`** — the exhaustive instruction-kind match checks each
  instruction's operand **arity** (the "Invariant" column above for arity). Adding an instruction
  requires defining its contract alongside those of every other kind. `Instruction::verify`
  delegates to this check. Operand *role* is intentionally not checked here (§3) — it is enforced at
  point of use.
- **`Interpreter::verify_function(func)`** — the per-function structural invariants of §2 (every block
  non-empty; terminator-iff-last-instruction; branch targets exist and are non-empty), and it runs
  each instruction's `verify`.

The point of fast structural verification is to make malformed IR fail with a precise message instead
of an out-of-bounds operand access or silently corrupted interpreter state — the moral equivalent of
the undefined behavior such IR would cause in a real backend.

In addition, the language-test harness executes each compiled expression with both the HIR tree
interpreter and the SSA interpreter. It compares typed results on success and runtime-error kinds on
ordinary failure; for hard abort it additionally compares both retained cause kinds. SSA-only tests
pin textual IR shape, configurable resource limits, and storage invariants that are not directly
observable in a source result.
