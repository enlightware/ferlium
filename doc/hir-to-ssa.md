# HIR → SSA Lowering Map

This document specifies how the elaborated HIR (`Elaborated` phase) is lowered to
the SSA IR in `src/emit_ssa.rs`. It is the contract that `emit_ssa_fn` and the
`lower_as_place` / `lower_as_rvalue` recursion implement, and the reference the
golden tests in `tests/language/ssa.rs` are written against.

Related docs:
- `doc/hir-ownership.md` — ownership/value invariants the lowering must preserve.
- `doc/abi.md` — the *physical* ABI (deferred; this pass emits a *logical* convention only).

## 1. Scope

**Iteration 1 (this map's "✅ now" rows):** all basic argument passing for scalar
(`TrivialCopy`) and reference (`MutableRef` / `SharedRef`) parameters, dictionaries /
evidence, local frame setup, `let`/`mut` locals, assignment, move-out, and the
`Block`/`Case`/`Loop` control flow needed to exercise them.

**Out of scope (deferred):** `string` heap clone/drop, arrays / `array_index`,
place-results (`FnReturnConvention::Place`), closures, variants, records-by-field.
These are listed below with status `later` so the map stays complete.

The callee-side parameter classification (`Value` / `SharedReference` / `MutableReference`) is
read back from each parameter's `LocalDecl::arg_passing`, which elaboration resolves once with the
trait solver. Lowering never reconstructs it from the parameter type. The physical
register-vs-pointer ABI decision for a by-value (`TrivialCopy`) parameter stays a backend concern
(see `doc/abi.md`): both layers are independent, and a shared-reference parameter is a place in the
SSA regardless of that later decision. Cleanup of a materialized shared-reference temporary
(`temp_cleanup = Drop(d)`) is not emitted yet.

## 2. Model

The lowering mirrors the interpreter (`eval.rs`): a function frame of *places*, each
node lowerable either **as a place** (a pointer SSA value) or **as an rvalue** (a value
SSA value), exactly like `try_eval_node_as_place` vs `eval_node_with_ctx`.

- An **rvalue** is an `ssa::Value` holding the value itself (`%pN`, `%rN`, constants).
- A **place** is an `ssa::Value` that is a *pointer* to storage (an `alloca` register,
  or an incoming by-reference parameter `%pN`).

## 3. Function signature & parameter ordering

A lowered `ssa::Function` has parameters numbered `%p0..` in this fixed order
(matching `emit_ssa_fn` and the interpreter frame layout):

1. **Extra parameters (dictionaries / evidence)** — one per
   `ty_scheme.extra_parameters(...).requirements`, in order. `%p0..%p(k-1)` where
   `k = requirements.len()`. Each is a dictionary value (a tuple of method function
   references), referenced by `ExtraParameterId`.
2. **Runtime arguments** — the visible parameters, which are the *leading*
   `LocalDecl`s of the function (`arg_names`), as `%pk..`. Argument `i` is
   `Parameter(k + i)`.

Closure-environment slots (later) would precede runtime args among the locals but are
out of scope here.

## 4. The slot rule (LocalStorage-following) — LOCKED

For each `LocalDecl` (in slot order), decide its SSA representation from
`LocalStorage` + the parameter's resolved passing. **Do not alloca-everywhere.**

| Local kind | `storage` | Representation | Place? | Rvalue (`load`/read) |
|---|---|---|---|---|
| By-value param (`TrivialCopy`) | `NonOwning` | `Parameter(i)` directly | none | `Parameter(i)` (trivial-copy clone is the same register) |
| By-ref param (`MutableRef`/`SharedRef`) | `NonOwning` | incoming pointer `Parameter(i)` | `Parameter(i)` | `load Parameter(i)` |
| `let` / `mut` / `let mut` local | `Owned { drop }` | fresh `alloca ty` | the alloca reg | `load <alloca>` |
| `Deferred(_)` | — | must be resolved before elaboration (panics otherwise) | — | — |

Consequences:
- Read-only by-value scalar params stay bare `%pN` (no alloca/load) → reproduces the
  existing goldens `simple_functions`, `call_functions`, `user_function_call`.
- Only `Owned` locals introduce `alloca`/`load`/`store`.

**Entry block construction (`emit_ssa_fn`):**
1. Create entry block `0`.
2. For each `Owned` local, append `alloca <local.ty>`; record slot → alloca place.
3. For each by-reference param, record slot → `Parameter(i)` as its place.
4. (No seeding store for by-value params; their value *is* `Parameter(i)`.)
5. Lower the body as an rvalue `v`; emit `ret v` (unless the body already returned).

## 5. Per-node mapping

`P = Elaborated`. "rvalue" / "place" columns give the lowering in each context.
Status: ✅ = iteration 1, `later` = deferred.

### Value construction
| Node | rvalue lowering | Status |
|---|---|---|
| `Uninit` | (target storage left uninitialized; only appears as a `CloneValue` target) | later |
| `Immediate(lit)` | `lower_as_primitive(lit)` → `i32 N` / `i1 b` / `()` constant | ✅ |
| `Tuple(ns)` | build aggregate from lowered elements (needs aggregate-build instr) | later |
| `Record(ns)` | build aggregate | later |
| `Array(ns)` | build array | later (arrays out of scope) |
| `Variant(v)` | build variant (tag + payload) | later |
| `BuildClosure(b)` | build closure value (function ref + captures) | later |

### Value access
| Node | lowering | Status |
|---|---|---|
| `Project(p)` | `project <index> from <rvalue of p.value>` | ✅ (tuple of scalars) |
| `FieldAccess` | record field projection | later |
| `ProjectAt(p)` | `project` via hidden field-index parameter (`LoadFieldIndex`) | later |
| `ExtractTag(n)` | tag extract from variant | later |

### Local storage & ownership
| Node | rvalue lowering | place lowering | Status |
|---|---|---|---|
| `LoadLocal(l)` | per slot rule §4: by-value param → `Parameter(i)`; by-ref param → `load %pi`; owned → `load <alloca>` | by-ref param → `%pi`; owned → `<alloca>`; by-value param → **no place** | ✅ |
| `StoreLocal(s)` | result `()`; lower `s.value`, then write it into slot `s.id`'s place per `s.clone` (see §7) | — | ✅ |
| `TakeLocalValue(t)` | `MoveOwned` → `load <alloca>` + suppress that slot's later drop; `CloneBorrowed(clone)` → clone per §7 | — | ✅ |
| `Assign(a)` | result `()`; lower `a.place` as a place, drop old value per `a.drop` (§7), lower `a.value`, `store` into the place | — | ✅ |
| `CloneValue(c)` | materialize `c.source` as an owned value per `c.clone` (§7) | — | ✅ |
| `CloneClosureEnv` / `DropClosureEnv` | closure env clone/drop | later |

### Calls & function values
| Node | lowering | Status |
|---|---|---|
| `GetFunction(g)` | `Value::Function(reference)` | ✅ |
| `StaticApply(app)` | `call <fn>(<extra dict args...>, <args by §6>)` → `app.ty.ret` | ✅ |
| `Apply(app)` | lower callee as rvalue, then `call <callee>(<args by §6>)` | ✅ (function-typed param) |
| `TraitMethodApply` | does not exist post-dictionary-elaboration | n/a |

### Trait / evidence
| Node | lowering | Status |
|---|---|---|
| `GetDictionary(g)` | `Value::Dictionary([method fn refs...])` from the resolved impl | ✅ |
| `LoadDictionary(l)` | `extra_parameters[l.extra_parameter]` = `Parameter(i)` for that `ExtraParameterId` | ✅ |
| `LoadFieldIndex(l)` | hidden structural field-index parameter | later |
| `GetDictionaryMethod(m)` | `project <entry> from <dictionary rvalue>` | ✅ |
| `GetDictionaryAssociatedConst` | project associated const from dictionary | later |
| `CallDictionaryMethod(c)` | `project <entry> from <dict>` then `call <method>(<args by §6>)` → `c.ty.ret` | ✅ |
| `GetTraitMethod` / `GetTraitAssociatedConst` / `GetTraitDictionary` | pre-dictionary-passing; absent in `Elaborated` | n/a |

### Runtime checks
| Node | lowering | Status |
|---|---|---|
| `CheckCallDepth` / `CheckFuel` | no SSA yet → `Value::Unit` (lower to nothing) | ✅ |

### Control flow
| Node | lowering | Status |
|---|---|---|
| `Block(b)` | lower each `body` node as a statement; value = last node's rvalue (or `()`); then emit cleanup obligations (§8) | ✅ |
| `Return(n)` | lower `n` as rvalue; run aggregated cleanup carried by `n`'s wrapper block (§8); `ret` | ✅ |
| `Case(c)` | alloca result temp; chain of `comp_eq` + `condbr` heads; each body stores into temp + `br tail`; tail `load`s temp | ✅ |
| `Loop(l)` | alloca result temp; record `loop_results[label]`; lower body in a loop block | ✅ |
| `Break(b)` | run cleanups for scopes exited up to the target loop (§8); store value into `loop_results[label]`; branch to loop exit | ✅ |
| `Continue(c)` | run cleanups for scopes exited; branch to loop head | ✅ |

## 6. Argument passing (`ResolvedArgPassing` → SSA)

Each `CallArgument.passing` is consumed directly (never recomputed):

| `passing` | SSA for the argument operand |
|---|---|
| `Value(TrivialCopy(layout))` | lower the arg node **as an rvalue** (a loaded/owned value) |
| `Value(SharedRef { temp_cleanup })` | lower the arg node **as a place** (pointer): forward the place when the node denotes one, otherwise materialize an owned temporary (`alloca` + `store`) and pass its pointer. If `temp_cleanup = Drop(d)`, drop it per §7 after the call (drop emission is deferred) |
| `MutableRef` | lower the arg node **as a place** (pointer); the callee mutates through it |

Extra dictionary arguments (`StaticApply.extra_arguments`) are lowered as rvalues and
prepended to the runtime arguments, matching the parameter order in §3.

## 7. Clone / drop dispatch

Clone (`ResolvedLocalClone`, used by `CloneValue`, `StoreLocal.clone`,
`TakeLocalValue::CloneBorrowed`):

| variant | SSA |
|---|---|
| `TrivialCopy(layout)` | the source rvalue itself (scalar copy is the same register); for aggregates, a representation copy (later) |
| `Static(fn)` | `call <fn>(<src place>) -> dst` (`Value::clone`) | later (non-scalar) |
| `Dictionary(p)` | load clone method from `extra_parameters[p]`, then call it | later (non-scalar) |

Drop (`ResolvedLocalDrop`, used by `Assign.drop`, `Block` cleanup, owned-slot release):

| variant | SSA |
|---|---|
| `Skip` | **no semantic drop**. (For heap-owning reps a native backend still reclaims storage; see `doc/hir-ownership.md` "Non-Contracts".) For scalars: genuinely nothing | ✅ |
| `Static(fn)` | `call <fn>(<place>)` (`Value::drop`) | later (non-scalar) |
| `Dictionary(p)` | load drop method from `extra_parameters[p]`, then call it | later (non-scalar) |

Iteration-1 scalars (`int`, `bool`) resolve to `clone = TrivialCopy` and `drop = Skip`,
so clone is a no-op register reuse and drop emits nothing.

## 8. Cleanup obligations

`Block.cleanup` is a list of owned locals to drop on scope exit (see
`doc/hir-ownership.md`). Lowering treats them as obligations:

- On normal block exit, emit the drop chain (§7) for each cleanup local **still live**
  (not moved-out). `TakeLocalValue::MoveOwned` marks its slot moved → skip its drop.
- `Return`'s operand carries its **own aggregated cleanup** wrapper block; lower that
  wrapper's cleanup minus moved locals (no external scope stack needed for `return`).
- `Break` / `Continue` do **not** carry cleanup; lowering must itself run the cleanups
  of every scope exited between the transfer and its target loop (scope-stack walk).
- Where liveness is statically unknown, use a runtime drop-flag; later SSA const-prop
  deletes provably-dead checks.

For iteration-1 scalars every drop is `Skip`, so cleanup emits nothing — but the
walk/obligation structure must already be in place.

## 9. Worked examples (golden targets)

Type debug for `int` prints `Type { world: Some(0), index: 5 }`; the `Num` impl methods
print as `std::Num<0-6>::add` / `::from_int` etc.

### By-value param, read-only — `fn t(x: int) { x }`
`x` is `NonOwning` by-value → bare `%p0`; trivial-copy clone is `%p0`.
```
fn t:
  0:
    %r0 = ret %p0
```

### `mut` local copy — `fn add_one(mut x: int) -> int { x = x + 1; x }`
slot 0 = by-value param `%p0`; slot 1 = `Owned` copy → alloca, seeded from `%p0`.
```
fn add_one:
  0:
    %r0 = alloca Type { world: Some(0), index: 5 }
    %r1 = store %p0 to %r0
    %r2 = load %r0
    %r3 = call std::Num<0-6>::from_int(i32 1)
    %r4 = call std::Num<0-6>::add(%r2, %r3)
    %r5 = store %r4 to %r0
    %r6 = load %r0
    %r7 = ret %r6
```

### `&mut` ref param (caller side) — `set_1(x)` with `set_1(a) { a = 1 }`
Caller passes the place pointer of its owned `x`; callee's `a` place = `%p`(ref).
The exact dictionary/evidence operands are pinned by the dictionary test.

## 10. Open items (discuss with maintainer)

- `string` drop disposition is provenance-sensitive (literal → `Skip`, cloned →
  `Static`); SSA must use per-local metadata, never the printed type. (Deferred.)
- `return` carries pre-aggregated cleanup but `break`/`continue` do not — confirm intent.
- `LocalDrop::Skip` on heap-owning reps still needs storage reclamation in a native backend.


TODO
- indirect return values (store into out parameter)
  - needed for non-trivial types and generic return values