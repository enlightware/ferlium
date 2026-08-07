# MIR optimization

How optimized MIR is produced: the passes, the order they run in, and the rules that decide where a
pass belongs. It describes the optimizer as it is; `doc/plans/partial-evaluation.md` holds what is
still missing.

Related documents: [mir-ir.md](mir-ir.md) for the IR itself,
[generic-instantiation.md](generic-instantiation.md) for how a call site records its callee's
instantiation, [runtime-sandboxing.md](runtime-sandboxing.md) for the compile-time execution
contract.

## Staging

Optimization is **opt-in and binary** — one flag per compiler session, off for IDE and REPL work, on
for shipping. There are no levels.

A module's artifacts hold two monotone stages: `raw_mir` as the emitter produced it, and
`optimized_mir`, built at most once. `ModuleArtifacts::mir` selects the stage the *asking session*
wants rather than preferring whatever exists — module revisions, the standard library above all, are
shared between sessions, and a session enabling optimization must not change what another executes.

With the flag off the compiler produces byte-identical MIR to an unoptimized build.

## The driver

Per module, from the optimization hook, which runs after the module entry is installed so the
module's own functions are visible. There is no whole-program pass and no cross-module fixpoint: a
module is optimized once, against immutable revisions of its dependencies.

Per function (`mir::pass::optimize_function`):

```text
for round in 0..MAX_ROUNDS:
    fold          // constant folding, devirtualization; block merging inside its own edit
    specialize    // point generic calls at concrete copies
    addressor CSE // merge repeated caller-rooted place calls before copying their bodies
    inline        // budget-limited; block merging inside its own edit
    stop if nothing warranted another round
subfield CSE       // merge repeated field addresses which inlining exposes
dce               // on every body, not only a changed one
finish            // restores canonical form and re-verifies
```

Then `MirArtifacts::optimize` drains the specializations those rounds requested as a worklist, since
optimizing a specialization may request more.

**Why the rounds.** Specialization makes a generic callee concrete, inlining copies it and binds its
dictionary parameters to constants, folding resolves the callee's `dict_entry`s into known functions,
and the calls that become direct are new candidates for all three. One pass cannot express that
cycle. Fold first within a round: it is cheap, it is what makes arguments known, and it shrinks a
function before the inliner measures it against the growth budget.

**Every pass reads *raw* bodies.** A callee's body, whether in this module or another, is taken from
the raw stage, so what a pass decides never depends on the order functions are optimized in. A
specialization has no raw artifact, so the table keeps each one as it was created, before the
worklist optimized it; that copy is its raw stage.

**Termination** rests on three independent bounds: the dataflow lattice is monotone within a run,
inlining is bounded by its growth budget and the non-recursive restriction, and `MAX_ROUNDS` bounds
the outer loop. Work per function is a product of named constants.

## Placement rules

Four rules, each of which cost a measurement to establish. They apply to any new pass.

1. **A pass that opens its own `FunctionEdit` pays for re-verification of the whole function, per
   round.** Block merging as a driver step measured +3.9% of compile time; folded into the passes
   that create the mergeable shapes, −6.6%.
2. **A rewrite that cannot enable another rewrite must not grant a round.** `Folded` carries
   `warrants_another_round` for this. Devirtualization sets it false: the callees a dictionary entry
   resolves to are overwhelmingly natives, which cannot be inlined and only fold with known
   arguments, so granting a round buys a full cycle that finds nothing — measured +19.2%.
3. **Reuse an analysis rather than building a second one.** The dataflow analysis is the cost of most
   rewrites. Devirtualization as a separate end-of-pipeline pass measured +24.0% because it must
   build its own analysis for every function; riding along with folding, +3.8%. A syntactic
   pre-filter does not save it — nearly every function in a generic standard library has both a
   `dict_entry` and an indirect call.
4. **Cleanup runs on every body**, not only on one a pass changed. A specialization arrives already
   carrying dead code, so "nothing changed it, so nothing is dead" does not hold.

## Folding

Runs a forward dataflow analysis to fixpoint and replaces calls it can evaluate at compile time.
Lattice per register and per `(place root, field path)`: `Unknown | Known(Const) | Uninit`, where a
root is an `alloca`, a parameter, or a `dict_entry`'s cell.

A call folds when the callee is statically known, every visible argument arrives by `Let`, every
argument place holds a known literal, every evidence operand is a constant dictionary, the effects
and result convention permit compile-time evaluation, and the result can be expressed as a MIR
constant. `call f(a, b, ret)` becomes `store @cN to ret`; the surrounding scaffolding is left correct
but dead for `dce`.

A `condbr` on a known condition becomes a jump. A source-fallible call whose evaluation *succeeds*
becomes a store plus a jump to the normal successor, and its error edge dies; an evaluation that
actually fails is refused, so a failure the program may observe is never folded away.

**Escape rules decide whether anything folds at all.** A first version escaped every place reaching a
call, which is safe and useless — every argument place in `2 + 3` is a call argument. What matters is
the convention: `Let` is immutable and non-escaping by the language's own contract, a `MutableRef`
argument escapes, and a call's result place is killed rather than escaped. Everything else is a
whitelist; an operation with no transfer function escapes its place operands.

**Compile-time evaluation is a separate engine** (`mir::const_eval`) with its own tight budget and
its own poisoning domain, reading *raw* bodies. Natives are the main path, not a special case: in
`fn f() -> int { 2 + 3 }` every call is a native `Num<int>` impl. Effects are trusted — a native
declaring neither `Read` nor `Write` is asserted pure and deterministic by its host, and the compiler
may run it at compile time zero, one or many times.

**Devirtualization** rides along with folding, using its analysis. An indirect call whose callee the
analysis resolved is rewritten to name that callee directly — restricted to a callee read from a
`dict_entry`, because any other place may hold a *closure*, whose captured environment a bare
function operand would silently drop.

## Specialization

A generic function is compiled once, its type parameters quantified and its trait constraints turned
into hidden dictionary parameters. Specializing it produces a private copy for one instantiation.

**Both halves are applied together, inside one edit.** Substituting the types without binding the
dictionaries, or the reverse, produces a body whose evidence says `int` while its types say `A`. That
is latent until a pass acts on it, and then unsound: folding evaluates a call at the concrete
instantiation and has nowhere type-correct to put the result. `specialize` takes both, so the
incoherent intermediate is never a `Function` and nothing can verify one.

**A call site's instantiation is recorded, not recovered.** The compiler knows the mapping exactly
once, when `TypeScheme::instantiate_with_fresh_vars` allocates a fresh variable per quantifier;
`FnInstData` keeps it and `emit_mir` carries it into the `Call` operation. The verifier checks that
substituting the callee's declared signature by the recorded arguments reproduces the call's own
type. See [generic-instantiation.md](generic-instantiation.md).

### When a call site is specialized

All of: the callee is statically known and generic and has a body; it is not itself a specialization;
the recorded instantiation is fully concrete; every evidence operand is a constant dictionary; the
body reads at least one dictionary parameter; and the budget allows another specialization unless one
is already cached.

A caller that forwards its own quantifiers records a *variable* instantiation and is skipped —
specializing that caller is what makes its inner call sites concrete on a later round. This is the
cascade, and it needs nothing extra: an instantiation is written in the containing function's type
environment, so substituting the container rewrites it.

The callee need not be in the module being optimized. Cross-module specialization is safe for the
same reason cross-module inlining is: a dependency's revision is immutable.

### What substitution covers

Every parameter's type; the type fields of `Alloca`, `AllocaPlace`, `Call`, `Project`, `Subfield`,
`DictEntry`, `SubscriptMember`, `BuildSubscript`, `Variant`, `BuildClosure`, `CloneClosureEnv`,
`Clone` and `Drop`; the constant pool's types; effects wherever they appear; and **the instantiation
recorded on the body's own calls**, which is what makes the cascade work.

Substitution interns types, and the type universe's lock is not reentrant: nothing may hold
`Type::data()` or `Type::summary()` across it.

### What specialization then removes

Substitution answers questions the generic body could not, so four things follow immediately:

- **Recursive calls are redirected to the specialization.** A recursive call records no instantiation
  — inference types a call within the defining group monomorphically rather than instantiating its
  scheme — so nothing else can redirect it, and the specialization would otherwise recurse into the
  generic original. Sound for the same reason the instantiation is missing: Hindley-Milner cannot
  infer polymorphic recursion, so a self-call is necessarily at its caller's instantiation. Mutual
  recursion is not covered.
- **An `invoke` whose operation became infallible is demoted to a plain operation** plus a jump. A
  call whose effects are a *variable* is conservatively fallible, and instantiating that variable can
  make it infallible; MIR requires the form to agree. Only this direction is possible — a plain
  `call` has no effect variables to instantiate.
- **Layout witnesses are dropped where the type is now statically sized.** `alloca` and `move` carry
  a `Value` dictionary witnessing a run-time layout; substitution is precisely what makes the layout
  static.
- **Clones and drops of types that now own nothing become `memcpy` and nothing.** This retakes the
  decision `resolve_local_clone` and `resolve_local_drop` make during elaboration. The dictionary
  entries they read are then unread, and `dce` removes them.

### Where specializations live

Appended to the **optimized** `MirArtifacts` past the HIR function count. A `FunctionId` names a
function in a context, and the context is `(module, artifact stage)`: past the count it is a
specialization, which exists only in the optimized stage — which is also what tells the stages apart
without a flag.

A specialization has no HIR entry, so everything outside its MIR body — script or native, return
convention, parameter passing, name — comes from `Specialization::original` through one indirection,
`CompilerSession::hir_identity_of`. The interpreter's metadata lookups all go through
`Interpreter::hir_function` for this reason.

**The signature is deliberately identical to the original's.** Binding a dictionary parameter
replaces its *uses* and leaves the parameter in place, so no metadata is duplicated. The parameters
are then dead; removing them is interprocedural work not yet done.

The table is keyed by `(callee, instantiation, dictionaries)`, so two call sites that instantiate a
function the same way share one body. Identities index the *owning* module's table, which is not in
general the callee's module.

**Naming follows the `#impl:` convention**: a readable local name, a `#spec:` marker, and a
discriminator — `twice_it#spec:[int]`. The readable part is the callee's *local* name because every
renderer prepends the module; the canonical string that the hash fallback covers stays fully
qualified. `unique_generated_name` guards collisions.

## Inlining

Copies a callee's body into its call site. It pays twice: it removes the call, which in an
interpreter costs frame setup and argument binding, and it hands folding a body whose parameters have
become the caller's places.

Either an ordinary `call` operation or an `invoke` terminator. The call site's block is split, the
callee's blocks and registers are renumbered and its constants merged into the caller's pool, every
exit is rewired (`return` to the continuation, `propagate_error` to the site's error successor), and
the body is bracketed with `stack_save`/`stack_restore` since the callee's `alloca`s now live in the
caller's frame.

Refused when: the callee is not statically known, has no body, uses an unsupported result convention,
is **generic** — meaning any parameter type is not constant — is recursive (its `check_call_depth` is
the local evidence), contains a scoped accessor, or is over budget. Also when the call site is on a
cleanup path and the callee has error flow of its own, since copying it there would shift its failure
states by one level.

A dictionary parameter is *not* itself a reason to refuse: splicing binds `@extra` parameters like
any other, and a genuinely generic body is already refused for its non-constant parameter types. What
remains is a specialization, whose evidence parameters are concrete and unread.

Cross-module inlining is allowed and is where most inlinable script callees live. It is sound because
function, dictionary and subscript identities are global while constant identities are function-local
and remapped into the caller's pool.

## Common-subexpression elimination

`mir::pass::cse` has a pre-inline call pass and a post-inline operation pass.

The call pass merges statically known `AddressorPlace` calls with identical call metadata and input
operands; the out-parameter is deliberately excluded from the key. It requires two independently
derived callee facts: provenance names the visible argument containing the returned place, and
repeatability proves the address computation has no external effects, does not mutate a visible
argument, and selects a stable place until structural storage changes. `buffer_slot`, whose body is
native, asserts both facts. A duplicate becomes a `memcpy` of the first returned pointer into the
second out-slot.

Availability is a forward CFG intersection. An `invoke` generates an address only on its normal
edge, so replacing a later identical invoke also removes an error edge that the earlier successful
call proved unreachable. A call receiving the provenance root by mutable reference invalidates its
addresses because it may reallocate the object; structural writes and `stack_restore` invalidate
them as well. Writing a value through an addressor-produced leaf does not reallocate its containing
object, which is why `swap` can reuse `a[j]`'s address across the assignment to `a[i]`.

This runs inside each optimization round after specialization and before inlining. On
`swap#spec:[int]`, four `array_index::ref_mut` calls become two before the accessor is copied, so the
final body has two bounds/index computations and two `buffer_slot` calls rather than four of each.

The operation pass merges repeated `subfield` operations — the field addresses a body recomputes —
by **dominator-based value numbering**: a table keyed on the result type and the *canonical*
operands, scoped to the dominator tree, entered on the way down and undone on the way back up. A
redundant operation is replaced when an equivalent one dominates it. Operands are already canonical
when an operation is reached, so comparing two arbitrarily deep expressions is one key comparison and
no subtree is re-walked. Partial redundancy — a value available on some paths only — is out of
reach; that needs available expressions and lazy code motion.

The `subfield` pass runs **once, after the rounds**, because inlining is what creates the redundancy: splicing an
accessor into every call site copies its `subfield` chain along with it. Per round it would pay an
extra edit cycle to catch redundancy that is mostly not there yet, and what it merges enables no
further folding — the fold analysis reads the same operands under one name instead of two.

**`subfield` alone, and the boundary is narrower than "pure".** A `subfield` *derives* a place: the
base's root and path with an index appended, holding no storage of its own, so it is valid exactly
where its base is — and the base is valid at the duplicate, since that is what the duplicate reads
too. Registers are single-assignment, so no intervening write invalidates it either: there is no kill
analysis. Three classes are out, each for its own reason.

- **A memory reader** — `load`, `comp_eq`, `extract_tag` — needs an aliasing argument about the
  writes in between.
- **An owned materialized value**, `build_subscript` among them, cannot be merged at all: such a
  register must have exactly one consuming use, and merging is what gives it two.
- **`dict_entry` and `subscript_member`** *allocate a cell* to materialize the function value into,
  so what they yield lives in the current stack region rather than deriving from an operand's. A
  `stack_restore` between two occurrences pops it. Merging them needs a kill on `stack_restore`.

Dominance itself is `mir::dominance`, shared with the verifier, which dominates *instructions* rather
than blocks because an invoked operation's result is anchored at the normal successor and must not
reach the error one. It therefore takes bare successor lists rather than a `Function`.

## Dead code elimination

Deliberately narrow, and intra-function only.

- An `alloca` goes only when *every* use of it is the destination of a `store` whose value is a pool
  constant, together with those stores. Safe with no ownership analysis: a constant is trivially
  copyable, so no drop obligation is discarded, and the value operand is not a register, so no owned
  register loses its single consuming use — the trap a wider rule hits first.
- A `dict_entry` goes when nothing reads its result. `dict_entry` reads evidence rather than storage,
  has no side effect, and yields a place, so an unread one discharges no obligation. One pass
  suffices: an entry's operand is never another entry's result.

Constants left unreferenced are pruned from the pool, explicitly, since that renumbers every
`ConstantId`.

## Budgets

All in `mir::pass::budget`, all per function except the last. A budget change is a user-visible
change: the optimization report cites them by name.

| constant | value | bounds |
|---|---:|---|
| `MAX_ROUNDS` | 4 | the driver's outer loop |
| `INLINE_CALLEE_OPERATIONS` | 32 | the largest callee inlining will copy |
| `INLINE_FUNCTION_GROWTH` | 128 | growth beyond the size a function had *before* optimization |
| `MAX_SPECIALIZATIONS` | 512 | specializations per module, against the cascade |

Budgets are per function and there is deliberately no global one: a module-wide budget would make
whether one function is optimized depend on what unrelated functions consumed earlier. Growth is
measured against the pre-optimization size, or each round would grant it afresh.

## The optimization report

`CompilerSession::optimization_report`, surfaced as `--optimization-report` in the REPL. **Derived,
not instrumented**: nothing is recorded during optimization: on request the report re-classifies each
remaining call site with each pass's own predicate, so its answers cannot drift from what the passes
decide, and a session that never asks pays nothing.

It counts call sites before and after rather than "folds", which stopped being derivable once
inlining could duplicate calls.

Its blind spot is worth knowing: it classifies **call sites**. A dead `dict_entry`, a redundant
clone, a layout witness that substitution made unnecessary — none of these is a call site, and every
one of them was found by reading generated MIR instead.

## Invariants

- `verify_function` passes on every function a pass produces, under the same debug/test gating as
  today. It is the primary safety net for every rewrite.
- Optimization never changes a program's observable result or its source-failure behaviour. It may
  change fuel and call-depth consumption, which are sandbox policy rather than source semantics.
- **A rewrite must make progress.** A pass may not report having changed something when its rewrite
  reproduces its own input: the driver loops until nothing changes, so a self-reproducing rewrite
  spins to the round cap reporting progress the whole way.
- With optimization off, MIR is byte-identical to an unoptimized build.
- **Host-dependent values must not be frozen into MIR.** A variant tag is an interned host pointer
  (`ustr_to_isize`), so folding an `extract_tag` result into a constant would bake a process address
  into the IR — harmless while MIR is built and run in one process, wrong the day it is cached,
  serialized or cross-compiled.
