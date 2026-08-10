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
    call CSE      // merge repeated addressor and trivial value calls before copying their bodies
    copy forward  // after specialization/call CSE changed the body; coalesce a redundant result slot
    place CSE     // merge repeated subfield and dictionary-entry places
    inline        // budget-limited; block merging inside its own edit
    stop if nothing warranted another round
place CSE          // merge places which inlining exposes
copy forward      // catch copies exposed after the last round
branch forward    // bypass booleans stored in branch arms only to control a second branch
string accumulate // forward an overwritten string into its self-prefixed format builder
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

**Devirtualization** rides along with folding, using its analysis. An indirect dispatch whose callee
the analysis resolved is rewritten to name that callee directly — restricted to a callee read from a
`dict_entry`, because any other place may hold a *closure*, whose captured environment a bare
function operand would silently drop.

This covers `call`, `drop` and `clone`. All three name a callee under the same contract — a constant
function reference, or the place of a function value read by reference and never consumed — and
differ only in where that operand sits, so the operand index is selected by operation kind. The
`Value` methods are the larger population: generic code drops through a dictionary entry far more
often than it calls through one.

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
linear admission preflight finds a payoff that substitution can expose; and the budget allows
another specialization unless one is already cached.

The admission preflight recognizes local devirtualization, trivial-copy clone/drop simplification,
static-layout witness removal, making a small generic body inlinable, and propagation of concrete
types or evidence into a direct generic callee. The last two matter because an apparently unchanged
specialized body can enable work in its caller or callees. Accepted and rejected specialization keys
are both memoized, so a distinct raw body is scanned at most once however many call sites request it.

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

**The visible signature is identical to the original's.** Binding a dictionary parameter replaces
its *uses* and leaves the parameter in place, so no metadata is duplicated — and no HIR record
describes the hidden parameters, which is what lets them go.

**Dead evidence is dropped from the finished module.** Because binding replaces every use, a
specialization has no live evidence parameter by construction rather than by analysis. A final
whole-module pass removes those parameters and the operands that pass them, running once after the
specialization worklist has drained so that every optimization decision above it is taken against
the signatures the optimizer has always seen. One module suffices: `specialize_call_sites` only ever
writes a specialization into a `call` callee operand, self-calls are redirected within the same
table, and every cross-module lookup reads the raw stage, which contains no specializations.

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

The call pass merges statically known calls with identical call metadata and input operands; the
out-parameter is deliberately excluded from the key. For an `AddressorPlace` call it requires two
independently derived callee facts: provenance names the visible argument containing the returned
place, and repeatability proves the address computation has no external effects, does not mutate a
visible argument, and selects a stable place until structural storage changes. `buffer_slot`, whose
body is native, asserts both facts. A duplicate becomes a `memcpy` of the first returned pointer
into the second out-slot.

A `Value` call is eligible when it is direct, its effects permit compile-time evaluation, every
visible argument uses `Let`, and its concrete result implements `TrivialCopy`. Its first result is
then representation-copyable into every duplicate out-slot. The cached value depends on the
contents of all its argument roots and on its first result slot remaining initialized, so a write
to any of those roots invalidates it. Non-copy results remain excluded: reusing one would require
semantic cloning plus ownership and drop accounting.

Availability is a forward CFG intersection. An `invoke` generates a result only on its normal edge,
so replacing a later identical invoke also removes an error edge that the earlier successful call
proved unreachable. A call receiving the provenance root by mutable reference invalidates its
addresses because it may reallocate the object; structural writes and `stack_restore` invalidate
them as well. Writing a value through an addressor-produced leaf does not reallocate its containing
object, which is why `swap` can reuse `a[j]`'s address across the assignment to `a[i]`. The same
write does invalidate a cached value call that read that leaf or its containing root.

This runs inside each optimization round after specialization and before inlining. On
`swap#spec:[int]`, four `array_index::ref_mut` calls become two before the accessor is copied, so the
final body has two bounds/index computations and two `buffer_slot` calls rather than four of each.

The operation pass merges repeated `subfield` and `dict_entry` operations by **dominator-based value
numbering**: a table keyed on the result type and the *canonical* operands, scoped to the dominator
tree, entered on the way down and undone on the way back up. A redundant operation is replaced when
an equivalent one dominates it. Operands are already canonical when an operation is reached, so
comparing two arbitrarily deep expressions is one key comparison and no subtree is re-walked.
Partial redundancy — a value available on some paths only — is out of reach; that needs available
expressions and lazy code motion.

It runs before inlining to merge the repeated dictionary entries generic bodies start with, then
again after the rounds because inlining copies a callee's `subfield` chains into the caller. These
placements target different redundancies: the first shrinks the body the inliner prices, while the
second cleans up what splicing created.

The boundary is narrower than "pure". A `subfield` *derives* a place: the base's root and path with
an index appended, holding no storage of its own, so it is valid exactly where its base is. A
`dict_entry` instead materializes a function place in a fresh cell; `stack_restore` and scoped
projection boundaries therefore kill materialized entries before numbering continues. Other
classes remain out for their own reasons.

- **A memory reader** — `load`, `comp_eq`, `extract_tag` — needs an aliasing argument about the
  writes in between.
- **An owned materialized value**, `build_subscript` among them, cannot be merged at all: such a
  register must have exactly one consuming use, and merging is what gives it two.
- **`subscript_member`** also materializes a function place in a cell, but is not yet represented in
  the computation key. If added, it needs the same stack-region kill as `dict_entry`.

Dominance itself is `mir::dominance`, shared with the verifier, which dominates *instructions* rather
than blocks because an invoked operation's result is anchored at the normal successor and must not
reach the error one. It therefore takes bare successor lists rather than a `Function`.

## Trivial-copy forwarding

`mir::pass::copy_forward` is deliberately separate from call CSE. CSE proves that two computations
produce equal values and safely replaces the duplicate with `memcpy first → second`; it does not
prove that the two mutable result places have interchangeable identities. Forwarding supplies that
storage proof, rewrites reads of the second place to the first, and removes both the copy and the
second `alloca`.

The proof is a linear whole-function use census. Both places must be local `alloca`s in one block,
with the source allocated first. Each has exactly one whole-place write, the destination's write is
the candidate `memcpy`, and every other use is a direct immutable read. A projection, mutable call
argument, ownership transfer, independent write or other escaping use rejects the candidate.
Allocating the source first proves it outlives the destination across any `stack_restore`.

It runs after specialization or call CSE changes a round, before the inliner prices the body, and
once more before final DCE. Structurally viable copies are selected before the whole-function use
census, so unrelated allocations are not tracked. The ten-workload profile contains no dynamically
executed forwardable site, so this pass is not a justification for widening the alias analysis: it
is the bounded cleanup that completes value-call CSE when that source shape occurs. A focused
interpreter profile does execute the shape: `(x - y) * (x - y)` falls from six MIR events to four,
losing one executed result allocation as well as the repeated call.

## Boolean branch forwarding

`mir::pass::branch_forward` removes a boolean storage round-trip created when one control-flow
diamond materializes `true` or `false` and its join immediately compares that slot with a boolean
literal to control a second `condbr`. Each incoming edge already determines the second branch, so
the pass redirects it to that successor. Any `stack_restore`s preceding the comparison are copied
onto every redirected edge; the now-unreachable join disappears, and final DCE removes the local
boolean allocation and its constant stores.

The proof is a linear use and predecessor census and deliberately narrower than general jump
threading. The slot must be a local boolean `alloca`; its only uses must be one known-boolean store
per incoming predecessor and the final comparison; every predecessor must jump unconditionally to
the join; and the join may contain only `stack_restore`s before that comparison. Other operations,
additional uses, unknown stores and self-edges all refuse the rewrite. Supporting integer values or
variant tags would require evidence for a broader predicate-propagation analysis.

## String accumulation forwarding

`mir::pass::string_accumulate` removes the growing-prefix copy in a self-prefixed formatted-string
assignment such as `out = f"{out}{suffix}"`. Lowering ordinarily constructs an empty string, renders
the complete old `out` into it, finishes the formatted value in a temporary, drops `out`, and moves
the temporary back. In a loop this copies the complete prefix on every iteration. The pass instead
moves `out` into the builder, leaves the suffix construction in place, and moves the builder back at
the original assignment commit point. Copy-on-write snapshots still detach on the next mutation.

This is the optimizer's first rewrite that relies on the semantics of named standard-library
operations rather than only on MIR structure. Its correctness contract is that
`string_from_static("")` produces the empty string; the concrete `Value<string>::to_string`
produces an equivalent string value; pushing that value onto an empty string is semantically the
identity; and that both appenders, `string_push_str` and `string_push_static_str`, preserve append
order, value semantics and NFC normalization. All of them have an empty source-effect row. The
proof does **not** rely on strings being implemented with `Rc`; copy-on-write buffer reuse is the
performance consequence, not part of the semantic equivalence. The corresponding maintenance
warning lives beside `String::push_str` in `src/std/string.rs`.

The matcher is deliberately exact. The accumulator, builder and assignment temporaries must be
local string `alloca`s in one block; the old accumulator must be the first builder component and
have no further use before replacement; every builder use must be a direct call to one of the two
appenders; and the construction must end in the emitter's ordinary move/drop/drop/move assignment
tail. Keeping the proof in one block also excludes a catchable source failure, which MIR would
represent as an `invoke` terminator. A linear definition/use census identifies the uses, and final DCE removes the
empty-builder, rendered-prefix and assignment scaffolding orphaned by the rewrite.

## Dead code elimination

Deliberately narrow, and intra-function only.

- An `alloca` goes only when *every* use of it is the destination of a `store` whose value is a pool
  constant, together with those stores. Safe with no ownership analysis: a constant is trivially
  copyable, so no drop obligation is discarded, and the value operand is not a register, so no owned
  register loses its single consuming use — the trap a wider rule hits first.
- An unread `dict_entry` or `subfield` goes. Both derive places without side effects or owned
  results, so deleting one discharges no obligation. A linear use-count worklist handles nested
  `subfield` chains: removing an unread leaf can make its base derivation unread.
- A properly nested same-block `stack_save`/`stack_restore` pair with one restore goes when no
  surviving operation inside may leave current-frame storage allocated. The paired rule runs after
  the other removals, so storage cleanup can make a region empty first.

Constants left unreferenced are pruned from the pool, explicitly, since that renumbers every
`ConstantId`.

## Dynamic profiling

`mir::profile` counts every operation and terminator executed by the MIR reference interpreter. It
provides totals, per-function counts and per-type counts where an operation carries a concrete type;
calls are split into direct and indirect dispatch. Instruction identities reuse the Strum-generated
discriminants of `OperationKind` and `TerminatorKind`, so the profiler does not maintain a second IR
enumeration.

`make profile-mir` compares raw and optimized MIR over the canonical runtime workloads without
Valgrind; `WORKLOADS="fibonacci sieve"` selects a subset. The native profiler and Gungraun share
workload compilation, inputs and typed result extraction through `benches/runtime_workloads.rs`.
Gungraun therefore continues to measure the same execution boundary.

The report orders instructions by broad cost shape — semantic/callee-dependent, size-dependent,
fixed storage, addressing/evidence, scalar/control, then interpreter scaffolding — but assigns no
weights. Native-call cost is callee-dependent and representation-copy cost is type-dependent, so a
single synthetic MIR score would assert backend costs the interpreter cannot establish.

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
