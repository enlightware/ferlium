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
    fold          // constant/semantic folding, devirtualization; block merging in its own edit
    specialize    // point generic calls at concrete copies
    call CSE      // merge repeated addressor and trivial value calls before copying their bodies
    copy forward  // coalesce redundant trivial-copy storage exposed during the round
    place CSE     // merge repeated subfield and dictionary-entry places
    inline        // budget-limited; block merging inside its own edit
    stop if nothing warranted another round
place CSE          // merge places which inlining exposes
copy forward      // catch trivial-copy storage exposed after the last round
branch forward    // bypass booleans stored in branch arms only to control a second branch
peephole          // collapse small local CFG/value patterns
negation          // test a boolean where it is computed, inverting the branch when negated
string accumulate // forward an overwritten string into its self-prefixed format builder
devirtualize      // final dictionary-entry callees exposed too late for a fold round
bounds checks     // prove array indices in range and remove checked access/failure edges
LICM              // hoist invariant pure direct calls with passive inputs and copyable results
dead proven calls // remove unused chains of known-total numeric or proved-returning script calls
dead stores       // remove unread initialization overwritten on every following path
dce               // on every body, not only a changed one
stack markers     // drop a mark duplicating one already held, and restores that pop nothing
tail merge        // hash-cons equivalent tails, collapse equal edges, and fold empty blocks
dead proven + dce // after tail sharing/equal-edge folding, collect its newly dead predicate
finish            // restores canonical form without exposing the intermediate body
```

Then `MirArtifacts::optimize` drains the specializations those rounds requested as a worklist, since
optimizing a specialization may request more. It then shares the specialized bodies that became
identical under optimization, forwards provable last-use arguments into owned ABI variants, drops
the specializations nothing calls, drops dead specialization evidence, and verifies every final
declared and generated body exactly once before installing the optimized artifact.

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

## Overwritten `TrivialCopy` stores

After all value-changing rewrites, a backward CFG liveness pass removes a `store` to a local
concrete-`TrivialCopy` `alloca` when every path replaces that exact whole place before a read. It
recognizes direct `store`, `memcpy`, and infallible caller-provided call-result places as writes, and direct
loads or representation transfers as reads. This removes the initialization in `let mut y = 0; if
b { y = x } else { y = x + 1 }; y` while retaining it if one branch reads `y` first.

The proof intentionally stops at exact roots: subfields, a candidate passed as a call argument,
and ownership transfers *into* the candidate reject the local. It runs immediately before ordinary
storage DCE, which can then remove any allocation or literal made wholly unread.
Stores that consume a freshly constructed owned value are retained, even when their destination is
`TrivialCopy`, because removing them would orphan that value's required consuming use.

Managed storage remains outside this store-liveness proof, but final DCE handles the ownership-safe
subset separately. A semantic clone whose destination is never observed is removed together with
the drops ending that cloned lifetime. This includes a complete dead local lifetime across cleanup
edges and an exact same-block clone/drop pair before the cell is reused. The latter rejects any
read, projection, call argument or other alias-producing use of the local root.

A source-fallible call is an `invoke` terminator, so its result place is deliberately outside this
first pass; the error edge and cleanup would need their own proof. DS has its own strict operand-role
scan rather than reusing the broader escape analysis: that analysis admits `Let` call arguments,
while DS permits only direct reads and whole-place writes of the local root. Any unmodelled use
rejects the candidate, so a future MIR operation cannot silently broaden the rewrite.

## Placement rules

Four rules, each of which cost a measurement to establish. They apply to any new pass.

1. **Internal pass edits restore canonical form but do not cross a verification boundary.** The
   optimizer owns every intermediate body, then verifies final artifacts once after whole-module
   cleanup. Raw lowering, generated specialization/substitution inputs consumed by another pass,
   and final optimized artifacts remain checked boundaries. Keep related canonical cleanup in the
   pass that creates it to avoid another body decomposition and reconstruction.
2. **A rewrite that cannot enable another rewrite must not grant a round.** `Folded` carries
   `warrants_another_round` for this. Devirtualization sets it false: the callees a dictionary entry
   resolves to are overwhelmingly natives, which cannot be inlined and only fold with known
   arguments, so granting a round buys a full cycle that finds nothing — measured +19.2%.
3. **Reuse an analysis rather than building a second one.** The dataflow analysis is the cost of most
   rewrites. Devirtualization rides along with folding for this reason. A final devirtualization
   sweep exists only for dictionary-entry callees exposed after the last fold round; it first runs a
   cheap syntactic filter and then lets DCE remove the entries it strands.
4. **Cleanup runs on every body**, not only on one a pass changed. A specialization arrives already
   carrying dead code, so "nothing changed it, so nothing is dead" does not hold.

## Folding

Runs a forward dataflow analysis to fixpoint and replaces calls it can evaluate at compile time.
Lattice per register and per `(place root, field path)`: `Unknown | Known(Const) | Uninit`, where a
root is an `alloca`, a parameter, or a `dict_entry`'s cell. `Const` includes scalar/tuple literals,
symbolic functions, dictionaries and variant tags, plus a constructive array recipe of known
`TrivialCopy` elements; the latter is not a mutable array stored in the constant pool.

A call folds when the callee is statically known, every visible argument arrives by `Let`, every
argument place holds a known literal or constructive array, every evidence operand is a constant
dictionary, the effects and result convention permit compile-time evaluation, and the result can be
reified as MIR. `call f(a, b, ret)` becomes `store @cN to ret` for an immediate result, or
`build_array` directly into `ret` for an array of `TrivialCopy` elements. The surrounding
scaffolding is left correct but dead for `dce`.

Two entries need no known argument at all. `Num<int>::from_int` is the conversion every integer
literal is desugared into, and at `int` it converts nothing, so the call becomes a copy of its
argument. That case is rarer than it sounds — std leaves no such call, since a literal argument is
known and folds outright — but a specialization at `int` of a generic body can. `not` has no MIR operation of its own, but `comp_eq value false` is exactly it, so the
call becomes that comparison — which is also what puts the value where the later passes can read
it, a call being opaque to all of them. Both step aside for a *known* argument: evaluating the call
outright yields a constant, which beats copying the cell that held it or comparing it at run time.

The pass also names the constants a `build_array`'s element slots hold, rather than reading them
back out. An element operand may be a materialized value as readily as a place — verification admits
either, and the reification above already emits the constant form — but the lowering of a source
array literal stores each element into a fresh slot only for the construction to read it straight
back. Substitution is per operand, so a literal beside an unknown element still becomes a constant
while the unknown one keeps its slot, and `dce` collects whatever became unread. This buys no round:
the array's own fact is derived from these same element facts, so the next round's analysis learns
nothing from the rewrite.

The same pass also simplifies a call from a documented std contract when only the relevant
arguments are known. Callees are recognized by resolved `FunctionId`, including through
specialization, rather than by name or body shape. For `int`, it applies the wrapping-sound
identities `0 + x`, `x + 0`, `x - 0`, `x - x`, `0 * x`, `x * 0`, `1 * x`, `x * 1`, and reflexive
comparison. For `float`, Ferlium values are finite but retain observable signed zero, so the safe
set is narrower: `x - +0.0`, `x - x`, `1.0 * x`, `x * 1.0`, and reflexive comparison. In
particular, neither `x + 0.0` nor `x * 0.0` is rewritten for an unknown float.

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

Inlining can expose one last `dict_entry`/dispatch pair after the final fold round. A final
devirtualization sweep catches only those known dictionary-entry callees before DCE, so the now
unread entries are removed without reopening the fold/specialize/inline loop.

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
`DictEntry`, `SubscriptMember`, `BuildSubscript`, `Variant`, `BuildArray`, `BuildClosure`,
`CloneClosureEnv`, `Clone` and `Drop`; the constant pool's types; effects wherever they appear; and **the instantiation
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

**An ordinary monomorphization's visible signature is identical to the original's.** Binding a
dictionary parameter replaces its *uses* and leaves the parameter in place, so no metadata is
duplicated — and no HIR record describes the hidden parameters, which is what lets them go. The
later owned-argument pass may create an optimized-only ABI variant with selected visible parameters
changed to ownership transfer.

**Dead evidence is dropped from the finished module.** Because binding replaces every use, a
specialization has no live evidence parameter by construction rather than by analysis. A final
whole-module pass removes those parameters and the operands that pass them, running once after the
specialization worklist has drained so that every optimization decision above it is taken against
the signatures the optimizer has always seen. One module suffices: `specialize_call_sites` only ever
writes a specialization into a `call` callee operand, self-calls are redirected within the same
table, and every cross-module lookup reads the raw stage, which contains no specializations.

## Owned argument forwarding

`mir::pass::owned_arguments` removes the interprocedural `clone(x); ...; drop(x)` left when a
borrowing `Let` parameter retains a caller temporary. The `Value` laws make this equivalent to
moving `x`: the pass marks the call operand as owned, removes the caller drop, and creates a cached
callee variant whose parameter is `@arg owned`. The parameter's sole, exit-dominating ownership sink
must be either a static-layout `clone`, replaced by `move`, or a direct call to which ownership can
be forwarded. The latter carries ownership through generated trait-method thunks into specialized
bodies.

Admission is conservative. The caller operand must be a whole local allocation, unaliased at the
call, and used afterwards only by its terminal cleanup drop. A fallible call requires equivalent
drops on its unique normal and error successors. The callee parameter must have exactly one use,
and ordinary generic bodies with live dictionaries are not copied; their concrete specializations
are. Variants are cached by `(callee, owned argument set)` and bounded independently.

This pass runs once after the specialization worklist, outside the fold/inline loop, because it
needs the completed local call graph and changes an optimized-only ABI. DCE and stack-marker cleanup
run on its results before dead-evidence removal and final verification.

The table is keyed by `(callee, instantiation, dictionaries)`, so two call sites that instantiate a
function the same way share one body. Identities index the *owning* module's table, which is not in
general the callee's module.

**Sharing is decided three times, because a key is finer than the body it produces.** Type, effect
and evidence arguments all enter the key, but only what survives substitution enters the body:
effects are erased unless they changed a control-flow form, and a dictionary appears only where it
was used.

1. The key cache answers a repeated call site outright, without substituting anything.
2. A structural identity over the residual body catches a *new* key whose MIR turns out to be a
   function already created — which needs the body built to be recognized at all.
3. `share_specializations` catches the copies that were created distinct and *converged*, once
   folding and inlining resolved what separated them. It runs over the finished module, after the
   worklist drains and before the owned-ABI variants below, so those are built from the deduplicated
   set.

The identity is the same throughout: the original plus the result convention, parameters, constants
and code, with the generated name and the body's own id — the two properties of *which copy this
is* — normalized away. A digest selects candidates and a derived comparison decides, so a collision
costs a sharing and can never merge two bodies that differ. Bodies are shared within one original
and never across two, because a specialization's metadata is answered through
`Specialization::original`: two originals with identical MIR can still declare different parameter
passing or return conventions.

Merging finished bodies adds an obligation creation-time sharing does not have: the grouping repeats
until a round merges nothing, since two bodies that call two copies of one callee are equal exactly
when those copies merge.

**A specialization nothing calls is then dropped.** The optimizer keeps working on the site it made
a copy for, and may inline that copy, specialize the caller so the reference moves to a copy of it,
or redirect the call to an owned-ABI variant — each leaves a finished body nothing names. Unlike a
declared body, a specialization needs no root analysis to be shown unreachable: `specialize_call_sites`
only ever writes one into a call callee operand, self-calls are redirected inside the same table,
every cross-module lookup reads the raw stage, which holds no specializations, and dictionaries name
impls rather than functions. So the declared bodies are the roots in full, and one transitive closure
answers it — transitive because a dropped body may be the only thing naming its own callees, and
without a fixpoint because liveness only shrinks. `MirArtifacts::pruned_specializations` records how
many were dropped, which the optimization report states: once the bodies are gone, nothing else can
say how much of what specialization built was thrown away.

Pruning runs **after** the owned-ABI variants and sharing **before** them, which is why they are two
passes rather than one. Sharing must precede them so the variants derive from the deduplicated set;
pruning must follow, or every body orphaned by a redirect to a variant survives.

Both compose their decision with the compaction of the table into a single rewrite, in
`specialization_table`, so no id is ever held across a renumbering. That rewrite reaches a function
wherever a body names one, including `build_closure`, which carries its function in the operation
kind where no operand walk sees it; `Function::visit_function_ids` is its read-only twin, and the two
must agree — a reference only one of them reaches is either a body kept alive by nothing or a live
reference the rewrite fails to renumber.

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
the local evidence), carries `#[inline(never)]`, contains a scoped accessor, or is over budget. Also
when the call site is on a cleanup path and the callee has error flow of its own, since copying it
there would shift its failure states by one level. The annotation remains on the source HIR
definition; the inliner resolves a MIR callee identity back to that definition, and specializations
inherit the policy of their original function.

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
semantic cloning plus ownership and drop accounting. When the callee still has a module-table
definition, its declared parameter-passing conventions are authoritative; this prevents incomplete
generated-call metadata from hiding a mutable argument. Optimizer-created callees fall back to the
conventions retained in their call type.

Although MIR passes call arguments indirectly, independently lowered literal occurrences still
denote the same value. The call pass's first input walk records eligible call sites and constant
stores together. Only when an over-approximate fingerprint can repeat does it run the conservative
use proof, which accepts local `alloca` cells with exactly one constant store whose other uses are
exclusively visible `Let` arguments. Those operands are keyed by the typed constant rather than by
the fresh cell. The cells themselves are not merged: call CSE removes the duplicate computation and
ordinary storage DCE then removes the unread materialization. A second store or any reference,
projection, ownership, result-slot or control-flow use rejects the equivalence. Addressor calls
never use it because equal pointees do not make two places identical.

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

## Storage forwarding

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

The same pass more generally retargets `producer → temporary; transfer temporary → destination` so
the producer initializes the final destination directly. Producers are `store`, `memcpy`, `move`,
`clone` and `call`; the final transfer may be `move` or, for a `TrivialCopy`, `memcpy`. The operations
must be adjacent, the temporary must be a local `alloca`, and its complete operand-use count must
consist of exactly the producer destination and transfer source. Contiguous transfer chains are
collapsed in one traversal rather than requiring another optimization round.

Retargeting must not make a producer overwrite storage it also reads. A small place-identity model
tracks allocation/parameter roots and constant `subfield` paths, proving different roots and sibling
fields disjoint while rejecting opaque `project` provenance. Calls and clones receive one additional
exception: a resolved native with a `TrivialCopy` result computes its owned HIR result before the MIR
bridge stores it, so its result may safely reuse an input place. This permits arithmetic writeback
such as `call add(%x, %y, %x)` without weakening the fresh-result contract for script calls.

Its cheap structural scan runs each optimization round before the inliner prices the body, and once
more before final DCE. The linear whole-function use census runs only when that scan finds a viable
candidate, and tracks only participating allocations. The original CSE result-slot shape has no
dynamically executed site in the corpus; a focused interpreter profile does execute it:
`(x - y) * (x - y)` falls from six MIR events to four, losing one executed result allocation as well
as the repeated call. General producer forwarding reduces optimized execution on the eleven-workload
profile from 3,517,325 to 3,423,626 events (-2.66%), including moves from 59,248 to 18,155 and
allocations from 812,240 to 767,872. `iter_pipeline` falls from 603,589 to 576,801 events (-4.44%),
with moves from 14,039 to 645, allocations from 136,187 to 122,793, and peak cells from 59 to 58.

## Boolean branch forwarding

`mir::pass::branch_forward` removes a boolean storage round-trip created when one control-flow
diamond materializes `true` or `false` and its join immediately reads that slot to control a second
`condbr`. Each incoming edge already determines the second branch, so the pass redirects it to that
successor. Any `stack_restore`s preceding the read are copied onto every redirected edge; the
now-unreachable join disappears, and final DCE removes the local boolean allocation and its
constant stores.

Both forms of that read are recognized. A boolean alternative head lowers to `load`, and that is
the shape the pass sees in practice; a `comp_eq` against a boolean literal is the older shape, kept
accepted because it is equally provable and costs one match arm. Each names the slot and carries a
polarity: a `load` takes the *then* edge when the arm stored `true`, a `comp_eq` when the arm
stored the pattern it compares against.

The proof is a linear use and predecessor census and deliberately narrower than general jump
threading. The slot must be a local boolean `alloca`; its only uses must be one known-boolean store
per incoming predecessor and the final read; every predecessor must jump unconditionally to the
join; and the join may contain only `stack_restore`s before that read. Other operations, additional
uses, unknown stores and self-edges all refuse the rewrite. Supporting integer values or variant
tags would require evidence for a broader predicate-propagation analysis.

## Boolean condition forwarding

`mir::pass::negation` tests a boolean where it is computed rather than where lowering last stored
it. Folding a `not` leaves `comp_eq value false`, and a predicate reaching a branch commonly
travels through a local cell first, so a negated condition arrives as a comparison, a store, a cell
and a load in front of the `condbr` that wanted the original.

The pass walks a boolean back to the register that computes it, counting the negations on the way,
and rewrites the consumer to name that register: a `condbr` swaps its targets when the count is
odd, and a `comp_eq` against a boolean flips the literal it tests. It removes nothing itself — the
chain becomes unread, and the dead-representation cleanup shared with tail merging collects the
cell, its store, its load and any comparison left over. `if not a { .. }` falls from five
operations to two, and `if not (x < y) { .. }` loses the negation entirely: the branch tests the
ordering comparison with its arms swapped.

**Cost.** The pass is skipped outright unless the body contains a comparison — every negation is
one, so a body without one has nothing to forward, while a body with a branch would otherwise pay
for a definition map, a use census and a dominator tree to discover that. The census and the
dominator tree are built only on the first walk that reaches a cell, so a condition the branch can
already test directly asks for neither. Measured on std: 24 negations rewritten, optimized std MIR
from 15,322 to 15,245 operations, for +1.7% of MIR optimization instructions. The gating is most of
what makes that number small — running the analysis on every body cost +2.9%. The eleven runtime
workloads move within their own ±0.7% run-to-run spread, since none of them negates in a hot loop.

Two rules carry the proof. **A register is immutable**, so stepping from a comparison to its
scrutinee needs no reasoning about what happens in between. **A cell is not**, so a cell may be
stepped through only when it is a local `alloca` whose single write is one `store` of a register,
whose every other use is a direct read, and whose write dominates the read being resolved; any
other use, including a call argument or a terminator operand, disqualifies it entirely. A literal
flag is not this pass's shape but `branch_forward`'s, proved there against the arms that store it.

Every value the walk reaches is a boolean by construction — a walk starts at a `condbr` condition or
at a scrutinee compared against a boolean pattern — which is what makes flipping a comparison's
literal sound without asking a type question. The walk keeps the last *materialized* value it
passed, since a condition must be one; it therefore stops short of a negation whose operand is a
place, such as the `not` of a short-circuit `and`, which would need its own proof that the place is
unwritten between the two sites.

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

## Bounds-check elimination

`mir::pass::bounds_check` removes either checked shape left after the optimization rounds when
relational analysis proves the resolved offset lies in `0..len`. A post-inline
`array_resolve_index(index, len)` becomes a representation copy when that offset is exactly `index`,
or the ordinary `Num<int>::add(len, index)` call when a proved negative index resolves to
`len + index`. A whole `array_index(array, index)` that the inliner left generic or oversized is
retargeted to std's internal `array_offset_unchecked`; the negative case first reads the array length
and materializes that normalized offset. The out-place and generic instantiation are unchanged,
while the call-site effect row comes from the unchecked callee. If either checked call was an
`invoke`, its failure edge is unreachable and becomes a jump to the normal successor; the pass
removes stranded blocks and DCE collects dead panic storage and cleanup.

The proof is a forward value-version analysis over affine integer forms and predicates. Direct,
known standard-library calls supply their documented arithmetic, comparison, range and array-length
semantics. `BuildArray` defines its destination's `len` field as its literal operand count even when
the element values are unknown; a constant access or matching constant-bounded loop can therefore
use the local shape fact. A successful checked access refines its normal edge. For a whole signed
`array_index`, a non-negative source index can be used directly only when `0 <= index < len` is
proved. A negative source index instead requires the actual wrapped form `len + index` to be proved
in that range; the emitted addition is the same known std operation the affine analysis modeled.
A canonical range loop supplies a non-negative constant-start induction fact, and bounds are
attached to its yielded cursor only where the flow state also proves `start <= end`.
Place contents receive fresh symbols after writes and distinct incoming values receive join symbols,
so a predicate cannot silently survive mutation. Registers that name places are structural SSA
facts kept outside the flow state.

Only functions containing a relevant known call are admitted. Induction recognition locally
interprets a loop's construction block, then one reverse-postorder-prioritized fixed point computes
the proof; replay performs the rewrite. Refusing a proof retains the original check. The pass runs
after the final devirtualization because inlining may expose `array_resolve_index` and may leave a
whole `array_index`, and immediately before DCE because removing either error edge strands cleanup.

## Loop-invariant pure calls

`mir::pass::licm` moves an invariant direct call from a natural loop into its unique unconditional
preheader. The call must have an empty effect row, excluding source-level failure, reads and writes.
Motion into a path on which the source call might not execute additionally requires a proof that the
callee returns: purity alone does not make a call safe to move out of a zero-trip loop. This
termination proof is generic callee metadata rather than an arithmetic or function-name condition
owned by LICM.

`mir::pass::will_return` derives that metadata once from raw MIR and caches it with the module's
artifacts. Its initial proof is intentionally small: a script body is proved only when its reachable
CFG is acyclic and every operation it may invoke names another proved callee. Recursive components,
indirect calls and dynamically resumed or cloned code remain unknown; native functions are proved
by the host-function termination contract. A proof remains true across semantics-preserving MIR
rewrites. Optimization may make an unknown body newly provable, but retaining the conservative raw
answer merely declines an optimization and avoids invalidation inside the per-function pipeline.

The initial proof is deliberately conservative. Every visible argument must use the `Let`
convention, its place definition must dominate the preheader, and its storage root must not be
written anywhere in the loop. The call must use the value-result convention, have no owned
arguments, and write a concrete `TrivialCopy` value to a whole static local allocation. That result
allocation has no other writer and none of its uses may escape the loop. These conditions are
generic over all direct callees satisfying the effect contract; they are implementation limits that
can be relaxed independently if a concrete workload justifies it.

The existing call is relocated rather than copied, and a loop-local result allocation moves with
it, so the pass never grows MIR. Stack regions constrain the insertion point: the moved allocation
and call are placed before any outside-loop `stack_save` whose marker is restored in the loop. If
that marker predates the preheader, there is no safe point and the candidate is retained. This keeps
the result alive across every iteration.

Natural loops are recovered from dominance backedges and processed from inner to outer. After one
successful move the analysis is rebuilt, allowing the same computation to move through nested
preheaders without maintaining incrementally edited dominance state. An allocation-free
descending-edge scan rejects acyclic bodies before the call census allocates its operand views; the
census then rejects bodies with no eligible call before CFG or dominance construction.

## Dead code elimination

Deliberately narrow, and intra-function only.

- An unused result chain of concrete `int`, `float` or `bool` calls goes when the known-callee
  table explicitly classifies every call as total, deterministic and speculatable, and its inferred
  effects are empty. Another direct call may use the same worklist only when it names a
  module-table script body whose raw MIR proves it returns, has no hidden evidence inputs, and
  every authoritative visible input convention is `Let`; its concrete result must also be
  `TrivialCopy`. These restrictions exclude mutation through an argument and a managed result's
  ownership lifetime. Purity alone is insufficient: a pure user function may diverge, and
  removing its unused call would make a formerly non-terminating program return.
- An `alloca` goes only when *every* use of it is the destination of a pool-constant `store`,
  together with those stores. The wider cleanup, entered after tail merging or condition
  forwarding, also admits a register whose defining operation requires no consuming use. Constants are trivially copyable; the explicit result
  contract excludes variants and owning closure construction. Thus no owned register loses its
  consuming use — the trap a wider rule hits first. The extra producer census is paid only when one
  of those rewrites actually fired.
- An unread `dict_entry` or `subfield` goes. Both derive places without side effects or owned
  results, so deleting one discharges no obligation. A linear use-count worklist handles nested
  `subfield` chains: removing an unread leaf can make its base derivation unread.
- A `build_array` destination (or a bare function constant slot) used only by its cleanup is removed
  together with every matching drop. Treating construction and cleanup as one dead lifetime avoids
  both leaking a constructed resource and dropping uninitialized storage; arbitrary resource
  producers remain outside this deliberately narrow rule.
- A semantic `clone` destination used only by its matching cleanup is removed by the same complete
  lifetime rule. An exact local clone/drop pair within one block may also go when no operation can
  observe or retain an alias to that allocation, even if a later lifetime reuses the cell. This is
  justified by the `Value` law that cloning and then ending ownership of the unused clone has no
  observable language-level effect; it does not grant general pure-call DCE.
- A properly nested same-block `stack_save`/`stack_restore` pair with one restore goes when no
  surviving operation inside may leave current-frame storage allocated. The paired rule runs after
  the other removals, so storage cleanup can make a region empty first.

Constants left unreferenced are pruned from the pool, explicitly, since that renumbers every
`ConstantId`.

## Tail merging

`mir::pass::tail_merge` simplifies shared control-flow tails after ordinary DCE has removed dead
lowering scaffolding. Its main rule hash-conses complete alpha-equivalent basic blocks. Operation
kinds, operands from outside the block and exact successors must agree. Results defined within the
block are compared by definition order rather than by their function-wide `ValueId`, and source
spans do not participate. The representative's span remains, as when any other optimization keeps
one of two redundant computations.

The table owns only a 64-bit canonical fingerprint and a block id. A matching fingerprint is
collision-checked by a borrowed alpha comparison before any edge is redirected; operation metadata
and operand lists are never cloned into keys. One local-result scratch map is reused while
fingerprinting blocks, and the editable body is opened only after a duplicate, equal-target branch,
or foldable empty exit was found.

Blocks are visited backwards so already-equivalent forward successors share a representative in
their predecessors' keys; this merges multi-block acyclic tails without graph isomorphism or code
motion. Backedges remain conservative. Source-fallible `invoke` blocks are excluded because an
invoked result begins its valid scope only on the normal edge and would require subgraph-level
renaming. Unreachable blocks are excluded too: they have no useful dominance relationship with a
reachable candidate and therefore cannot safely serve as its representative.

Every edge to a duplicate is redirected to the representative. A `condbr` whose targets thereby
become equal becomes a `goto`, after which unreachable-block and single-predecessor cleanup remove
the duplicate structure.

Independently, an empty block holds nothing to execute, so its terminator folds into the edges
reaching it — without copying an operation, since there is none. How far that goes depends on the
terminator, and the asymmetry is the IR's, not a choice. A `goto` is folded into *every* predecessor
edge whatever its kind, because an edge names a block and forwarding only changes which one; chains
of them resolve in a single scan, with the block count bounding the walk so a cycle of empty jumps
is left alone. An operand-free terminal — `ret`, `propagate_error` or `failure_during_cleanup` — can
only replace a predecessor's own `goto`: a `condbr` or `invoke` edge must name a block and has
nowhere to put a terminal instead. That is why an `invoke`'s continuation survives as a block even
when it does nothing but return.

Merging a tail or collapsing a branch can make its predicate dead. Only in that case does the
driver run a small cleanup fixed point: unread `comp_eq`, `load`, and `extract_tag` results;
explicitly total/speculatable calls; and their local storage lifetimes. Folding only an empty exit
cannot make a value dead and does not buy that cleanup. Unchanged bodies pay neither the fixed point
nor a second storage-DCE scan.

## Redundant stack markers

A stack marker is the interpreter's allocation frontier at the point it was taken, and only an
`alloca` moves that frontier. `mir::pass::stack_region` runs over the settled body, after DCE has
emptied every bracket it can, and removes the two consequences: a `stack_save` taken where a live marker already holds the frontier
records the same value, so it is replaced by that marker; and a `stack_restore` to a frontier
already current reclaims nothing. Nesting is what creates them — inlining brackets every spliced
body, and a body spliced directly inside another's bracket takes its mark at the same frontier.

The analysis is a forward fixpoint over the set of markers known equal to the frontier, intersected
at joins, cleared by anything that may leave frame storage. It shares that predicate with `dce` so
the two cannot disagree about what grows a frame.

It runs *before* tail merging, and the order matters in one direction only: canonicalization
**creates** the alpha-equivalence tail merging looks for. Two mutually exclusive arms which restore
duplicate markers of the same frontier are the same block only once both name the surviving marker;
merging first compares them while they still differ by a register name and concludes, wrongly, that
they are distinct.

**A bracket that reclaims real storage is never removed**, and the distinction is not caution. Such
a bracket is where a live range ends, which is what a backend's stack-slot allocator needs to prove
two slots may share a frame offset — the same information LLVM carries as `lifetime.start` and
`lifetime.end`. Deleting one would buy two interpreter dispatches at the price of a larger native
frame, trading a real cost in the backend for a saving that exists only in the boxed interpreter.
What this pass removes is a *duplicate* mark and a restore that pops nothing, neither of which tells
a backend anything the surviving marker does not; peak cell use is unchanged.

## Dynamic profiling

`mir::profile` counts every operation and terminator executed by the MIR reference interpreter. It
provides totals, per-function counts and per-type counts where an operation carries a concrete type;
calls are split into direct and indirect dispatch. Instruction identities reuse the Strum-generated
discriminants of `OperationKind` and `TerminatorKind`, so the profiler does not maintain a second IR
enumeration.

`make profile-mir` compares raw and optimized MIR over the canonical runtime workloads without
Valgrind; `WORKLOADS="fibonacci sieve"` selects a subset. The native profiler and Gungraun share
workload compilation, inputs and typed result extraction through `benches/runtime_workloads.rs`.
Gungraun therefore continues to measure the same execution boundary. Each row includes its signed
delta and percentage change; a count introduced from a zero baseline is marked `new`. Peak cells is
a high-water mark within one run, while the corpus summary sums the workloads' paired peaks to make
their improvements additive; that sum is a comparison score, not simultaneous memory use.
When standard output is a terminal, decreases are green, increases red and unchanged values dimmed;
headings and totals are emphasized. Redirected output is always plain, and `NO_COLOR` disables color
explicitly.

The report orders instructions by broad cost shape — semantic/callee-dependent, size-dependent,
fixed storage, addressing/evidence, scalar/control, then interpreter scaffolding — but assigns no
weights. Native-call cost is callee-dependent and representation-copy cost is type-dependent, so a
single synthetic MIR score would assert backend costs the interpreter cannot establish.

## Budgets

All in `mir::pass::budget`. A budget change is a user-visible change: the optimization report cites
the inlining limits by name.

| budget | value | bounds |
|---|---:|---|
| `MAX_ROUNDS` | 4 | the driver's outer loop |
| `INLINE_CALLEE_OPERATIONS` | 32 | the largest callee inlining will copy |
| `INLINE_FUNCTION_GROWTH` | 128 | growth beyond the size a function had *before* optimization |
| `specialization_limit` | `max(512, 4 × declared MIR bodies)` | specializations per module, against the cascade |
| `owned_argument_variant_limit` | `max(256, 2 × stable source bodies)` | ownership-taking ABI variants per module |

Inlining budgets are per function; generated-variant budgets are per module to cap call-graph
cascades. The specialization population is measured before optimization; the owned-variant source
population is the declared bodies plus completed specializations entering that final pass. Neither
kind of generated output enlarges its own allowance. For each generated-variant budget, the fixed
number is a minimum total allowance and the scaled number replaces it once larger; the two are not
added together. Growth is measured against the pre-optimization size, or each round would grant it
afresh.

## The optimization report

`CompilerSession::optimization_report`, surfaced as `--optimization-report` in the REPL. It is
**almost entirely derived rather than instrumented**: on request the report re-classifies each
remaining call site with each pass's own predicate, so those answers cannot drift from what the
passes decide. A tiny artifact aggregate records rewrites such as removed bounds checks, because a
deleted operation cannot be reconstructed from final MIR.

It counts call sites before and after rather than "folds", which stopped being derivable once
inlining could duplicate calls.

Its blind spot is worth knowing: refusal reasons classify **call sites**. A dead `dict_entry`, a
redundant clone, a layout witness that substitution made unnecessary — none of these is a call site,
and every one of them was found by reading generated MIR instead. A pass needs an explicit aggregate
if its most useful result would otherwise disappear without a count.

## Invariants

- `verify_function` passes on raw lowering and generated optimizer inputs before another pass
  consumes them, then on every final declared and specialized optimized body after whole-module
  cleanup, under debug/test gating. Intermediate pass results never escape the optimizer. This is
  the primary safety net for every rewrite without repeating whole-function dataflow at every pass.
- **Block order is not a definition order.** A value may be defined in a higher-numbered block than
  its uses; the only requirement is dominance, which is a property of the CFG rather than of block
  numbering. `emit_mir` produces such bodies already — a `Case` whose scrutinee is itself
  source-fallible numbers its `invoke` successors above the alternative heads that read it. The
  verifier therefore resolves a `Pointee`/`Same` result role on demand from `value_definition`
  instead of assuming its walk has already reached the operand's definition.
- Optimization never changes a program's observable result or its source-failure behaviour. It may
  change fuel and call-depth consumption, which are sandbox policy rather than source semantics.
- **A rewrite must make progress.** A pass may not report having changed something when its rewrite
  reproduces its own input: the driver loops until nothing changes, so a self-reproducing rewrite
  spins to the round cap reporting progress the whole way.
- With optimization off, MIR is byte-identical to an unoptimized build.
- **Session-dependent values must not be frozen into MIR.** Variant tags remain symbolic in cached
  HIR/MIR and a backend resolves them through the session's `Ustr`/`u32` table. Folding an
  `extract_tag` result into an ordinary integer constant would bake one session's compact ID into
  portable IR.
