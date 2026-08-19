# HIR Ownership and Value Dispatch

This document records the ownership invariants that MIR lowering should rely on.
It describes final HIR after type inference, dictionary and ownership elaboration, and final borrow and lifetime validation.
At that point all `LocalStorage::Deferred`, `PendingLocalClone::Unknown`,
`PendingLocalDrop::Unknown`, and `PendingTakeLocalValueMode::Unknown` placeholders have been
resolved, and every call site and function parameter has a concrete `ArgConvention`.

See `doc/abi.md` for the physical calling convention.
This document is about source-level ownership semantics and the HIR operations that preserve them.

## Values, Places, and Locals

A HIR expression either produces an owned value, denotes a caller-rooted place in existing storage, or drives a scoped yielded place.
Caller-rooted place-like nodes include `LoadLocal`, direct projections (`Project`), and call nodes whose selected implementation has `CallResultConvention::ADDRESSOR_PLACE`.
MIR does not treat every `LoadLocal` as an owned read: ownership transfer, clone, and copy are explicit HIR operations.

When a place-producing projection or call needs a non-place base, HIR generation stores that base in an explicit owned temporary local first.
The consumer then uses a normal place rooted at that temporary, and the surrounding `Block.cleanup` releases the temporary after the consumer.

Addressor-place call nodes are place-like nodes.
Native addressors are registered as subscript members when they model projection, and source subscript members without `yield` infer `SubscriptResultConvention::AddressorPlace` from their body shape.
After HIR construction the selected call metadata is the source of truth: consumers handle any call node with `AddressorPlace` like a place when a place is required, or materialize it with `CloneValue` when an owned value is required.
The returned place is an expression-local capability, not a storable reference value.
HIR must not store a raw place in a local, aggregate, closure capture, or normal value return.

### Subscripts and Projection Evidence

A subscript bundle is a `SubscriptType`, not a `FnType`.
Each selected `ref` or `mut` member is emitted as a member function, and the member definition plus selected HIR call metadata carry the wrapper call result convention.
`SubscriptApply` selects a member at the use site and carries that selected call metadata.

First-class subscript values carry the bundle identity and can carry hidden evidence for constrained generic use.
Generic projection evidence is passed as a real `SubscriptValue`.
Explicit projection subscripts can satisfy that evidence directly; for structural fields, the compiler generates internal addressor subscripts when evidence is needed.
Generated structural projection values currently do not need captured hidden evidence themselves.

Unelaborated generic `FieldAccess` records whether the use needs the `ref` or `mut` member.
Elaboration either lowers a still-generic receiver through subscript evidence, or collapses a receiver that has resolved concrete back to the direct field/addressor path.
When a first-class subscript is used through an inferred abstract capability, the selected HIR call uses the yielded interface; a concrete addressor-place member may still be adapted by the runtime driver with no epilogue.

Subscript members split by body shape.
A member that contains `yield` uses `SubscriptResultConvention::YieldedOnce`, exposed on selected HIR calls as `CallResultConvention::YIELDED_ONCE`.
The yielded place is valid only while the accessor frame is suspended, so HIR must consume the call through `WithYielded { accessor, binding, body }`.
`WithYielded` runs the accessor to its single `Yield(place)`, binds that place to an internal non-owning `binding`, evaluates `body`, then resumes the accessor epilogue.
The binding is not source-visible storage and must not be captured, returned, or stored as a value.
If `body` exits by return, break, continue, or source failure, the accessor epilogue and normal frame cleanup are attempted before the transfer continues.
If an epilogue or cleanup action raises a second source failure while another source failure is already propagating, execution is poisoned by `FailureDuringCleanup` and no further Ferlium cleanup runs.
A sandbox violation always poisons immediately and bypasses cleanup.
If the accessor fails before yielding, no yielded binding exists and no post-yield epilogue runs.
See [mir-error-propagation.md](mir-error-propagation.md) for the MIR cleanup CFG and
[runtime-sandboxing.md](runtime-sandboxing.md) for executor poisoning.

A member without `yield` uses `SubscriptResultConvention::AddressorPlace`, exposed on selected HIR calls as `CallResultConvention::ADDRESSOR_PLACE`, and keeps caller-rooted projection behavior.
Its place-producing base argument uses `Let` (or `MutableRef`) access, so the returned place remains rooted in caller storage rather than a short-lived copied argument.
When a subscript use must evaluate an addressor projection exactly once, HIR uses `WithPlace { place, binding, body }`.
`WithPlace` evaluates `place` as a caller-rooted place, binds it to an internal non-owning `binding`, and evaluates `body`.
It does not suspend an accessor and has no epilogue.
Std `array_index` is a source subscript with `AddressorPlace` provenance, backed by the private native `buffer_slot` subscript; source array-index syntax resolves `array_index` and lowers through the addressor path.

`LocalDecl` is the ownership metadata for a local:

| Field | MIR-facing meaning |
|-------|--------------------|
| `slot` | Frame slot offset within the local value frame. Extra dictionary/evidence parameters use a separate index space. |
| `storage` | Whether this local is a non-owning alias, owns storage with lexical cleanup, or is temporarily deferred until final mutability facts are known. |
| `clone` | If present, `StoreLocal` initializes the local by either a trivial copy or the returned result of `Value::clone(source)`. |
| `assignment_mode` | `InitializeStorage` means assignment writes uninitialized storage and must not drop the previous destination. |

## Owned Materialization

Every final-HIR `Immediate` contains immutable constant data with a concrete `TrivialCopy` representation, so it never owns a resource requiring semantic clone or drop.
A managed source literal is materialized explicitly: for example, a string literal is a `StaticStr` immediate passed to the private `string_from_static` constructor, which produces an owned `string`.
Aggregate construction materializes managed literal leaves before assembling the runtime tuple, record, variant, or array.

Literal patterns use the same immutable representation data but compare it asymmetrically with runtime values.
In particular, `StaticStr` pattern data is compared directly with an owned runtime string; runtime text is never interned to perform a match.
Final-HIR validation checks immediate representation types and statically known pattern shapes.

When a context needs an owned value and the source is already an owned value, HIR can use that value directly.
When the source is a place, HIR must materialize ownership explicitly:

- Type not yet resolved after HIR construction: emit
  `CloneValue { source, clone: PendingLocalClone::Unknown }`.
- Concrete `TrivialCopy` type after dictionary elaboration: resolve to
  `ResolvedLocalClone::TrivialCopy`.
- Non-`TrivialCopy` value type after dictionary elaboration: resolve to a static or dictionary `Value::clone` dispatch.
- Local consumed as an owned result: emit `TakeLocalValue { id, mode }` and skip the matching lexical drop if it resolves to `MoveOwned`.
- If local ownership is not known yet, emit `TakeLocalValue { id, mode: Unknown }`, then resolve it to either a move or clone/copy after local storage is known.

Generic types are not treated as `TrivialCopy` for this purpose, even if the function has a `T: TrivialCopy` constraint.
They use the generic `Value` dictionary path.

Current lowering applies these rules in the main ownership-sensitive contexts:

- `let mut` initialized from a place owns a snapshot, using either trivial-copy mode or `Value::clone` mode.
- A `let` initialized from a mutable place owns a snapshot.
- A `let` initialized from a place whose mutability is not yet resolved records deferred local storage; after inference it resolves to either an owned snapshot or a non-owning alias.
- A `let` initialized from a known immutable place may be non-owning.
- Closure captures are materialized as owned values before `BuildClosure`.
- Function returns use `TakeLocalValue` when returning a local out of the current scope.
- Function calls use the explicit argument passing rules described below.
- Assignment targets may consume projections and addressor-place calls directly as places, subject to the usual mutability checks.
- Projections and addressor-place calls of non-place bases use explicit owned temporaries when consumed as places; if an owned result is needed, that place is then wrapped in `CloneValue`.
- Subscript reads, assignments, and compound assignments use one projection driver: `WithYielded` for scoped members and `WithPlace` for addressor members.
  Compound assignment reads and writes the internal binding inside that single projection instead of duplicating the accessor.

## Drops and Cleanup

Lexical cleanup is represented by `Block.cleanup`, a list of locals in declaration order.
When a block is exited, cleanup runs in reverse order.
After local storage resolution, cleanup is a no-op for non-owning locals.
For owned locals it applies the resolved `LocalDrop`: `Skip` reclaims only storage, while static and dictionary modes call `Value::drop` before discarding storage.
Once a semantic-drop action starts, the target lifetime has ended even if a sandbox violation stops execution before or during the drop body; the target is invalidated and must not be observed or retried.

Assignments to initialized storage carry an optional `Assignment::drop`.
If present, the old destination lifetime ends before the new value replaces it; the resolved mode may be `Skip`.
Assignments to uninitialized storage use `assignment_mode == InitializeStorage` and must not drop the destination first.

Final-HIR evaluation and lowering must preserve this cleanup behavior on all exits:

- Normal scope exit runs the block's cleanup.
- A moved local is not dropped again.
- Source-failure edges attempt semantic drops for initialized owned locals created in the exited scope, in reverse order, before storage is reclaimed.
  `Value::drop` is source-infallible by contract.
- Accessor slides follow the source-failure and poisoning rules described under `WithYielded` above.
- `return`, `break`, and `continue` edges run the cleanup for each lexical block they exit.
- A value carried by `return` or `break` is prepared before cleanup runs: a local owned by the exited scope is moved with `TakeLocalValue`, while a still-live place is materialized with `CloneValue` or a trivial copy.
- If a transfer exits a `WithYielded` body, the suspended accessor epilogue runs before the transfer continues past the `WithYielded`.
  `WithPlace` has no epilogue; ordinary enclosing `Block.cleanup` still applies.

Function-entry locals are not represented by an extra cleanup block today.
They are non-owning views governed by the parameter's `ArgConvention`; the caller remains responsible for the argument's ownership and cleanup.
Direct scalar transport does not give the callee a semantic cleanup obligation.

## Block Sequencing

Blocks evaluate every node in `Block.body` in order.
Only the tail node is the block's value, but non-tail nodes are still semantic evaluation steps and must not be skipped by HIR consumers.
Inside a yielded-once accessor body, `Yield(place)` has type `never` because it suspends the accessor until the caller-side `WithYielded` driver resumes the epilogue.
HIR construction enforces a single reachable, block-structured yield for such bodies; consumers may rely on that invariant.

HIR generation makes discard cleanup explicit for non-tail values that need semantic `Value::drop`.
In that case, the generation stores the discarded value in a generated owned local, wraps that store in a block, and records the local in that wrapper's `Block.cleanup`.
MIR lowering treats these wrappers like ordinary blocks: it lowers their body, runs their cleanup on every exit, and ignores their unit result as the enclosing block's non-tail value.
For any non-tail node, MIR lowering preserves evaluation order and effects, ignores the produced value as the enclosing block value, and preserves any nested or enclosing `Block.cleanup` obligations.

## Clone and Drop Dispatch

Clone and drop dispatch are specialized by site.
Before dictionary elaboration, `Unknown` means the final type is needed to choose the implementation.

`LocalClone` resolves to one of:

- `TrivialCopy`, which copies a concrete value representation without `Value::clone`.
- `Static(FunctionId)`, which calls a concrete generated or user-provided `Value::clone`.
- `Dictionary(ExtraParameterId)`, which loads `Value::clone` from a hidden dictionary parameter.

`LocalDrop` resolves to one of:

- `Skip`, which reclaims storage without semantic `Value::drop`.
- `Static(FunctionId)`, which calls a concrete generated or user-provided `Value::drop`.
- `Dictionary(ExtraParameterId)`, which loads `Value::drop` from a hidden dictionary parameter.

The `Value` method signatures are:

- `clone(source: T) -> T`
- `drop(target: &mut T)`

Both methods have an empty effect type.
In particular, semantic drop cleanup does not add source-level fallibility.
`clone` semantically produces a fresh owned value. MIR lowering may still use the
normal caller-allocated return convention to write that result directly into its
final destination slot.

The defining module supplies the compiler-generated `Value` implementation for a named type. When
the type and `Value` are publicly nameable, that implementation is selectable by other modules;
its generated method bodies remain private to the defining module. Consequently a public type with
a private representation shares one canonical ownership implementation without exposing that
representation or permitting a consumer to define a competing implementation.
Generated clone and drop bodies use the same concrete `TrivialCopy` predicate as ordinary ownership
elaboration: a qualifying value is cloned by copying its whole representation and needs no semantic
drop, while generic or managed structure retains member-wise `Value` dispatch.

For `Dictionary(id)`, `id` indexes the function's extra dictionary/evidence parameter list.
The dictionary entry is selected with `VALUE_TRAIT.dictionary_method_index(...)`.
Extra dictionary/evidence parameters do not have matching `LocalDecl`s and do not affect source-level local slots.
MIR lowering may choose a physical ABI layout that packs evidence and values together, but that packing is not part of HIR ownership semantics.

Dispatch sites are:

- `StoreLocal` with `LocalDecl::clone`: clone, then store the returned value into the local's storage.
- `CloneValue`: clone or copy a place into a fresh owned temporary result.
- `Block.cleanup` with `LocalDecl::drop`: drop an owned local at scope exit.
- `Assignment::drop`: drop the overwritten destination value.

## Call Argument Passing

HIR derives one of two source-level argument conventions from the callee type:

- `T` parameters use `Let`, giving immutable, non-escaping access for the duration of the call;
- `&mut T` parameters use `MutableRef`, giving exclusive mutable access to a place for the duration of the call.

Call nodes store this `ArgConvention` so eval and MIR lowering preserve the same access semantics without rediscovering them from incidental representation details.
For HIR bodies, the same convention is stored on `ModuleFunction.parameter_passing` for visible callee parameters, in declaration order.
Native/interpreter-only bodies provide the same visible metadata explicitly; context-native helpers that also receive hidden runtime arguments keep those separate from visible parameter passing.
That metadata intentionally stores no cleanup and no layout payload.

`Let` does not by itself require a clone.
The callee cannot mutate or retain the argument, and elaboration already inserts the normal ownership operations if the body later needs an owned value.
However, if a `Let` argument path overlaps a `MutableRef` argument path in the same call, or evaluation of a later argument writes an overlapping path, elaboration inserts a `CloneValue` snapshot at the `Let` argument's evaluation point.
The clone dispatch records representation copy, static semantic clone, or dictionary clone. A managed snapshot is stored in an explicit owned local that the enclosing call block cleans after the call; a `TrivialCopy` snapshot remains a direct HIR value and needs no cleanup.
The argument-position store preserves left-to-right evaluation: a later mutable argument cannot change the earlier observed value before the callee reads it, while managed snapshot cleanup stays visible to every backend.
Two overlapping `Let` arguments may share; overlapping mutable arguments are rejected by the borrow checker.

The legality of `ResolvedLocalClone::TrivialCopy` remains a trait-solver decision during HIR elaboration and is independent of size.
Concrete value layout is not persisted in call metadata or `Module`; eval and later lowering compute it structurally from `Type` plus the owning module environment when implementing a representation copy.

`Let` calls should not hide temporary lifetimes in call metadata.
If a non-`TrivialCopy` `Let` argument is not already a place, HIR generation materializes it into an owned `$arg` local and wraps the call in normal `Block.cleanup`.
This keeps the cleanup visible to eval and MIR lowering as ordinary HIR.

Addressor-place calls use `Let` or `MutableRef` for their caller-rooted base.
The returned place therefore cannot accidentally point into a consumed argument value whose lifetime ends with the call.

### Function Callee Lifetime

A first-class function expression is evaluated before its arguments. A direct local, projection,
index, or addressor-place access chain remains a place and `FunctionApply` reads the function value
through that place without consuming or cloning it. If evaluating or passing a later argument may
write an overlapping path, elaboration snapshots the function value into an owned
`$function_snapshot` local at the function expression's evaluation point; argument temporaries are
created afterwards and therefore clean up before that snapshot.

A `YieldedOnce` access chain cannot let its yielded place escape the suspended accessor. When such
a chain is used as a callee, HIR materializes the function value inside the yielded body, resumes the
accessor through its epilogue, and only then evaluates the call arguments. An `AddressorPlace` chain
has no suspended frame and remains a borrowed place through the call.

### Semantic and Physical Argument Passing

The semantic convention is derived at call construction/elaboration time and stored on call edges.
Target-specific ABI lowering later chooses physical transport.
`MutableRef` lowers to exclusive mutable access to caller storage.
`Let` may lower to a direct scalar or shared indirect access.
When overlap analysis inserted a snapshot, an indirect `Let` must point to that snapshot rather than the original mutable place.

## Function Values

Function surface types do not create user-visible `Value` dictionary requirements.
Their `Value` implementation is compiler-provided and uses the closure payload metadata stored in the function value.

`FunctionClone` returns a function value with a cloned closure environment.
`FunctionDrop` drops the owned closure environment stored in a function value.
If a function value has no owned closure environment, these operations are no-ops.

For closures with captures, `BuildClosure` stores:

- hidden dictionary/evidence captures, which are not semantically dropped as `Value`s;
- owned value captures, already materialized by the rules above;
- a `captures_value_dictionary`, the `Value` dictionary for the tuple of owned captures.

MIR makes this closure environment visible as data.
Clone/drop for a function value must call the captured-environment dictionary, not host-language clone/drop.

## Trait Dictionaries and Associated Constants

Dictionary elaboration rewrites transient `GetTraitMethod`, `GetTraitAssociatedConst`, and `GetTraitDictionary` nodes into explicit dictionary/evidence nodes.
MIR lowers the elaborated form.

Every runtime dictionary entry is a function: trait methods occupy the first entries, followed by associated constants as zero-argument getter functions.
The getter owns literal materialization, so each access to a managed associated constant produces a fresh owned value.

For a concrete associated constant, elaboration emits a static zero-argument call to the selected getter; for a generic associated constant, it emits a zero-argument `CallDictionaryFunction` through the hidden dictionary parameter.
Compiler-owned `Value::SIZE` and `Value::ALIGN` metadata may still be inspected directly while computing concrete layouts.
At runtime their getters carry generic layout metadata like any other associated constant, but they are not the source of truth for concrete layouts.

## Non-Contracts of the Boxed Interpreter

The current boxed interpreter still has helper paths such as boxed native `TrivialCopy` copying and interpreter-only `ValOrMut::Ref` call arguments for borrowing existing boxed storage. It also physically over-boxes variant payloads, while each `Value::Variant` separately records whether the canonical payload representation is inline or indirect; representation-copying a trivial variant preserves that mode but allocates a fresh interpreter box, and raw interpreter-storage reclamation remains separate from semantic `Value::drop`.
These are interpreter implementation details, not language or MIR contracts.
MIR lowers `CloneValue` with `TrivialCopy` mode as a storage copy and lowers clone/drop through the explicit dispatch described above.
