# HIR Ownership and Value Dispatch

This document records the ownership invariants that SSA lowering should rely on.
It describes HIR after type inference, borrow checking, and dictionary elaboration.
At that point all `LocalStorage::Deferred`, `LocalClone::Unknown`, `LocalDrop::Unknown`, and `TakeLocalValueMode::Unknown` placeholders must have been resolved.
All call-site `ArgPassing` metadata must also have been resolved.

See `doc/abi.md` for the physical calling convention.
This document is about source-level ownership semantics and the HIR operations that preserve them.

# Values, Places, and Locals

A HIR expression either produces an owned value or denotes a place in existing storage.
Place-like nodes include `LoadLocal`, projections (`Project`, `ProjectAt`, field projections before elaboration), and call nodes whose `FnType` has `FnReturnConvention::Place`.
SSA must not treat every `LoadLocal` as an owned read: ownership transfer, clone, and copy are explicit HIR operations.

When a place-producing projection or call needs a non-place base, HIR generation stores that base in an explicit owned temporary local first.
The consumer then uses a normal place rooted at that temporary, and ordinary `DropLocal` cleanup releases the temporary after the consumer.

Std-only functions marked with `#[place_result]` are place-like nodes.
The attribute also marks the function unsafe, so user source cannot call or bind it directly.
The attribute is a bootstrap spelling for `FnReturnConvention::Place`; after HIR construction the function type is the source of truth.
HIR consumers must handle `Apply`, `StaticApply`, and unelaborated `TraitMethodApply` calls with that convention like other place references when a place is required, or first materialize them with `CloneValue` when an owned value is required.
The returned place is an expression-local capability, not a storable reference value.
HIR must not store a raw place in a local, aggregate, closure capture, or normal value return.

`LocalDecl` is the ownership metadata for a local:

| Field | SSA-facing meaning |
|-------|--------------------|
| `slot` | Frame slot offset within the local value frame. Extra dictionary/evidence parameters use a separate index space. |
| `storage` | Whether this local is a non-owning alias, owns storage with lexical cleanup, or is temporarily deferred until final mutability facts are known. |
| `clone` | If present, `StoreLocal` initializes the local by either a trivial copy or `Value::clone(source, &mut uninit_target)`. |
| `assignment_mode` | `InitializeStorage` means assignment writes uninitialized storage and must not drop the previous destination. |

# Owned Materialization

When a context needs an owned value and the source is already an owned value, HIR can use that value directly.
When the source is a place, HIR must materialize ownership explicitly:

- Type not yet resolved after HIR construction: emit `CloneValue { source, clone: LocalClone::Unknown }`.
- Concrete `TrivialCopy` type after dictionary elaboration: resolve to `LocalClone::Resolved(TrivialCopy(layout))`.
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
- Assignment targets may consume projections and place-result calls directly as places, subject to the usual mutability checks.
- Projections and place-result calls of non-place bases use explicit owned temporaries when consumed as places; if an owned result is needed, that place is then wrapped in `CloneValue`.

# Drops and Cleanup

Lexical cleanup is represented by `Block.cleanup`, a list of locals in declaration order.
When a block is exited, cleanup runs in reverse order.
After local storage resolution, cleanup is a no-op for non-owning locals.
For owned locals it applies the resolved `LocalDrop`: `Skip` reclaims only storage, while static and dictionary modes call `Value::drop` before discarding storage.

Assignments to initialized storage carry an optional `Assignment::drop`.
If present, the old destination lifetime ends before the new value replaces it; the resolved mode may be `Skip`.
Assignments to uninitialized storage use `assignment_mode == InitializeStorage` and must not drop the destination first.

SSA must preserve the same cleanup behavior on all exits:

- Normal scope exit runs the block's cleanup.
- A moved local is not dropped again.
- Runtime-error edges must run semantic drops for initialized owned locals created in the exited scope, in reverse order, before storage is reclaimed.
- `return`, `break`, and `continue` edges run the cleanup for each lexical block they exit.
- A value carried by `return` or `break` is prepared before cleanup runs: a local owned by the exited scope is moved with `TakeLocalValue`, while a still-live place is materialized with `CloneValue` or a trivial copy.

Function-entry locals are not represented by an extra cleanup block today.
This is compatible with the current calling convention: non-trivial source-level value inputs are passed by reference, and owned function-boundary inputs are trivial-copy values whose cleanup is `Skip`.

# Clone and Drop Dispatch

Clone and drop dispatch are specialized by site.
Before dictionary elaboration, `Unknown` means the final type is needed to choose the implementation.

`LocalClone` resolves to one of:

- `TrivialCopy(ResolvedValueLayout)`, which copies the value representation without `Value::clone`.
- `Static(FunctionId)`, which calls a concrete generated or user-provided `Value::clone`.
- `Dictionary(ExtraParameterId)`, which loads `Value::clone` from a hidden dictionary parameter.

`LocalDrop` resolves to one of:

- `Skip`, which reclaims storage without semantic `Value::drop`.
- `Static(FunctionId)`, which calls a concrete generated or user-provided `Value::drop`.
- `Dictionary(ExtraParameterId)`, which loads `Value::drop` from a hidden dictionary parameter.

The `Value` method signatures are:

- `clone(source: T, target: &mut Uninit<T>)`
- `drop(target: &mut T)`

Both methods have an empty effect type.
In particular, semantic drop cleanup does not add source-level fallibility.
The clone target is allocated as `Uninit<T>` before the call and becomes initialized after `clone` returns.
Dropping `Uninit<T>` is a no-op, so first writes into clone out-parameters never drop prior garbage storage.

For `Dictionary(id)`, `id` indexes the function's extra dictionary/evidence parameter list.
The dictionary entry is selected with `VALUE_TRAIT.dictionary_method_index(...)`.
Extra dictionary/evidence parameters do not have matching `LocalDecl`s and do not affect source-level local slots.
SSA lowering may choose a physical ABI layout that packs evidence and values together, but that packing is not part of HIR ownership semantics.

Dispatch sites are:

- `StoreLocal` with `LocalDecl::clone`: clone into the local's uninitialized target storage.
- `CloneValue`: clone or copy a place into a fresh owned temporary result.
- `Block.cleanup` with `LocalDecl::drop`: drop an owned local at scope exit.
- `Assignment::drop`: drop the overwritten destination value.

# Call Argument Passing

HIR derives source-level argument passing from the callee ABI type:

- mutable parameters resolve the argument as a mutable place;
- generic by-value parameters are passed by shared reference, even when a concrete call site later solves them to a `TrivialCopy` type;
- by-value parameters that are concrete types that solve as `TrivialCopy` are copied by representation;
- other by-value parameters are passed by shared reference.

Call nodes store the resolved passing class (`MutableRef`, `SharedRef`, or `TrivialCopy`) so eval and SSA lowering do not have to rediscover callee ABI decisions after type inference has solved call-site types.
For HIR bodies, the same high-level passing class is stored on `ModuleFunction.parameter_passing` for visible callee parameters, in declaration order.
Native/interpreter-only bodies provide the same visible metadata explicitly; context-native helpers that also receive hidden runtime arguments keep those separate from visible parameter passing.
That metadata intentionally stores no cleanup and no layout payload.

The legality of `TrivialCopy` remains a trait-solver decision during HIR elaboration.
Concrete value layout is not persisted in HIR or `Module`; eval and SSA lowering compute it structurally from `Type` plus the owning module environment when a resolved `TrivialCopy` edge needs size/alignment.
`Value` associated consts remain the dictionary carrier for generic layout metadata, not the source of truth for concrete layouts.

Shared-reference calls should not hide temporary lifetimes in call metadata.
If a non-`TrivialCopy` by-value argument is not already a place, HIR generation materializes it into an owned `$arg` local and wraps the call in normal `Block.cleanup`.
This keeps the cleanup visible to eval and SSA lowering as ordinary HIR.

## High-level passing convention requirements vs. physical ABI

The high-level passing convention is derived at call construction/elaboration time and stored on call edges.
Native (a.k.a. physical) calling conventions must agree with the derived convention: mutable/shared-reference arguments are passed by pointer, while concrete `TrivialCopy` arguments may still need target-specific ABI lowering as specified by `doc/abi.md`.
For example, a `TrivialCopy` value larger than the native immediate argument size should be passed indirectly even though its language-level representation can be copied.

# Function Values

Function surface types do not create user-visible `Value` dictionary requirements.
Their `Value` implementation is compiler-provided and uses the closure payload metadata stored in the function value.

`FunctionClone` clones a function value's closure environment into already allocated target storage.
`FunctionDrop` drops the owned closure environment stored in a function value.
If a function value has no owned closure environment, these operations are no-ops.

For closures with captures, `BuildClosure` stores:

- hidden dictionary/evidence captures, which are not semantically dropped as `Value`s;
- owned value captures, already materialized by the rules above;
- a `captures_value_dictionary`, the `Value` dictionary for the tuple of owned captures.

SSA must make this closure environment visible as data.
Clone/drop for a function value must call the captured-environment dictionary, not host-language clone/drop.

# Trait Dictionaries and Layout Constants

Dictionary elaboration rewrites transient `GetTraitMethod`, `GetTraitAssociatedConst`, and `GetTraitDictionary` nodes into explicit dictionary/evidence nodes.
SSA should lower the elaborated form.

For concrete associated constants, elaboration emits an immediate.
For generic associated constants, elaboration emits `GetDictionaryAssociatedConst` from the hidden dictionary parameter.
`Value::SIZE` and `Value::ALIGN` are therefore available either as constants or as dictionary associated constants and are the source of typed storage sizes.

# Non-Contracts of the Boxed Interpreter

The current boxed interpreter still has helper paths such as boxed native `TrivialCopy` copying and interpreter-only `ValOrMut::Ref` call arguments for borrowing existing boxed storage.
These are interpreter implementation details, not language or SSA contracts.
SSA should lower `CloneValue` with `TrivialCopy` mode as a storage copy and lower clone/drop through the explicit dispatch described above.
