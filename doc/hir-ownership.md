# HIR Ownership and Value Dispatch

This document records the ownership invariants that SSA lowering should rely on.
It describes HIR after type inference, borrow checking, and dictionary elaboration.
At that point all `LocalClone::Unknown` and `LocalDrop::Unknown` placeholders must have been resolved.

See `doc/abi.md` for the physical calling convention.
This document is about source-level ownership semantics and the HIR operations that preserve them.

# Values, Places, and Locals

A HIR expression either produces an owned value or denotes a place in existing storage.
Place-like nodes include `EnvLoad`, projections (`Project`, `ProjectAt`, field projections before elaboration), and `Apply` / `StaticApply` nodes whose function definition has `returns_place`.
SSA must not treat every `EnvLoad` as an owned read: ownership transfer, clone, and copy are explicit HIR operations.

When a place-producing projection or call needs a non-place base, HIR generation stores that base in an explicit owned temporary local first.
The consumer then uses a normal place rooted at that temporary, and ordinary `EnvDrop` cleanup releases the temporary after the consumer.

Std-only functions marked with `#[place_result]` are place-like nodes.
The attribute also marks the function unsafe, so user source cannot call or bind it directly.
HIR consumers must handle `Apply` and `StaticApply` with `returns_place` like other place references when a place is required, or first materialize them with `CloneValue` when an owned value is required.

`LocalDecl` is the ownership metadata for a local:

| Field | SSA-facing meaning |
|-------|--------------------|
| `slot` | Frame slot offset within the local value frame. Extra dictionary/evidence parameters use a separate index space. |
| `owns_storage` | This local owns storage that may be moved from and whose storage must be reclaimed. Non-owning locals are aliases. |
| `clone` | If present, `EnvStore` initializes the local by either a trivial copy or `Value::clone(source, &mut target)`. |
| `drop` | If present, lexical release ends this local's owned lifetime; the resolved mode either skips semantic drop or calls `Value::drop`. |
| `assignment_mode` | `InitializeStorage` means assignment writes uninitialized storage and must not drop the previous destination. |

# Owned Materialization

When a context needs an owned value and the source is already an owned value, HIR can use that value directly.
When the source is a place, HIR must materialize ownership explicitly:

- Type not yet resolved after HIR construction: emit `CloneValue { source, clone: LocalClone::Unknown }`.
- Concrete `TrivialCopy` type after dictionary elaboration: resolve to `LocalClone::Resolved(TrivialCopy)`.
- Non-`TrivialCopy` value type after dictionary elaboration: resolve to a static or dictionary `Value::clone` dispatch.
- Owned local moved out of its lexical scope: emit `EnvMove { id }` and skip the matching lexical drop.

Generic types are not treated as `TrivialCopy` for this purpose, even if the function has a `T: TrivialCopy` constraint.
They use the generic `Value` dictionary path.

Current lowering applies these rules in the main ownership-sensitive contexts:

- `let mut` initialized from a place owns a snapshot, using `CloneValue` with either trivial-copy mode or `Value::clone` mode.
- A `let` initialized from a mutable place owns a snapshot; during HIR construction, unresolved place mutability is treated conservatively the same way.
- A `let` initialized from a known immutable place may be non-owning.
- Closure captures are materialized as owned values before `BuildClosure`.
- Function returns move an owned local with `EnvMove` when returning that local out of the current scope.
- Non-place arguments passed by shared-reference ABI are stored in owned temporaries; the call receives places to those temporaries and the temporaries are dropped after the call.
- Projections and place-result calls of non-place bases use explicit owned temporaries when consumed as places; if an owned result is needed, that place is then wrapped in `CloneValue`.

# Drops and Cleanup

Lexical drops are explicit `EnvDrop { id }` nodes generated in reverse local order.
Locals with owned storage whose lifetime ends receive `EnvDrop` nodes.
`EnvDrop` applies the resolved `LocalDrop`: `Skip` reclaims only storage, while static and dictionary modes call `Value::drop` before discarding storage.

Assignments to initialized storage carry an optional `Assignment::drop`.
If present, the old destination lifetime ends before the new value replaces it; the resolved mode may be `Skip`.
Assignments to uninitialized storage use `assignment_mode == InitializeStorage` and must not drop the destination first.

SSA must preserve the same cleanup behavior on all exits:

- Normal scope exit runs the generated `EnvDrop`s.
- A moved local is not dropped again.
- Runtime-error edges must run semantic drops for initialized owned locals created in the exited scope, in reverse order, before storage is reclaimed.
- Early return propagates the returned value and must not drop storage that has been moved into that return value.

# Clone and Drop Dispatch

Clone and drop dispatch are specialized by site.
Before dictionary elaboration, `Unknown` means the final type is needed to choose the implementation.

`LocalClone` resolves to one of:

- `TrivialCopy`, which copies the value representation without `Value::clone`.
- `Static(FunctionId)`, which calls a concrete generated or user-provided `Value::clone`.
- `Dictionary(ExtraParameterId)`, which loads `Value::clone` from a hidden dictionary parameter.

`LocalDrop` resolves to one of:

- `Skip`, which reclaims storage without semantic `Value::drop`.
- `Static(FunctionId)`, which calls a concrete generated or user-provided `Value::drop`.
- `Dictionary(ExtraParameterId)`, which loads `Value::drop` from a hidden dictionary parameter.

The `Value` method signatures are:

- `clone(source: T, target: &mut T)`
- `drop(target: &mut T)`

Both methods have an empty effect type.
In particular, semantic drop cleanup does not add source-level fallibility.
The clone target is allocated but uninitialized before the call and becomes initialized only if `clone` returns normally.

For `Dictionary(id)`, `id` indexes the function's extra dictionary/evidence parameter list.
The dictionary entry is selected with `VALUE_TRAIT.dictionary_method_index(...)`.
Extra dictionary/evidence parameters do not have matching `LocalDecl`s and do not affect source-level local slots.
SSA lowering may choose a physical ABI layout that packs evidence and values together, but that packing is not part of HIR ownership semantics.

Dispatch sites are:

- `EnvStore` with `LocalDecl::clone`: clone into the local's uninitialized target storage.
- `CloneValue`: clone or copy a place into a fresh owned temporary result.
- `EnvDrop` with `LocalDecl::drop`: drop an owned local.
- `Assignment::drop`: drop the overwritten destination value.

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

Dictionary elaboration rewrites transient `GetTraitMethod`, `GetTraitAssociatedConst`, and `GetTraitDictionary` nodes into ordinary dictionary values and projections.
SSA should lower the elaborated form.

For concrete associated constants, elaboration emits an immediate.
For generic associated constants, elaboration projects from the hidden dictionary parameter.
`Value::SIZE` and `Value::ALIGN` are therefore available either as constants or as dictionary projections and are the source of typed storage sizes.

# Non-Contracts of the Boxed Interpreter

The current boxed interpreter still has helper paths such as boxed native `TrivialCopy` copying and interpreter-only `ValOrMut::Ref` call arguments for borrowing existing boxed storage.
These are interpreter implementation details, not language or SSA contracts.
SSA should lower `CloneValue` with `TrivialCopy` mode as a storage copy and lower clone/drop through the explicit dispatch described above.
