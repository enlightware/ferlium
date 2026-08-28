# MIR structure and invariants

Ferlium MIR is a storage-explicit, executable ownership IR. It is the shared input intended for the
reference interpreter and future machine backends; it is not a physical target ABI.

Related documents:

- [abi.md](abi.md) defines representation and physical call lowering;
- [hir-ownership.md](hir-ownership.md) defines the source-level ownership semantics MIR preserves;
- [mir-uninit-tracking.md](mir-uninit-tracking.md) describes derived initialization/drop state;
- [mir-error-propagation.md](mir-error-propagation.md) describes source-error cleanup; and
- [runtime-sandboxing.md](runtime-sandboxing.md) distinguishes source failures from sandbox exits.

## Canonical function form

A finalized `mir::Function` contains parameters, a function-local typed constant pool, and basic
blocks. Every block has exactly:

```text
BasicBlock {
    operations: Vec<Operation>,
    terminator: Terminator,
}
```

Operations never carry intra-function successors. The terminators are:

- `goto`, `condbr`, and `switch_variant tag [Case => bN, ...] default bM`;
- `invoke <operation> -> bN error bM`, for a source-fallible operation;
- `yield place -> resume`, which suspends a scoped accessor;
- `return`;
- `propagate_error`, which returns the pending source failure; and
- `failure_during_cleanup`, which poisons execution after a second source failure.

The first block is the entry block. Every target is a `BlockId` in the same function. Missing
terminators and forward-declared block bodies exist only in the private `FunctionBuilder`; they
cannot occur in a finalized function. In debug builds, `FunctionBuilder::finish` runs the full MIR
verifier at this boundary.

**A `FunctionId` names a function in a context, and the context is `(module, artifact stage)`.** A
module's MIR bodies line up one-for-one with its HIR function table — except in the *optimized*
stage, which the optimizer may extend past the end with **specializations**: private copies of a
generic function with one call site's types substituted and its recursively static evidence bound
to constants, plus optimized-only ABI variants. The raw stage is always exactly the HIR table, which is also what lets the two stages be
told apart without a flag.

A specialization has no HIR entry, since nothing in the source declared it. Whether it is script or
native and its source return convention come from the function it was specialized from, through one
indirection. An ordinary monomorphization keeps that original's visible signature. A later
optimized-only variant may change selected parameters to ownership transfer, recorded directly in
its MIR body and call sites. Hidden evidence parameters need no HIR metadata either: binding
evidence replaces its uses, and the optimizer removes the now-dead parameters and call operands.
An owned-ABI variant of an evidence-parameterized generated thunk retains that live evidence.

## Values and roles

MIR uses independent, function-local `ValueId`s rather than operation locations:

- `%pN` is a parameter;
- `%rN` is an operation result;
- `@cN` is a concrete `TrivialCopy` constant representation;
- `bN` is a block target; and
- function, dictionary, subscript, and pattern operands remain symbolic.

Text dumps render function and subscript operands with their module-qualified names. Definition
annotations use `*T` for a pointer to `T`; function, variant, and first-class subscript pointees are
grouped to preserve the pointer boundary, for example `*((A) -> B)` and `*(Left A | Right B)`.

Moving an operation therefore does not renumber unrelated values. A derived def-use map locates the
operation that defines each `ValueId` when an analysis needs it.

The constant pool is also an input to *reification* — expressing a value computed at compile time
back as MIR (`src/mir/reify.rs`). Because `@cN` is pinned to a `TrivialCopy` representation, only a
trivially-copyable leaf, or a tuple or record of those, can be stored directly. An array whose
elements have such representations can instead be reified as `build_array<A> [@c0, ...] to %dest`:
the immutable elements remain constants and executing the operation allocates fresh mutable array
storage. A compile-time `string` similarly reifies constructively: its normalized contents enter the
pool as a `StaticStr`, and `string_from_static` creates a fresh owned string in the destination at
run time. The text is bounded by the optimizer's per-result reification budget. A list, variant,
closure, or array with non-`TrivialCopy` elements still has no reified form (including a
`TrivialCopy` variant), so its producing computation remains runtime code. Further resource types
need either a frozen-prototype representation plus an operation to clone it, or dedicated MIR that
rebuilds the value from constants the pool can hold.

A `ValueId` does not say which of these it is. An operand slot may accept more than one role —
`comp_eq` reads a place, a materialized Ferlium value, or an opaque tag — and keeping the operand
array uniform is what lets alpha-equivalence, hash-consing and operand substitution stay generic
across passes. The role is instead a property of the *defining* operation, derived by
`src/mir/role.rs`:

| Role | Meaning |
|---|---|
| place | Addressable storage, printed as `place T`. It is not a first-class pointer value. |
| materialized value | A value available without dereferencing a place. |
| variant tag | An opaque semantic tag identity, comparable only with symbolic variant-tag pattern data. |
| evidence | A dictionary, subscript, or variant-storage choice used for generic dispatch/layout. Compile-time evidence may recursively close a definition over other evidence. |
| stack marker | A saved allocation frontier consumed by `stack_restore`. |
| open projection | A yielded place plus the accessor contract whose slide must be ended exactly once. |

An owned result has exactly one consuming use on every returning path which executes its
definition. Mutually exclusive paths may consume it differently. A store transfers its obligation
to storage, whose initialization and drop obligations are tracked separately.

Almost every operation fixes its result's role by itself. `load` is the exception, reading its role
from its operand, so the derivation is a table rather than a function per operation. Lowering fills
that table as it appends; a finished body is re-derived on demand, since block order is not a
definition order.

Role checking, like the rest of verification (`src/mir/verify.rs`), is debug-and-test only. Lowering
checks each operand slot as the operation is inserted, naming the block and index while the emitting
frame is still on the stack. Each finished body is then checked as a whole at the artifact boundary,
which needs no `ModuleEnv`, no trait solving and no dataflow, so it runs before the heavier analyses
trip over the consequences; it also covers passes, which rewrite a block's operations directly.

Every register definition renders the role it takes: `place T` for addressable storage, `T` for a
materialized value, and `dict`, `subscript`, `fn`, `pattern`, `stack` or `open place T` for the rest.
`*T` is a materialized pointer value which address-consuming operations may dereference. This is what
distinguishes an `alloca` slot from an `alloca_place` one:

```
%r0: place *int = alloca_place int
%r1: *int = load %r0
```

Compile-time match patterns are not runtime constants. They may represent source literals such as
`string` whose runtime value is owned even though its HIR immediate representation is `StaticStr`.

Variant tags are not Ferlium integers. HIR cases branch directly on a variant value; MIR lowering
introduces `extract_tag` only at the storage/CFG boundary, yielding an opaque `tag` register. The
reference interpreter retains its symbolic name. A machine backend resolves that name to the
session-local 31-bit identity and masks the payload-storage bit when reading the ABI's raw `u32`
field. A tag can only be compared with symbolic variant patterns or consumed by `switch_variant`;
it cannot enter Ferlium storage, calls, boolean branches, or arithmetic.

Variant `Case` nodes lower directly to one `switch_variant`. Other literal matches remain
`comp_eq`/`condbr` chains.

## Function boundaries

Parameters appear in this order:

1. `@extra`: dictionaries and other hidden evidence;
2. `@arg`: runtime arguments tagged `let`, `&mut`, or optimized-MIR-only `owned`; and
3. `@ret`: the caller-provided result storage, present unconditionally in current MIR, including
   for `()` results.

All argument conventions are represented as places. `Let` is immutable non-escaping access,
`MutableRef` is exclusive mutable access, and `owned` transfers the pointee into a private callee
variant which must consume it on every exit. Lowering emits only the first two; the final
whole-module ownership pass introduces `owned` after proving the caller's last use.

`CallResultConvention` determines the result storage shape:

- `Value`: the callee initializes `*T` through `@ret`;
- `AddressorPlace`: the callee writes a caller-rooted `*T` through an `@ret` of shape `**T`; and
- `YieldedOnce`: `project` exposes a callee-rooted place until `end_project` resumes its slide.

Every `Call` and `Project` retains its instantiated `CallImplType`. It is the source of argument and
result types, the result convention, and source fallibility. Call-site types are boxed in
`OperationKind` so the variable-sized signature metadata does not inflate every operation.

Call operands are `[callee, hidden evidence..., visible places..., ret-out]`. Project operands omit
the trailing result place because the operation itself yields the scoped place. A dynamic callee is
read through the place of its function value, so calling a closure never moves its environment.

## Operations

The operation kind fixes operand arity, roles, and result shape. The main groups are:

| Group | Operations | Contract |
|---|---|---|
| storage | `alloca`, `alloca_place`, `runtime_alloc`, `runtime_dealloc`, `load`, `store`, `clear`, `memcpy`, `move` | Stack storage follows stack regions; runtime storage has an explicit lifetime. `store` never drops; `memcpy` requires a concrete `TrivialCopy` pointee; `move` leaves its source absent. |
| aggregates | `subfield`, `variant`, `extract_tag`, `build_array` | Aggregate construction and ownership remain field-addressable. Product `subfield` records its aggregate type and carries `Value` witnesses for direct inline members with open layouts. A variant operation first builds an uninitialized payload shell. Generic variant construction and payload-marked `subfield` operations carry the selected payload's `Value<B>` layout witness; projection reads inline/indirect classification from the stored tag. `extract_tag` yields an opaque semantic tag, not the raw ABI word. `build_array` initializes fresh canonical array storage from borrowed `TrivialCopy` elements. |
| evidence | `dict_entry`, `build_dictionary`, `subscript_member`, `build_subscript` | Evidence remains symbolic. Construction closes a definition over evidence operands; dictionary entries are closed function places. |
| calls/projections | `call`, `project`, `end_project` | Proven source-infallible forms are ordinary operations. Potentially source-fallible forms occur only inside `invoke`. |
| ownership | `clone`, `drop`, `build_closure`, `clone_closure_env`, `drop_closure_env` | Semantic ownership actions are explicit. `Value::clone` and `Value::drop` are source-infallible by contract. |
| matching | `comp_eq` | Compares a borrowed/materialized runtime value with compile-time pattern data. |
| stack/runtime | `stack_save`, `stack_restore`, `check_call_depth`, `check_fuel` | Stack markers describe allocation frontiers. Runtime guards are pinned operations whose sandbox violations leave the MIR CFG. |

**Copying and releasing come in a representation-level and a semantic form**, and both forms are
operations rather than one being a call:

| | representation | semantic |
|---|---|---|
| copy | `memcpy` | `clone <source> to <dest> via <callee>` |
| transfer / release | `move` | `drop <target> via <callee>` |

Lowering picks the representation form when the type is trivially copyable and the semantic form
otherwise. `clone` and `drop` each carry the type they act on, so a pass that changes what a type is
— substituting a concrete instantiation into a generic body — can re-ask whether the semantic form is
still needed without recovering the type from the dictionary behind the callee. Their callee follows
the same contract as a `call`'s: a constant function, or the place of a function value read by
reference. A `clone` initializes its destination and gives it the drop obligation the copy creates.

When devirtualization resolves a closed dictionary entry, `call`, `clone`, and `drop` name the
function directly and place its recursively static hidden evidence immediately after the callee.

`build_dictionary<Definition> [capture0, ...]` is pure, effect-free and idempotent. Its operands all
have the evidence role and follow the definition's canonical capture schema. A capture-free
dictionary remains a symbolic constant; an entirely static construction folds to recursive static
evidence.

`build_array<A> [e0, ...] to destination` representation-copies each borrowed element and
initializes `destination: [A]` with a fresh logical array of exactly that length. `A` must be
statically `TrivialCopy`; otherwise array literals retain their in-place lowering, which initializes
each backing slot without an implicit clone. The operation is specified over Ferlium's canonical
array type, not over its current `Buffer` implementation. The compiler-known array layout and the
interpreter tuple representation are pinned together by a contract test in `std::array_type`.

A `call` additionally carries optional metadata: **how it instantiated its callee**, when statically
known and generic: the type and effect arguments its quantifiers stand for, positionally. They are
carried down from HIR rather than recovered by matching the callee's generic signature against this
call's concrete one — see [generic-instantiation.md](generic-instantiation.md). The operand is absent
for an indirect call, for a non-generic callee, and at synthesized call sites where no generic
application substitution is available; a consumer treats absence as "not known", which costs an
optimization rather than correctness. Blanket-method forwarding thunks are not such a case: blanket matching
supplies their substitution, and their call records it.

The same optional metadata records which visible operands transfer ownership. Rendered calls prefix
those operands with `move`; the matching callee parameters render as `@arg owned`. The verifier
consumes each caller place on both normal and source-error edges and requires every owned parameter
to be absent at all callee exits.

`Operation::verify` checks kind-local arity. The function verifier additionally checks operand
roles, types where independently known, dominance, linear uses, source-failure flow, and storage
ownership. For a call that records an instantiation it also checks that substituting the callee's
declared signature by the recorded arguments reproduces the call's own type — the invariant that
keeps the two from drifting between the inference that records them and the passes that consume
them.

## Source failures and sandbox exits

A source-fallible operation is wrapped by `Invoke`, even if its error successor only contains
`propagate_error`. An invoked result exists only on the normal successor. `EndProject` derives
fallibility from its `OpenProjection` operand rather than duplicating the accessor type.

The verifier rejects both a fallible operation in a block body and an infallible `Invoke`. It also
tracks the implicit source-error payload through the explicit CFG: normal code may `return`, one
pending failure may `propagate_error`, and a second failure must reach `failure_during_cleanup`.
Normal and error control flow may not silently rejoin.

Sandbox violations are not source failures. Fuel, call-depth, and reference-interpreter
environment-cell limits bypass MIR successors, poison the executor, and enter native reclamation
without running more guest cleanup.

## Ownership verification boundary

The verifier derives recursive present/absent/drop state for identifiable local storage and follows
normal and error outcomes separately. `Project` creates an open-projection obligation on its normal
edge; `EndProject` consumes it when the slide starts on both outcomes. `return` and
`propagate_error` require all exact local obligations to be discharged. Poisoning exits may transfer
remaining storage to runtime reclamation.

Generic descriptor equalities proved by HIR inference are not yet retained as standalone MIR
witnesses. The verifier therefore checks call/storage representations whenever both sides are
independently concrete, while witnessed generic moves and calls retain that inference boundary. A
serialized standalone MIR format will need explicit normalized-layout/equality metadata to close it.

## Physical MIR stage

> Status: canonical compact inline-product byte-address lowering is implemented; indirect product
> ownership, the remaining representations, and the unboxed interpreter are planned.

Physical lowering consumes the complete optimized `MirArtifacts`, including declared bodies and
retained specializations. It resolves physical addresses, representations, callable environments,
and native ABI entries while preserving the semantic CFG, failure flow, ownership operations,
types, and constants where their representation does not require expansion.

The result need not correspond one-to-one with semantic function artifacts. Lowering may introduce
adapters and helpers, merge physically equivalent artifacts, or remove unreachable internal
artifacts. It maintains a resolution from every retained semantic callable and specialization to
its physical entry and convention, and rewrites calls consistently. Top-level module entries retain
their externally visible identity. Generated helpers are ordinary entries in the physical artifact.

The lowerer builds a physical function table. The readiness verifier checks it and returns
`BackendReadyMirArtifacts`. Both stages use the same MIR structures without a phase parameter.

Backend-ready MIR may retain symbolic operands, `DictEntry`, variant construction, and
`extract_tag`. Each executor supplies their target representation. Interpreter-only native calls
and target-lowered value representations must be resolved.

### Physical call results

Semantic MIR gives every call a result place, including calls returning `()`. Physical lowering
assigns a result convention to each lowered function artifact after specialization. A direct
artifact returning exactly canonical unit may use `NoValue`, omitting both its `@ret` parameter and
the corresponding call operand. Other zero-sized and named types retain a value result. A shared
generic artifact retains `Value`; a specialization whose concrete result is `()` may independently
use `NoValue`.

The convention belongs to the artifact rather than an individual call site, and every direct call
must match it. First-class callables always expose `Value`. When a `NoValue` implementation is used
first-class, physical lowering supplies an adapter entry that invokes it and produces the logical
unit result.

### Runtime allocation

Physical MIR exposes the compiled runtime boundary directly:

```text
runtime_alloc<A>(byte_size: int, align: int) -> *A
runtime_dealloc(address: *A)
```

The result is a materialized pointer value; the pointee type describes the storage reached through
it, while the explicit byte size gives the allocation its extent. An array of `A` therefore also
receives `*A`. Allocation is fresh, uninitialized and owned until transferred or deallocated.
Deallocation accepts the materialized allocation pointer, and a zero-byte allocation remains valid
and reclaimable. Both operations are pinned.

### Typed byte addressing

Physical MIR adds two representation-level address operations:

```text
address_offset<A>(base_address, byte_offset: int) -> place A
address_offset_place<A>(base_address, byte_offset: int) -> place *A
```

The base is address-bearing and the offset is a materialized Ferlium `int`. `address_offset` yields
an aligned inline place of `A`; `address_offset_place` yields a slot containing an indirect place of
`A`, which `load` dereferences. Both retain the base allocation's provenance. Byte-offset
expressions use ordinary calls such as `Num<int>::add` and `Num<int>::mul`.

Semantic MIR retains logical `subfield` operations through its ordinary optimization rounds. A
product projection names the aggregate and carries the direct member `Value` witnesses required
when its physical offset is still open. Physical lowering replaces inline projections with an
ABI-derived offset and `address_offset`, emitting a closed addressor helper over those witnesses
when needed. Owning indirect members retain their logical projection until their lifecycle is
expanded, so the readiness verifier rejects such a projection until that pass is implemented.
Remaining borrows can then use `address_offset_place` and `load`. Buffer call expansion uses the
loaded backing pointer and element-size evidence.

### First-class subscript environments

`BuildSubscript` creates an owned environment. Planned `CloneSubscriptEnv` and
`DropSubscriptEnv` operations clone and release it; moving transfers it. The ABI defines the
descriptor, environment layout, and clone/drop dispatch.

`SubscriptMember` produces a physical-stage-only `BorrowedCallable`: the selected `ref` or `mut`
entry and a borrow of the original subscript environment. The verifier accepts it only as the
callee of `Call` or `Project`. `Call` holds the borrow for one invocation; `Project` holds it until
the matching `EndProject`.

The callable type determines its visible ABI. The descriptor-specific entry determines its
environment schema. Invocation borrows stored evidence and clones source-value captures into the
temporary required by Ferlium's stateless callable semantics.

### Known and target-native calls

Calls recognized by shared physical lowering remain ordinary calls throughout semantic MIR and its
optimization rounds. The lowerer resolves their exact function identities through a session table,
as existing MIR passes do with `KnownCallees`. Other native calls retain their `FunctionId` and use
the matching Rust `export ferlium` entry. Backend-readiness verification requires every native call
to have been lowered or have a compatible entry for the selected target.
