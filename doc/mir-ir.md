# MIR structure and invariants

Ferlium MIR is a storage-explicit, executable ownership IR. It is the shared input intended for the
reference interpreter and future machine backends; it is not a physical target ABI. This document
defines its structure, operation semantics, and validity requirements, not compiler implementation
mechanics.

Related documents:

- [abi.md](abi.md) defines representation and physical call lowering;
- [hir-ownership.md](hir-ownership.md) defines the source-level ownership semantics MIR preserves;
- [mir-optimization.md](mir-optimization.md) describes optimization passes and compile-time evaluation;
- [mir-uninit-tracking.md](mir-uninit-tracking.md) describes derived initialization/drop state;
- [mir-error-propagation.md](mir-error-propagation.md) describes source-error cleanup; and
- [runtime-sandboxing.md](runtime-sandboxing.md) distinguishes source failures from sandbox exits.

## Canonical function form

A finalized function contains parameters, a function-local typed constant pool, and basic blocks.
Every block contains an ordered sequence of operations followed by exactly one terminator.

Operations never carry intra-function successors. The terminators are:

- `goto`, `condbr`, and `switch_variant tag [Case => bN, ...] default bM`;
- `invoke <operation> -> bN error bM`, for a source-fallible operation;
- `yield place -> resume`, which suspends a scoped accessor;
- `return`;
- `propagate_error`, which returns the pending source failure;
- `failure_during_cleanup`, which poisons execution after a second source failure; and
- `invariant_failure "message"`, which fatally terminates execution on a compiler/runtime bug.

`invariant_failure` requires a fatal trap, not an unchecked unreachability assumption. It has no
continuation and does not use source-failure cleanup or poisoning.

The first block is the entry block. Every target is a `BlockId` in the same function. A finalized
function has no missing terminators or unresolved block bodies.

A `FunctionId` identifies a function within `(module, artifact stage)`. Raw semantic entries
correspond to the module's HIR functions. Optimized artifacts may additionally contain private
specializations and ownership-transfer variants without HIR entries.

A specialization records its original function and concrete type/evidence bindings. It inherits
the original's script/native classification and source result convention. An ownership-transfer
variant records its changed parameter conventions in its MIR body and every call site. Any hidden
evidence not fixed by specialization remains part of the callable's interface.

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

Moving an operation does not change unrelated value identities.

The constant pool holds concrete `TrivialCopy` leaves and tuples or records of those. Owned runtime
values require construction rather than shared mutable constant storage. For example,
`build_array<A> [@c0, ...] to %dest` creates fresh array storage from constant elements. Compile-time
evaluation must preserve these ownership rules when expressing its results as MIR.

A `ValueId` does not encode its role; the defining operation determines it. An operand slot may
accept more than one role: for example, `comp_eq` reads a place, a materialized value, or an opaque
tag.

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

Almost every operation fixes its result's role by itself. `load` instead derives its result role
from the storage it reads. Every operand must have a role accepted by its operation, and every
definition must dominate its uses.

Every register definition renders the role it takes: `place T` for addressable storage, `T` for a
materialized value, and `dict`, `subscript`, `fn`, `pattern`, `stack` or `open place T` for the rest.
`*T` is a materialized pointer value which address-consuming operations may dereference. This is what
distinguishes an `alloca` slot from an `alloca_place` one:

```
%r0: place *int = alloca_place int
%r1: *int = load %r0
```

Compile-time match patterns are not runtime constants. They may describe values, such as strings,
whose runtime representation requires owned storage.

Variant tags are not Ferlium integers. `extract_tag` yields an opaque, symbolic `tag` value; its
physical encoding is specified in [abi.md](abi.md#tag-representation). A tag can only be compared
with symbolic variant patterns or consumed by `switch_variant`; it cannot enter Ferlium storage,
calls, boolean branches, or arithmetic. Variant matches use `switch_variant`; other literal
matches use `comp_eq` and conditional branches.

## Function boundaries

Parameters appear in this order:

1. `@extra`: dictionaries and other hidden evidence;
2. `@arg`: runtime arguments tagged `let`, `&mut`, or optimized-MIR-only `owned`; and
3. `@ret`: the caller-provided result storage, present unconditionally in semantic MIR, including
   for `()` results.

All argument conventions are represented as places. `Let` is immutable non-escaping access,
`MutableRef` is exclusive mutable access, and `owned` transfers the pointee into a private callee
variant which must consume it on every exit. Raw semantic MIR uses only the first two conventions;
an optimized `owned` argument requires proof that the caller relinquishes ownership.

`CallResultConvention` determines the result storage shape:

- `Value`: the callee initializes `*T` through `@ret`;
- `AddressorPlace`: the callee writes a caller-rooted `*T` through an `@ret` of shape `**T`; and
- `YieldedOnce`: `project` exposes a callee-rooted place until `end_project` resumes its slide.

Native member addressors use `AddressorPlace` with explicit native result metadata recording the
receiver root, pointee layout, and access permission; see [abi.md](abi.md#native-member-addressors).
The receiver, including a temporary, must remain live throughout every use of the returned place.
Member storage must stay initialized: consuming access and shared writes are invalid, and owning
overwrites require `replace`. These restrictions survive aliases and forwarding through ordinary
generic mutable parameters. They do not make independently owned storage or Buffer slots subject
to a native member's initialization contract.

Every `Call` and `Project` retains its instantiated `CallImplType`. It is the source of argument and
result types, the result convention, and source fallibility. A native entry's machine return form
does not change this MIR result-storage contract.

Call operands are `[callee, hidden evidence..., visible places..., ret-out]`. Project operands omit
the trailing result place because the operation itself yields the scoped place. A dynamic callee is
read through the place of its function value, so calling a closure never moves its environment.

## Operations

The operation kind fixes operand arity, roles, and result shape. Moving an initialized place to
itself leaves it unchanged. The main groups are:

| Group | Operations | Contract |
|---|---|---|
| storage | `alloca`, `alloca_place`, `runtime_alloc`, `runtime_dealloc`, `is_initialized`, `load`, `store`, `clear`, `memcpy`, `move`, `move_bytes`, `replace` | Stack storage follows stack regions; runtime storage has an explicit lifetime. `is_initialized` exposes a physical drop flag without fixing its storage layout. `store` never drops; `memcpy` requires a concrete `TrivialCopy` pointee; moves leave their source absent. `move_bytes` carries an already-materialized byte extent instead of a layout dictionary. `replace` installs a fully initialized whole owned value without an observable initialization gap, retaining the displaced state for cleanup. Its destination may be a projection, absent, or partially initialized. |
| aggregates | `subfield`, `variant`, `extract_tag`, `extract_payload_indirection`, `build_array` | Aggregate construction and ownership remain field-addressable. Product `subfield` records its aggregate type and carries `Value` witnesses for direct members with open inline layouts. A variant operation first builds an uninitialized payload shell. Generic variant construction and payload-marked `subfield` operations carry the selected payload's `Value<B>` layout witness; projection reads inline/indirect classification from the stored tag. `extract_tag` yields an opaque semantic tag, while physical `extract_payload_indirection` yields the representation bit as `bool`. `build_array` initializes fresh canonical array storage from borrowed `TrivialCopy` elements. |
| evidence | `dict_entry`, `build_dictionary`, `subscript_member`, `build_subscript_evidence` | Evidence remains symbolic. Construction closes a definition over evidence operands; dictionary entries are closed function places. |
| calls/projections | `call`, `project`, `end_project` | Proven source-infallible forms are ordinary operations. Potentially source-fallible forms occur only inside `invoke`. |
| ownership | `clone`, `drop`, `build_closure`, `clone_closure_env`, `drop_closure_env`, `build_subscript`, `clone_subscript_env`, `drop_subscript_env` | Semantic ownership actions are explicit. `Value::clone` and `Value::drop` are source-infallible by contract. |
| matching | `comp_eq` | Compares a borrowed/materialized runtime value with compile-time pattern data. |
| stack/runtime | `stack_save`, `stack_restore`, `check_call_depth`, `check_fuel` | Stack markers describe allocation frontiers. Runtime guards are pinned operations whose sandbox violations leave the MIR CFG. |

**Copying and releasing come in a representation-level and a semantic form**, and both forms are
operations rather than one being a call:

| | representation | semantic |
|---|---|---|
| copy | `memcpy` | `clone <source> to <dest> via <callee>` |
| transfer / release | `move` | `drop <target> via <callee>` |

Representation copying requires `TrivialCopy`; otherwise copying uses semantic `clone`. `clone`
and `drop` each carry the type they act on independently of their callee. Their callee follows
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
statically `TrivialCopy`. The operation is specified over Ferlium's canonical array type, independent
of any interpreter representation. Non-trivial elements require explicit ownership operations.

A `call` may record the type and effect arguments instantiating a statically known generic callee,
in quantifier order; see [generic-instantiation.md](generic-instantiation.md). Substituting these
arguments into the callee's declared signature must reproduce the call's own type. Missing
instantiation metadata means "not known", not that the call is necessarily monomorphic.

The same optional metadata records which visible operands transfer ownership. Rendered calls prefix
those operands with `move`; the matching callee parameters render as `@arg owned`. Each transferred
caller place is consumed on both normal and source-error edges, and every owned parameter must be
absent at all callee exits.

Valid MIR satisfies operation arity and role requirements, type compatibility where independently
known, dominance, linear uses, source-failure flow, and storage ownership.

## Source failures and sandbox exits

A source-fallible operation is wrapped by `Invoke`, even if its error successor only contains
`propagate_error`. An invoked result exists only on the normal successor. `EndProject` derives
fallibility from its `OpenProjection` operand rather than duplicating the accessor type.

Both a fallible operation in a block body and an infallible `Invoke` are invalid. The implicit
source-error payload follows the explicit CFG: normal code may `return`, one pending failure may
`propagate_error`, and a second failure must reach `failure_during_cleanup`. Normal and error control
flow may not silently rejoin.

Sandbox violations, such as exceeding fuel, call-depth, or memory limits, are not source failures.
They bypass MIR successors, poison the executor, and enter runtime reclamation without running
more guest cleanup.

## Ownership verification boundary

Initialization and drop obligations are path-sensitive, including for members of local storage;
normal and source-error outcomes are distinct. `Project` creates an open-projection obligation on its normal
edge; `EndProject` consumes it when the slide starts on both outcomes. `return` and
`propagate_error` require all exact local obligations to be discharged. Poisoning exits may transfer
remaining storage to runtime reclamation.

MIR relies on HIR's proofs of generic descriptor equalities where no standalone MIR witness records
them. Call/storage representations are independently checked when both sides are concrete;
witnessed generic moves and calls retain that inference boundary. Standalone serialization requires
explicit normalized-layout/equality metadata to preserve those proofs.

## Physical MIR stage

Physical lowering consumes the complete optimized `MirArtifacts`, including declared bodies and
retained specializations. It resolves physical addresses, representations, callable environments,
and native ABI entries while preserving the semantic CFG, failure flow, ownership operations,
types, and constants where their representation does not require expansion.

The result need not correspond one-to-one with semantic function artifacts. Lowering may introduce
adapters and helpers, merge physically equivalent artifacts, or remove unreachable internal
artifacts. It maintains a resolution from every retained semantic callable and specialization to
its physical entry and convention, and rewrites calls consistently. Top-level module entries retain
their externally visible identity. Generated helpers are ordinary entries in the physical artifact.

`BackendReadyMirArtifacts` contains a verified physical function table and its supporting catalogs.
Semantic and physical stages use the same MIR structures, and shared operations retain their
meaning. Partially lowered bodies are not valid input to physical executors.

Shared optimization may run again after physical expansion. Rewrites preserve physical place and
ownership contracts; transformed artifacts are reverified before execution or backend emission.

Physical MIR retains shared ownership, callable, and control-flow operations with physical storage
semantics; it is not machine instruction-level IR. In particular, `clone`, `drop`, scoped
`project`/`yield`, and `invoke` remain valid. Unresolved semantic field projections and semantic
subscript-member selection must instead be expanded before this boundary.

Readiness verification checks structural and ownership contracts that survive lowering, supported
operations, and agreement between call sites and physical entries. It does not prove raw-memory
safety: physical execution must additionally enforce allocation bounds, alignment, initialization,
storage lifetimes, and native argument aliasing. Unsupported execution contracts must report an
error without silently falling back to another execution representation.
Malformed compiler-generated MIR can trigger an internal verifier panic, including in release
builds; embedders must not assume such invariant failures are recoverable compilation errors.

Each physical module owns relocatable dictionary and subscript catalogs. A dictionary definition
records its stable identity, physical capture layout, entry functions, and entry-to-capture mappings.
A subscript definition records its identity, capture schema, optional `ref` and `mut` functions, and
their provenance. Foreign references form explicit import lists. Local metadata and resolved
imports must agree on capture counts, entry contracts, and available members, independently of
semantic HIR storage.

A target-independent assembly step creates a `ResolvedPhysicalProgram` over the independently
lowered artifacts. It resolves function and evidence imports without rewriting or merging their
MIR bodies. Stable module-qualified identities remain available alongside resolved dictionary
descriptor indexes; executors materialize target addresses from the catalogs.

Backend-ready MIR may retain symbolic operands, dictionary construction and entry selection,
variant construction, and `extract_tag`, with representations fixed by the target ABI. Dictionary
construction retains captured evidence; live evidence values keep their environments alive
independently of stack regions. Calls borrow evidence, and releasing its owners follows the
[ABI evidence lifetime contract](abi.md#dictionary-evidence). Interpreter-only native calls and
target-lowered value representations must be resolved.

Physical artifacts retain native ABI contracts under the existing `FunctionId`, including native
dependencies reached through evidence catalogs and first-class values. This lets executors lower
calls without reconstructing transport from semantic types or introducing another function identity.
Contracts describe transport and storage requirements. Native representations are opaque leaves:
their Rust identity and layout must agree with their typed entries and registered `Value` layout
and clone/drop operations. Unsupported native type constructors with Ferlium arguments are rejected;
`Buffer<T>` uses its explicit physical representation instead. These requirements cover declared
native roots and local or imported evidence entries, not only direct calls.

MIR references remain symbolic. Native bindings must match the executing runtime's entry identities,
layouts, and result-domain guarantees. Process-local bindings are not portable ABI fingerprints:
equal size and alignment do not establish compatibility with an independently built Rust runtime.
The protocols are specified in [abi.md](abi.md#native-function-boundary).

### Physical failure transport

Physical MIR retains `Invoke` and its success-only result initialization contract. The leading
failure-state pointer is recorded in physical ABI signature metadata, not in MIR call operands.
Executors supply the current invocation's state. Signature verification must establish agreement
between call fallibility and failure transport, including for indirect calls. Machine lowering
implements `Invoke` with status handling without expanding it into a call and branch in shared MIR.
The diagnostic layout remains opaque; its ownership and lifetime are specified in
[abi.md](abi.md#source-failure-diagnostics).

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
runtime_alloc<A>(byte_size: int, align: int [, count: int]) -> *A
runtime_dealloc(address: *A)
```

The result is a materialized pointer value; the pointee type describes the storage reached through
it, while the explicit byte size gives the allocation its extent. An array of `A` therefore also
receives `*A`. Allocation is fresh, uninitialized and owned until transferred or deallocated.
Deallocation accepts the materialized allocation pointer, and a zero-byte allocation remains valid
and reclaimable. Repeated storage also carries its element count, including for zero-sized elements.
Both operations are pinned.

### Typed byte addressing

Physical MIR adds two representation-level address operations:

```text
address_offset<A>(base_address, byte_offset: int) -> place A
address_offset<A>(base_address, byte_offset: int, index: int) -> place A
address_offset_place<A>(base_address, byte_offset: int) -> place *A
```

The base is address-bearing and the offset is a materialized Ferlium `int`. `address_offset` yields
an aligned inline place of `A`; `address_offset_place` yields a slot containing an indirect place of
`A`. Loading the latter yields `*A`, while using that pointer as an address reaches `place A`. Both
retain the base allocation's provenance. Byte-offset expressions use ordinary calls such as
`Num<int>::add` and `Num<int>::mul`.

Product projections retain a static member index as instruction metadata, printed as `member N`.
Repeated-element projections instead take a third operand, printed as `index I`. These forms are
mutually exclusive. Distinct zero-sized subobjects may share an address but retain independent
initialization and drop obligations; byte location alone does not identify ownership. A variant
payload projection selects the active case, and changing cases invalidates views into the previous
payload.

Checked execution validates allocation lifetime, alignment, bounds, and the type of the selected
subobject. Transferring a member preserves the initialization state of its siblings. Copying or
moving a whole product requires all its fields to be initialized; replacement preserves absent
fields of the displaced value. Padding bytes are not value data and need not be initialized or read.

Logical product projections lower to typed byte addresses using the aggregate's layout and any
`Value` witnesses required by open inline member layouts. When the product shape itself is unknown,
tuple indices and record fields use projection-subscript evidence instead.

Variant-payload addressors inspect the indirection bit stored in the active tag when the storage
mode is not statically uniform. Inline payloads use their case-specific aligned byte offset.
Storing an indirect variant shell allocates its payload storage from `Value<B>` size and alignment;
payload projection only loads the resulting address. Payload initialization is independent of this
allocation lifetime, so `clear` can leave an addressable but absent payload and a later `store` can
reuse the allocation.

Moving a complete variant transfers its owning pointer; cloning requires a new allocation.
Destruction drops the live payload before releasing its allocation. Cleanup of a failed partial
construction drops only initialized members and releases nested allocations from inner to outer.

Private std Buffer functions carry a crate-private `BufferPrimitive` identity, including the slot
addressor and the `Value`/`Inspect` methods. The standard library registers their signatures and
addressor contracts and assigns the identities internally; it supplies no native executable entry.
HIR and boxed MIR share the Buffer intrinsics and boxed storage in `src/eval/buffer.rs`.
Physical lowering uses the same identities to expand storage calls and build retained bodies for
addressors, dictionaries and first-class references. Snapshots preserve these identities directly,
without native callable rebinding.

Physical `Buffer<A>` storage is one owning `*A` slot, with the backing layout specified in
[abi.md](abi.md#arrays). Taking and transferring elements use `move_bytes<A>`; a slot-to-slot
transfer requires an absent destination. Whole-buffer movement releases the target allocation,
transfers the source pointer, and leaves a valid zero-byte allocation in the source. Buffer
destruction releases the allocation and clears the pointer slot.
Boxed Buffer destruction likewise releases storage immediately and clears its owning value slot.
Normal boxed destruction checks in debug builds that every element slot was consumed.
Its Rust storage destructor also reclaims any remaining payload storage during poisoning, without
running Ferlium destructors.

### First-class subscript environments

`BuildSubscriptEvidence` closes non-owning symbolic evidence. `BuildSubscript` materializes it as
an owned first-class value; `CloneSubscriptEnv` and `DropSubscriptEnv` clone and release that
environment, while moving transfers it. The ABI defines its descriptor and environment layout.

Physical lowering refines semantic `SubscriptMember` into `BorrowSubscriptMember`, which produces a
`BorrowedCallable`: the selected `ref` or `mut` entry and a borrow of the original environment. It
is valid only as the callee of `Call` or `Project`. `Call` holds the borrow for one
invocation; `Project` holds it until the matching `EndProject`.

The callable type determines its visible ABI. The descriptor-specific entry determines its
environment schema. Invocation borrows stored evidence and clones source-value captures into the
temporary required by Ferlium's stateless callable semantics.

### Known and target-native calls

Compiler-known storage and addressor calls remain ordinary calls in semantic MIR; their physical
expansions are identified by function identity, not spelling. Other native calls retain their
`FunctionId` and use the matching Rust `extern "C"` entry. Backend-readiness requires every native
call to have been lowered or have a compatible entry for the selected target. A retained native
entry must have the closed, monomorphic Ferlium signature required by [abi.md](abi.md), with no
unresolved type variables at any depth in its parameters or result.

Retained Buffer and structural addressor entries must have physical MIR bodies under their existing
identities, including when referenced through dictionaries, subscripts, or first-class values.
Program assembly requires an actual body or verified native entry for every retained callable.

Buffer's internal `Value::clone` lowers to `invariant_failure`: only the surrounding array has
the information needed for element-wise cloning.
