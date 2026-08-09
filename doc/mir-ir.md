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

- `goto` and `condbr`;
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
generic function with one call site's types substituted and its trait dictionaries bound to
constants. The raw stage is always exactly the HIR table, which is also what lets the two stages be
told apart without a flag.

A specialization has no HIR entry, since nothing in the source declared it. Everything outside its
MIR body — whether it is script or native, its return convention, its parameter passing, its name —
is read from the function it was specialized from, through one indirection. That is why a
specialization keeps its original's signature exactly: binding a dictionary parameter replaces the
parameter's *uses* and leaves the parameter in place, so no metadata has to be duplicated.

## Values and roles

MIR uses independent, function-local `ValueId`s rather than operation locations:

- `%pN` is a parameter;
- `%rN` is an operation result;
- `@cN` is a concrete `TrivialCopy` constant representation;
- `bN` is a block target; and
- function, dictionary, subscript, and pattern operands remain symbolic.

Moving an operation therefore does not renumber unrelated values. A derived def-use map locates the
operation that defines each `ValueId` when an analysis needs it.

The constant pool is also the target of *reification* — expressing a value computed at compile time
back as MIR (`src/mir/reify.rs`). Because `@cN` is pinned to a `TrivialCopy` representation, only a
trivially-copyable leaf, or a tuple or record of those, can be reified; a compile-time `String`,
list, variant, or closure has no constant form, and the computation that produced it is left as
runtime code. Lifting that restriction requires either a frozen-prototype representation in the pool
with an operation to clone one, or emitting the MIR that rebuilds the value from constants it can
hold.

The verifier derives these roles from parameter kinds and operation results:

| Role | Meaning |
|---|---|
| place | Pointer to addressable storage. |
| materialized value | A value available without dereferencing a place. Owned materialized values have exactly one consuming use on each feasible path. |
| evidence | A dictionary or subscript used for generic dispatch. |
| stack marker | A saved allocation frontier consumed by `stack_restore`. |
| open projection | A yielded place plus the accessor contract whose slide must be ended exactly once. |

Compile-time match patterns are not runtime constants. They may represent source literals such as
`string` whose runtime value is owned even though its HIR immediate representation is `StaticStr`.

## Function boundaries

Parameters appear in this order:

1. `@extra`: dictionaries and other hidden evidence;
2. `@arg`: runtime arguments tagged with HIR's `Let` or `MutableRef` convention; and
3. `@ret`: the caller-provided result storage, present unconditionally in current MIR, including
   for `()` results.

Both argument conventions are represented as places in this MIR. `Let` is immutable, non-escaping
access to the selected value; `MutableRef` is exclusive mutable access. Snapshotting, cloning,
representation copying, and ownership transfer have already been made explicit before MIR lowering.

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
| storage | `alloca`, `alloca_place`, `load`, `store`, `clear`, `memcpy`, `move` | `store` never drops; `memcpy` requires a concrete `TrivialCopy` pointee; `move` leaves its source absent. Dynamic allocation/move carries a layout witness. |
| aggregates | `subfield`, `variant`, `extract_tag` | Aggregate construction and ownership remain field-addressable. A variant operation first builds an uninitialized payload shell. |
| evidence | `dict_entry`, `subscript_member`, `build_subscript` | Evidence remains symbolic and dictionary entries are function places. |
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

A `call` additionally carries **how it instantiated its callee**, when the callee is statically known
and generic: the type and effect arguments its quantifiers stand for, positionally. They are carried
down from HIR rather than recovered by matching the callee's generic signature against this call's
concrete one — see [generic-instantiation.md](generic-instantiation.md). The operand is absent for an
indirect call, for a non-generic callee, and at synthesized call sites where no generic application
substitution is available; a consumer treats absence as "not known", which costs an optimization
rather than correctness. Blanket-method forwarding thunks are not such a case: blanket matching
supplies their substitution, and their call records it.

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
