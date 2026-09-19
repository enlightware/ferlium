# Ferlium ABI Specification

This document is a draft of the Ferlium ABI for future Ferlium-WASM (and native) interoperability.
It specifies binary value representations, calling conventions, and the ownership and lifetime
contracts required at compiled boundaries, independently of the execution backend. Interpreter
storage and compiler implementation are outside its scope; [mir-ir.md](mir-ir.md) specifies MIR
contracts, and [hir-ownership.md](hir-ownership.md) specifies source-level ownership semantics.
Ferlium’s ABI is parametric over backend profiles, which define:

- Size
- Alignment

Backends then apply the common layout rules for:

- Records
- Tuples
- Tagged unions

This separation allows Ferlium to target:

- **Wasm32** (32‑bit pointers)
- **Wasm64** (64‑bit pointers)
- **Native** 32‑bit and 64-bit platforms

The language-defined representations in this document are stable across modules and compilation
units using the same backend profile. Rust-native values are intentionally build-coupled instead:
generated code and its runtime must use the same native-type layout catalog, as described below.
Each supported target must validate that its native calling conventions and layouts agree with
the runtime; matching pointer width alone does not establish ABI compatibility.

# Backend Profiles

A *backend profile* defines the fundamental sizes and alignments for a Ferlium target.

## ABI‑32 profile

This profile is used by wasm32, native‑32, or any backend with 32‑bit pointers.

| Type | Size | Alignment | Notes |
|------|------|-----------|-------|
| `()` (unit) | 0 | 1 | No storage needed |
| `bool` | 1 | 1 | Stored as 0/1 |
| `i8`, `u8` | 1 | 1 | |
| `i16`, `u16` | 2 | 2 | |
| `i32`, `u32`, `f32` | 4 | 4 | |
| `i64`, `u64`, `f64` | 8 | 8 | |
| `int`, `isize`, `usize` | 4 | 4 | same size as pointer size |
| Pointer (`*T`) | 4 | 4 | 32‑bit offset in linear memory or native pointer |

## ABI‑64 profile

This profile is used by wasm64, native‑64, or any backend with 64‑bit pointers.

Same rules as ABI‑32 except:

| Type | Size | Alignment |
|------|------|-----------|
| `int`, `isize`, `usize` | 8 | 8 |
| Pointer (`*T`) | 8 | 8 |

Scalars follow the same C/Rust alignment rules across mainstream platforms.

## Scalar slots

Besides pointer size, a backend profile defines its *ABI scalar slots*: the set of value shapes that the backend can pass and return directly, without going through memory.
A scalar slot is independent of the pointer size; in particular, 32-bit profiles still have 64-bit scalar slots.

| Profile | Scalar slots |
|---------|--------------|
| ABI-32 (wasm32, native-32) | `i32`, `i64`, `f32`, `f64` |
| ABI-64 (wasm64, native-64) | `i32`, `i64`, `f32`, `f64` |

These correspond to the Wasm value types on Wasm targets, and to register-passable scalars on native targets (where C ABIs pass 64-bit integers and doubles by value even on 32-bit platforms).

A value uses a scalar slot only when target ABI lowering assigns it a scalar representation.
Primitive integers, floats, booleans, and pointers have such representations.
An aggregate does not acquire a scalar representation merely because its byte size is at most 8; tuples, records, and named product types are passed indirectly under this ABI.

Aggregate coercion or flattening requires an explicit ABI extension defining padding, packing, and
callee reconstruction; it is not a consequence of `TrivialCopy` or size alone.

# Calling conventions

Ferlium source has mutable value semantics.
A parameter written as `T` is a `Let` access: the callee may observe it immutably for the duration of the call, but may neither mutate it nor retain access after returning.
A parameter written as `&mut T` is a `MutableRef` access: the callee receives exclusive mutable access to the caller's place for the duration of the call.

`Let` is a semantic convention, not a physical transport choice.
It permits the caller to share existing storage when that is safe.
The value observed through a `Let` argument must not change because of later argument evaluation
or mutation inside the callee. If these accesses overlap, the caller supplies a snapshot of the
value at the argument's evaluation point. Two `Let` arguments may share storage; overlapping
mutable arguments are invalid.

Physical argument passing is derived from the lowered parameter type:

| Semantic convention and representation | Physical ABI form |
|-----------------------------------|-------------------|
| `MutableRef` | Mutable reference/pointer to caller storage |
| `Let` with a scalar ABI representation | Direct scalar value |
| Other concrete `Let` | Shared reference/pointer to storage containing the observed value |
| Generic `Let` | Shared reference/pointer to storage containing the observed value |

Unit has no scalar representation: a concrete `Let` unit argument is indirect, while a unit
result is omitted from the machine return.

Generic `Let` parameters are physically indirect, even if they have a `T: TrivialCopy` constraint.
This gives every generic function one stable ABI independent of later concrete instantiations.

These transport choices apply to direct entries. First-class function entries use the uniform
pointer-based interface described under [Functions and closures](#functions-and-closures).

An indirect `Let` points to the original shared place or, when a snapshot is required, to the
snapshot's storage. In either case, the observed value remains live throughout the call.

For example, `int` and `float` have scalar ABI representations on ABI-32 and ABI-64.
A tuple or record uses indirect transport even when it is small.
The representation of a structurally `TrivialCopy` aggregate may be copied regardless of size.
`TrivialCopy` classifies whether a representation copy is semantically valid independently of physical passing.

## Return value

Return passing is derived from the lowered return type and the function effects.
Each function can have effects, which might be polymorphic and represented by effect variables.
There are two language-effect cases:

- **No language failure**: the function's effects contain no `Fallible` and no effect variables
- **May return a language failure**: the function's effects contain `Fallible` or effect variables

There are three return value classes:

- **No value**: `()` and eligible statically zero-sized Ferlium products
- **Direct value**: concrete values with a direct scalar ABI representation
- **Caller-allocated value**: aggregates, address-only values, and polymorphic results

First-class Ferlium callables use a uniform caller-allocated result convention, including for `()`.
An optimized direct implementation may omit a statically zero-sized product result; an adapter
preserves the callable interface and initializes the declared result type on success. Zero size does
not remove construction effects or destruction obligations. Shared generic implementations retain
result storage. Physical module interfaces distinguish direct and callable entries without changing
source function types. Rust native entries retain their declared result contracts.

Direct generated Ferlium calls and Rust native entries use these return forms:

| May return language failure? | Return value kind      | ABI return form                                                | Out-pointer needed? |
|------------------------------|------------------------|----------------------------------------------------------------|---------------------|
| No                           | No value               | Returns `()`                                                   | No                  |
| No                           | Direct value           | Returns the value directly                                     | No                  |
| No                           | Caller-allocated value | Returns `()`; callee writes result to out-pointer              | Yes                 |
| Yes                          | No value               | Returns status                                                 | No                  |
| Yes                          | Direct value           | Returns status; callee writes result to out-pointer on success | Yes                 |
| Yes                          | Caller-allocated value | Returns status; callee writes result to out-pointer on success | Yes                 |

Status is an unsigned 32-bit integer (`u32` in Rust): 0 on success and non-zero on source failure.
On failure, result storage contains no live result; the callee must clean up any partial construction.

Physical parameter order is: failure-state pointer (when the function may fail), other hidden
parameters, source arguments, then result out-pointer (when required). Output pointers are explicit
parameters, not implicit C aggregate-return parameters.

### Source-failure diagnostics

The execution harness creates one empty, opaque failure state per invocation and passes its
pointer through calls that may fail, including calls with unresolved effect variables. Calls
within an invocation share this state.
A failing callee records its diagnostic, then callers follow semantic cleanup and propagate status.
The Rust runtime owns the diagnostic, including messages and backtraces; generated code accesses
it only through runtime operations. The harness takes the diagnostic when execution ends.

Nested host-initiated invocations use separate states. A second failure during cleanup preserves
both causes and triggers harness cancellation; poisoning is not another return status. Diagnostic
storage must survive guest-domain reclamation.

### Sandbox violations

Host-enforced sandbox violations are separate from the source-language `Fallible` effect. Fuel,
call-depth and accounted-memory limits do not make every function
that can allocate or execute a loop source-level `Fallible`; Ferlium code cannot catch these
violations.

A sandbox violation therefore does not change the normal return forms above.
It exits ordinary call/return control flow, poisons the affected runtime domain, and runs no Ferlium semantic cleanup.
A backend may implement this as a trap or non-returning runtime abort entry that captures diagnostics and performs bounded host-side revocation and storage reset.
Failures raised by Ferlium's accounted runtime use this defined path; exhaustion below that runtime, such as failure of the host allocator, may still abort or trap at a lower level. See [runtime-sandboxing.md](runtime-sandboxing.md).

## Wasm

Rust and generated Ferlium code call each other through ABI-matched Wasm functions sharing one
linear memory. Linking and an outer trap boundary may use JavaScript, but language arguments and
results never require JavaScript conversion or forwarding.

The wasm32 profile uses `i32` for pointers and target-sized Ferlium `int`. A wasm64 profile must
change both integer transport and addressing; enabling 64-bit memory alone is insufficient.
Rust hosts binding generated functions into their function table must link with `--growable-table`.

The Wasm backend maps direct values to Wasm value types (`i32`, `i64`, `f32`, `f64`) following the scalar-slot rules.
The `u32` status maps to Wasm `i32`, whose type does not encode signedness.
Shared references, mutable references, and caller-allocated result pointers are represented as pointers in linear memory using the selected backend profile.

Parameters follow the physical order above, with result storage last. Fallible calls return only
the status; they do not use multi-value results for `(status, value)`.

## Native

Use the target C calling convention with the explicit scalar/pointer transport above. Detailed
lowering is target-specific: pointers and `usize`/`isize` follow the target width, while status
remains `u32`.

# Scalar Representation

This section applies once the backend profile is selected.

- All scalars are stored in **little‑endian** format.
- Alignment must be respected.
- Memory is byte-addressable.
- Floating-point values must be finite (neither NaN nor infinity).

# Rust-native values

A Rust-native Ferlium type registered for a compiled target stores an actual value of its Rust type
`T` in-place. It is not converted to a separately invented Ferlium aggregate or handle
representation merely because it crosses between generated Ferlium and Rust runtime code.

Its layout is the layout selected by Rust for the matching runtime build and target:

```
size(native T)  = size_of::<T>()
align(native T) = align_of::<T>()
```

The corresponding `Value<T>::SIZE` and `Value<T>::ALIGN` evidence must report that same layout.
Generated code and the runtime therefore share a native-type catalog identifying the Rust type,
layout and target glue. A generated artifact is compatible only with a runtime whose catalog and
layout fingerprint match; Rust-native layouts are not promised to remain compatible across Rust
compiler versions or independently built runtimes.

On ordinary execution paths, the target glue preserves Rust initialization and RAII rules:

- construction writes a valid `T` into uninitialized, correctly aligned storage;
- a Ferlium `Let` or `MutableRef` access may be adapted to a temporary Rust `&T` or `&mut T` for the
  duration of the runtime call, but the reference may not escape that access;
- cloning invokes the registered Rust clone operation and initializes distinct destination storage;
- moving relocates the value into uninitialized destination storage and leaves the source absent;
- replacement installs the prepared new value before destroying the detached old value; and
- opaque native `Value::drop` invokes the registered Rust destructor exactly once and leaves the
  target uninitialized; subsequent reclamation releases only its storage.

Opaque native destruction has the Ferlium signature `Value::drop(&mut T) -> ()`; its
`unsafe extern "C"` entry takes `*mut T` to initialized storage and destroys the pointee without
freeing that storage. The caller must subsequently treat the pointee as uninitialized and must not
destroy it again. Ordinary mutable native entries instead leave their target initialized after the
call. Entry contracts distinguish consuming storage from an ordinary mutable borrow without
introducing another source-language parameter convention.

These destructor rules concern types stored as their actual Rust representation. `Buffer<T>` has
the separate compiled representation and ownership contract described in the [Arrays section](#arrays).

Generated code may allocate, move and pass a native value using its registered layout, but it must
not inspect private fields or synthesize byte patterns unless the native registration separately
exposes structural operations that make doing so valid. Internal pointers and allocations owned by
`T` belong to the matching runtime's memory and resource domain.

Poisoning is deliberately outside the ordinary RAII path because it stops semantic cleanup. Bounded
reclamation of Rust-native values and revocation of any external resources they own is a general
runtime-domain requirement, not a type-specific representation rule; see
[runtime-sandboxing.md](runtime-sandboxing.md).

# Records

Records are laid out linearly in memory without boxing.

## Type-level equality

Ferlium records are **structural**:

```
{ x: i32, y: f32 } == { y: f32, x: i32 }
```

Type equality ignores field order.

## Canonical field order

Fields are canonicalised to produce a stable layout:

1. Compute each field’s alignment (per backend profile).
2. Sort fields by:
   - **Primary:** decreasing alignment
   - **Secondary:** lexicographic field name

```
fields(record) = sort_by( (-align(type(field)), field.name) )
```

Whether a record is named (`struct`) does not affect layout.

## Layout Algorithm

Given canonical ordered fields `f₁, f₂, …`:

1. Let `offset = 0`
2. For each field `f`:
   - Let `a = align(T_f)`, `s = size(T_f)`
   - Align offset upward to `a`
   - Assign field offset
   - Set `offset += s`
3. Set `align(record) = max align(T_f)`
4. Set `size(record) = round_up(offset, align(record))`

Equivalent to Rust's `#[repr(C)]` after canonical ordering.

# Tuples

Tuples are laid out linearly in memory without boxing.
Tuples are **positional**:

- Order = declared order `(T₀, T₁, …)`
- Layout follows record rules with that order
- Alignment = maximum element alignment

Equivalent to a C struct with fields in positional order.

# Tagged unions

Tagged unions store their payloads inline unless the payload edge belongs to the same recursive
representation component. Such recursive edges are represented by an owning pointer, making
recursive layouts finite.

Tagged unions can be named:

```
enum V {
  A : T_a,
  B : T_b,
  C,          // no payload
}
```

or anonymous:

```
A (T_a) | B (T_b) | C
```

This does not affect their layout.

## Tag representation

Tags are stored as `u32`. The low 31 bits refer to an interned string within one compilation
session; tag identity is global by name across variant types, as generic variant matching requires.
The high bit is clear for an inline payload and set for an indirect payload. Semantic tag comparison
masks that representation bit. Numeric discriminants are not stable across compilation sessions.

## Payload layout

For each case:

- No payload is treated as unit: size 0, alignment 1
- Payload type follows record/tuple rules
- A tuple payload is the payload value itself. Its fields are laid out directly according to the
  tuple rules; there is no additional tuple box.

## Variant representation

Let `V` be a variant type and `B_i` the logical payload type of case `i`. The stored representation
`S_i` of that case is:

```
S_i = B_i                 if the payload is inline
S_i = owning_pointer<B_i> if the payload is indirect
```

The case payloads do not share one maximum-aligned C-union offset. Each case has an offset derived
from its own stored representation:

```
payload_offset_i = align_up(size(u32), align(S_i))
```

The complete variant still has one fixed size and alignment, independent of its active case:

```
align(V) = max(align(u32), max_i(align(S_i)))
size(V)  = align_up(
    max(size(u32), max_i(payload_offset_i + size(S_i))),
    align(V),
)
```

Consequently, the tag determines not only which payload type is active but also which payload offset
applies. Code must establish the case before forming a payload place. This is intentionally not a C
union representation.

Case-specific offsets avoid padding a small but long payload to the alignment required by an
unrelated case. For example, with a 4-byte tag, twelve inline `u8` fields end at byte 16, while an
inline `u64` case starts at byte 8 and also ends at byte 16. The variant therefore occupies 16 bytes
at alignment 8. A common union offset of 8 would make the twelve-byte payload end at byte 20 and
round the variant size up to 24 bytes.

For an open generic case with payload type `B`, physical lowering uses the case's inline/indirect
storage evidence together with `Value<B>`:

- inline storage uses `Value<B>::ALIGN` to calculate the case offset;
- indirect storage uses the target pointer alignment for the case offset and `Value<B>::SIZE` and
  `Value<B>::ALIGN` to allocate the separate payload block.

When the case remains open in unspecialized generic code, construction receives the indirection
decision as a transient boolean evidence argument and combines it into the tag it writes. This is
not a separate field in the constructed value. Once a variant value has been constructed, payload
projection obtains the same classification from the high bit of the stored tag; it does not need a
second boolean argument.

A payloadless case writes only its tag and requires no payload layout witness.

No `Value<V>` witness is needed merely to address a known case payload inside an existing `V`
place. Allocating or moving the complete variant remains a whole-value operation and uses `Value<V>`
when `V` has no static layout at the lowering site.

Payload layout evidence uses the ordinary `Value<B>` hidden parameter, not a distinct runtime
dictionary kind. Multiple cases with the same payload type and ordinary operations on `B` share
that parameter.

Every case whose payload representation reaches the same recursive representation component as
`V` stores an owning pointer to its complete payload `B_i`; other case payloads are inline.
Consequently non-recursive payloads do not acquire a box merely because they belong to a variant.
A variant is `TrivialCopy` exactly when all its possible payloads are `TrivialCopy`; an indirect
recursive edge owns storage and therefore prevents that classification.

### Indirect payload ownership

An indirect payload pointer uniquely owns an allocation containing the payload value. Its lifecycle
is part of the value representation:

- Construction allocates storage using the payload representation's size and alignment, initializes
  the payload in that storage, and stores the owning pointer in the active case's payload slot.
- Cloning recursively clones the payload into a new allocation; it never copies the owning pointer
  as a second owner.
- Moving transfers the pointer unchanged and leaves the source variant moved out; it does not clone
  or reallocate the payload.
- Dropping first runs the payload's semantic drop, then deallocates the payload allocation and clears
  the pointer. As with Buffer storage, the runtime deallocator accepts only the pointer and recovers
  any allocator-specific layout metadata internally.

Inline payloads require no allocation or representation-level deallocation. A case without a
payload likewise allocates nothing.

# Arrays

Arrays store their elements linearly in memory without boxing.
Arrays in Ferlium are actually double-ended queues (deques) to allow efficient appends at both ends:

```
struct Deque<T> {
   data_ptr : *T,    // pointer to backing buffer of `cap` elements
   head     : usize, // index of first logical element in [0..cap)
   len      : usize, // number of elements currently stored (≤ cap)
   cap      : usize, // capacity (number of T slots)
}
```

with elements stored in a ring buffer of `cap` T values, and logical index `i` mapping to physical slot `(head + i) mod cap`.

This leads to:

* alignment = 4 (32 bit targets) or 8 (64 bit targets)
* size = 16 (32 bit targets) or 32 (64 bit targets)

The source prelude represents `data_ptr` with its private `Buffer<T>` native type while keeping
`head`, `len`, and `cap` in the surrounding array value. The compiled representation of
`Buffer<T>` is therefore exactly one owning pointer: its size and alignment are the target pointer
size and alignment.

Buffer allocation receives `Value::<T>::SIZE` and `Value::<T>::ALIGN` explicitly. Slot-addressing
and element-move operations receive only `Value::<T>::SIZE`: the aligned allocation base and the ABI
rule that type sizes include tail padding already guarantee that each slot is aligned.

Every layout has a positive power-of-two alignment and a size divisible by that alignment. For
non-zero-sized types, alignment is therefore no greater than size. Zero-sized types are the
exception to that last inequality—for example, `()` has size 0 and alignment 1—and require no
backing allocation.

A buffer allocated with capacity 0 may use placeholder size 0 and alignment 1, because it has no
slot to address and no storage to align. Its zero-byte allocation is valid and reclaimable; these
placeholder arguments do not describe the element layout. Growth to non-zero capacity must use
the true `Value<T>` layout, so no slot is addressed with the placeholder.

Array cleanup destroys its live elements before releasing the backing buffer. Buffer destruction
deallocates the backing storage and clears its owning pointer. The runtime exposes pointer-only
deallocation and retains any allocator-specific layout metadata internally; a capacity-0 buffer is
deallocated by the same path as any other. Whole-buffer moves must release an existing target
allocation before replacing its pointer, so every allocation is reclaimed exactly once.

# Dictionary evidence

A dictionary reference has this representation, with fields in the stated order and alignment
according to the backend profile:

```text
{
   descriptor_index: u32,
   env_ptr: target_pointer
}
```

`descriptor_index` identifies the dictionary's entries and environment contract. Dictionary,
function, and subscript descriptors use module-qualified symbolic references in independently
compiled artifacts. Linking resolves those references to program-wide indexes; references to
static data similarly resolve to target addresses.

`env_ptr` points to the captured prerequisite evidence, or is zero for a captureless dictionary.
The descriptor determines the environment's layout and entry calling contracts, including how
each entry receives its required evidence.

Dictionary entries use the trait declaration's argument transport, before implementation-type
substitution, and the caller-allocated result convention. Adapters bridge to implementation ABIs
when necessary.

Dynamic evidence environments are immutable and reference-counted. Calls borrow evidence for
their duration. Capturing or cloning evidence retains its environment; moving transfers ownership;
releasing the last owner releases the captured evidence and reclaims the environment. Static
evidence has program lifetime and requires no reference-count updates. Evidence lifecycle
operations do not invoke source-level clone/drop methods.

Stored evidence captures form an acyclic graph: construction captures existing evidence, and
capture fields cannot subsequently change. An entry requiring its own dictionary receives the
current dictionary reference rather than an owning self-capture. Capturing evidence therefore
secures the lifetime of all its transitive prerequisites without copying their environments.

# First-class callables

Every first-class callable uses the same outer `{ descriptor_index: u32, env_ptr: target_pointer }`
layout as [dictionary evidence](#dictionary-evidence). Its environment ownership follows the
function or subscript contract below.

## Functions and closures

Ferlium represents all first-class functions uniformly as closures using the common callable
layout.

For a closure, `descriptor_index` selects:

- the call entry;
- environment cloning; and
- environment drop and deallocation.

On Wasm, the descriptor selects the closure-compatible `call_indirect` entry and its environment
metadata.

`env_ptr` is the owning pointer to the closure environment in target memory. The environment
contains the runtime representations of captured hidden evidence and owned source values. Its
ordered shape is known at the closure construction site, but a generic capture tuple `B` may have
witness-derived size, alignment and field offsets. The environment therefore retains any dynamic
`Value<B>` evidence needed by the closure entry and its clone/drop operations. Statically known
evidence may instead be compiled into those operations.

`env_ptr` is zero exactly when the closure captures neither hidden evidence nor source values. A
non-zero environment pointer owns one allocation:

- construction moves the already-owned source captures into it and retains captured evidence;
- moving the closure transfers the pointer and clears the source;
- cloning the closure allocates a new environment, retains captured evidence and clones the
  owned capture tuple through `Value<B>`;
- dropping the closure drops the owned capture tuple, releases captured evidence, and deallocates
  the environment exactly once.

Invoking a closure borrows the closure value. It clones the owned capture tuple into a per-call
temporary, passes the temporary captures and stored hidden evidence to the function body, and
drops the temporary after both normal return and language failure.

A closure-compatible entry uses the uniform parameter order `failure_state`, `env_ptr`, visible
arguments, then result storage. Visible arguments and results are passed by pointer, including for
`()`, and the entry returns a status; infallible targets always return success. An adapter preserves
source access modes while translating this interface to the target's direct ABI. A captureless
entry ignores its zero `env_ptr`.

## First-class subscripts

A first-class subscript uses the common callable layout. Its descriptor selects optional `ref` and
`mut` entries, environment layout, and clone/drop support. The entry determines the environment
schema; indirect application passes `env_ptr` and the type-derived visible ABI.

A non-zero `env_ptr` owns one environment allocation. Construction initializes it, moving transfers
ownership, cloning creates an independent environment, and dropping destroys its captures and
deallocates it. Construction and cloning retain captured evidence; destruction releases it.
Invocation borrows stored evidence. Captured source values follow the closure invocation rules
above.

Selecting `ref` or `mut` borrows the subscript environment. [mir-ir.md](mir-ir.md) specifies the
resulting ephemeral MIR value and its lifetime.

# Native-function boundary

A native callable used by compiled code exposes one typed `extern "C"` entry. Interpreter boxing
is not part of the ABI. Export naming and retention are separate from the calling convention.

The entry contract specifies parameter representations, pointee layouts, mutability, and the result
protocol. The Rust entry and its Ferlium declaration must agree on this contract. Like
[Rust-native layouts](#rust-native-values), it is build-coupled: generated callers and the runtime
must agree on the contract for their target.

Every native signature retained at the compiled boundary must be closed and monomorphic, including
all nested types in visible parameters, hidden parameters, and results. Generic native calls must
be specialized to closed entries or eliminated before reaching the boundary; this ABI does not
define polymorphic native entries. Every retained native callable must supply a compatible C entry.

## Value transport and safety

Entries follow the [calling conventions](#calling-conventions) above:

- Concrete `int` and `float` use `isize` and `f64` transport. Opaque Rust values remain indirect,
  even when small; size alone does not determine transport.
- Borrowed inputs use `&T` or `&mut T`, and output storage uses `&mut MaybeUninit<T>`, all transported
  as pointers. The caller guarantees valid, aligned storage and call-scoped borrowing. Consuming
  destructors follow the separate [ownership contract](#rust-native-values).
- Output storage is initialized exactly once when a result is produced and contains no live result
  on failure or absence.
- Fallible entries return status and record diagnostics through the leading failure-state pointer.
  Rust `Result` and error layouts never cross the ABI. Rust panics are not source failures and must
  not unwind across the C boundary.

Floating-point values must satisfy Ferlium's finite-value contract before crossing the boundary.
The `float` type has the layout and ABI of `f64`; the finite-value requirement also applies to
optional and fallible payloads. Native implementations must preserve language semantics without
panicking on valid Ferlium inputs.

Native entries must not embed session-local variant tags. They return transport-level values, such
as scalar comparison codes, from which the caller constructs Ferlium variants.
An ordering code is exactly `-1`, `0`, or `1` for Rust `Less`, `Equal`, or `Greater`. This value
domain does not itself assert ordering laws or effects.

## Native optional results

A Rust `Option<R>` result is supported when the Ferlium result's resolved `Repr` is exactly
`None(()) | Some((T,))` and `R` has the representation of `T`. Compatibility depends on this
representation, not on the identity of the `Option<T>` alias.

The entry uses a presence flag and trailing payload storage:

```text
extern "C" fn(arguments..., output: &mut MaybeUninit<R>) -> bool
```

It returns `true` after initializing `output` exactly once with the `Some` payload, or `false` for
`None` with no live output. The caller constructs the canonical Ferlium variant; Rust's `Option<R>`
layout never crosses the ABI. This protocol is infallible: absence is not a source failure.
Optional results must use this protocol with matching payload representations.

# Compiled runtime boundary

Generated code obtains allocation services from its runtime. The target interface provides aligned
allocation and reallocation together with pointer-only deallocation. `dealloc(ptr)` recovers any
allocator-specific size and alignment metadata.

A zero-byte allocation is valid and reclaimable. Allocation quota exhaustion follows the
sandbox-violation policy; lower-level allocator exhaustion may abort the runtime. Accounting,
shared-memory headroom, and reclamation are specified in
[runtime-memory-limits.md](runtime-memory-limits.md) and
[runtime-sandboxing.md](runtime-sandboxing.md).

On Wasm, every pointer returned by these services is an offset into the shared linear memory. The
generated module imports that memory and the runtime functions it calls. It exports only the
top-level module entrypoints invoked by the host; ordinary Ferlium functions and indirect-call
table entries remain internal. A host-facing entrypoint wrapper adapts browser, Rust, or C values
to the core Ferlium ABI and makes ownership transfer explicit.

The exact Wasm import names and allocator function signatures are part of the matching target
catalog.

# Rust structural interoperability

Rust-native types are opaque leaves: Ferlium stores the real `T` and uses its registered
operations without computing member offsets. A native member can be exposed through an explicit
addressor or adapter, which follows the Rust type's own layout.

Ferlium variants use case-specific payload offsets and are not C unions. A Rust enum is therefore
not structurally interchangeable merely because its cases have corresponding names and payloads;
it remains an ordinary non-structurally-exposed Rust-native type unless an adapter explicitly
implements the Ferlium variant representation.

## Native member addressors

A native member addressor exposes a member `M` of a closed Rust-native receiver `T` through
independent shared and mutable pointer entries. Both types must have registered native
representations; exposing a member does not make the receiver structurally interchangeable with
a Ferlium product. Each entry takes one receiver argument:

```rust,ignore
unsafe extern "C" fn shared(receiver: *const T) -> *const M;
unsafe extern "C" fn mutable(receiver: *mut T) -> *mut M;
```

Fallible entries use the invocation-owned failure protocol, with trailing pointer-result storage.
`NativeFailureState` denotes the opaque [failure state](#source-failure-diagnostics):

```rust,ignore
unsafe extern "C" fn shared(
    failure: &mut NativeFailureState,
    receiver: *const T,
    output: &mut MaybeUninit<*const M>,
) -> u32;
unsafe extern "C" fn mutable(
    failure: &mut NativeFailureState,
    receiver: *mut T,
    output: &mut MaybeUninit<*mut M>,
) -> u32;
```

An infallible entry returns a non-null, aligned pointer to an initialized member. A fallible entry
writes such a pointer to its output on success; failure records a diagnostic and leaves the output
uninitialized. Both exits preserve the receiver's initialization. The entry contract identifies the
receiver as the result root and records the member layout and shared/mutable permission. Pointers
are memory offsets on Wasm32. [MIR result storage](mir-ir.md#function-boundaries) is separate from
these native return forms.

The host guarantees that the pointer is rooted in the receiver, remains valid throughout its
borrow, and requires no suspended Rust guard or access epilogue. The caller keeps the receiver live
through every use of the member, including when the receiver is a temporary.
Entries must not retain input pointers or unwind. A mutable entry additionally guarantees that
arbitrary valid member mutation and replacement preserve the enclosing Rust value's invariants.
If that guarantee cannot be made, expose a shared member or a validating getter/setter instead.
The addressor contract does not assert repeatability or disjointness of differently named members.

Native members remain initialized for the enclosing value's entire live lifetime. Shared members
permit reads and registered cloning. Mutable members additionally permit ordinary typed mutable
calls, whole-member replacement, and complete writes of `TrivialCopy` members. Replacement installs
the new member before destroying the detached old value. Moving out, clearing, consuming destruction,
or using a live owning member as uninitialized result storage is invalid. These restrictions also
apply when forwarding the member through aliases or generic mutable parameters. Generated Ferlium
code never discovers Rust field offsets by layout arithmetic.
