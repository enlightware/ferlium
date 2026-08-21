# Ferlium ABI Specification

This document is a draft of the Ferlium ABI for future Ferlium-WASM (and native) interoperability.
It specifies the binary representation of Ferlium values independently of the execution backend.
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
An aggregate does not acquire a scalar representation merely because its byte size is at most 8; tuples, records, and named product types are initially passed indirectly.

A later backend may introduce an explicit aggregate coercion or flattening plan.
Such a plan must define padding, packing, and callee reconstruction and is an ABI optimization, not a consequence of `TrivialCopy` or size alone.

# Calling conventions

Ferlium source has mutable value semantics.
A parameter written as `T` is a `Let` access: the callee may observe it immutably for the duration of the call, but may neither mutate it nor retain access after returning.
A parameter written as `&mut T` is a `MutableRef` access: the callee receives exclusive mutable access to the caller's place for the duration of the call.

`Let` is a semantic convention, not a physical transport choice.
It permits the caller to share existing storage when that is safe.
When a `Let` argument aliases a mutable argument of the same call, or when evaluation of a later argument writes the same place, HIR stores an explicit `CloneValue` snapshot at the `Let` argument's evaluation point.
Managed snapshots use an owned temporary cleaned after the call; `TrivialCopy` snapshots remain direct values.
Thus neither later argument evaluation nor mutation inside the callee can change the value observed through the earlier argument.
Two `Let` arguments may share storage; overlapping mutable arguments remain a borrow-checking error.

Physical argument passing is derived from the lowered parameter type:

| HIR convention and representation | Physical ABI form |
|-----------------------------------|-------------------|
| `MutableRef` | Mutable reference/pointer to caller storage |
| `Let` with a scalar ABI representation | Direct scalar value |
| Other concrete `Let` | Shared reference/pointer to storage containing the observed value |
| Generic `Let` | Shared reference/pointer to storage containing the observed value |

Generic `Let` parameters are physically indirect, even if they have a `T: TrivialCopy` constraint.
This gives every generic function one stable ABI independent of later concrete instantiations.

An indirect `Let` normally points to the original shared place.
If overlap analysis required a snapshot, it instead points to the explicit snapshot's storage.
The convention remains `Let` in both cases: the snapshot and its cleanup are represented by HIR ownership operations, not hidden in call metadata.

For example, `int` and `float` have scalar ABI representations on ABI-32 and ABI-64.
A tuple or record initially uses indirect transport even when it is small.
If a snapshot of a structurally `TrivialCopy` aggregate is needed, `CloneValue::TrivialCopy` copies its representation regardless of size.
`TrivialCopy` classifies whether a representation copy is semantically valid independently of physical passing.

Implementation note: HIR and native callables expose semantic argument conventions.
Target-specific ABI lowering will derive scalar or indirect physical transport later.
The interpreter's native-Rust bridge makes the analogous `T` versus `&T` extraction decision separately from `ArgConvention`; both Rust adapter forms can implement a Ferlium `Let` parameter.
Current MIR keeps both semantic argument conventions as places and gives every function an
unconditional return out-pointer, including functions returning `()`. This uniform executable MIR
form is intentionally independent of the direct/indirect physical ABI chosen by a machine backend.

## Return value

Return passing is derived from the lowered return type and the function effects.
Each function can have effects, which might be polymorphic and represented by effect variables.
There are two language-effect cases:

- **No language failure**: the function's effects contain no `Fallible` and no effect variables
- **May return a language failure**: the function's effects contain `Fallible` or effect variables

There are three return value classes:

- **No value**: `()`
- **Direct value**: concrete values with a direct scalar ABI representation
- **Caller-allocated value**: aggregates, address-only values, and polymorphic results

The calling convention for return values is:

| May return language failure? | Return value kind      | ABI return form                                                | Out-pointer needed? |
|------------------------------|------------------------|----------------------------------------------------------------|---------------------|
| No                           | No value               | Returns `()`                                                   | No                  |
| No                           | Direct value           | Returns the value directly                                     | No                  |
| No                           | Caller-allocated value | Returns `()`; callee writes result to out-pointer              | Yes                 |
| Yes                          | No value               | Returns status                                                 | No                  |
| Yes                          | Direct value           | Returns status plus the direct value                           | No                  |
| Yes                          | Caller-allocated value | Returns status; callee writes result to out-pointer on success | Yes                 |

For a `Fallible` function, status is 0 on success and non-zero on language failure.

### Sandbox violations

Host-enforced sandbox violations are separate from the source-language `Fallible` effect. Fuel,
call-depth, interpreter-environment, and future accounted-memory limits do not make every function
that can allocate or execute a loop source-level `Fallible`; Ferlium code cannot catch these
violations.

A sandbox violation therefore does not change the normal return forms above.
It exits ordinary MIR control flow, poisons the affected runtime domain, and runs no Ferlium semantic cleanup.
A backend may implement this as a trap or non-returning runtime abort entry that captures diagnostics and performs bounded host-side revocation and storage reset.
Failures raised by Ferlium's accounted runtime use this defined path; exhaustion below that runtime, such as failure of the host allocator, may still abort or trap at a lower level. See [runtime-sandboxing.md](runtime-sandboxing.md).

## Wasm

The Wasm backend maps direct values and status values to Wasm value types (`i32`, `i64`, `f32`, `f64`) following the scalar-slot rules.
Shared references, mutable references, and caller-allocated result pointers are represented as pointers in linear memory using the selected backend profile.

Parameters are passed to Wasm functions in the order of their definitions.
Caller-allocated return pointers, when needed, are passed before source-level parameters.
For fallible direct-value returns, Wasm uses multi-value results for `(status, value)`.

## Native

To be defined later, possibly per platform.

# Scalar Representation

This section applies once the backend profile is selected.

- All scalars are stored in **little‑endian** format.
- Alignment must be respected.
- Memory is byte-addressable.
- Floating-point values are forbidden to be NaN.

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
- replacement destroys an initialized destination before writing its replacement; and
- final storage destruction invokes the registered Rust drop glue exactly once.

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

> Status: this is the intended long-term ABI layout optimization.
> The current interpreter representation does not yet reorder record fields this way.

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
Compiler IR keeps the semantic identity opaque and symbolic; materializing the 31-bit number and
packing or masking the storage bit are physical ABI-lowering operations.

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

A payloadless case writes only its tag and requires no payload layout witness.

No `Value<V>` witness is needed merely to address a known case payload inside an existing `V`
place. Allocating or moving the complete variant remains a whole-value operation and uses `Value<V>`
when `V` has no static layout at the lowering site.

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
size and alignment. Its interpreter representation as a Rust `Vec<Value>` is not part of the ABI.

Buffer allocation receives `Value::<T>::SIZE` and `Value::<T>::ALIGN` explicitly. Slot-addressing
and element-move intrinsics receive only `Value::<T>::SIZE`: the aligned allocation base and the ABI
rule that type sizes include tail padding already guarantee that each slot is aligned. The boxed
interpreter accepts and ignores this physical layout evidence. Compiled lowering uses it to allocate
aligned storage and calculate slot addresses.

Every layout has a positive alignment and a size divisible by that alignment. For non-zero-sized
types, alignment is therefore no greater than size. Zero-sized types are the exception to that last
inequality—for example, `()` has size 0 and alignment 1—and require no backing allocation.

A buffer allocated with capacity 0 is the one case where the layout arguments are not the element's
own: an empty array literal passes size 0 and alignment 1 whatever `T` is, because a capacity-0
buffer has no slot to address and no storage to align. Lowering must therefore treat a zero-byte
allocation as valid and reclaimable rather than reading the element layout back out of it. Buffers
that later grow are reallocated by `array_ensure_capacity`, which passes the true `Value::<T>`
layout, so no slot is ever addressed with the placeholder.

The interpreter's native `buffer_drop` remains a no-op because the subsequent interpreter storage
discard drops the Rust `Vec`. Compiled lowering replaces that semantic Buffer drop with
`dealloc(buffer.ptr)` followed by clearing the pointer. The runtime exposes pointer-only
deallocation and retains any allocator-specific layout metadata internally; a capacity-0 buffer is
deallocated by the same path as any other. Whole-buffer moves must use the same cleanup when
replacing an existing target, so every allocation is reclaimed exactly once.

# Closures

Ferlium represents all first-class functions uniformly as closures. A closure has two target
words. On Wasm32 it is:

```
{
   code_index: u32,
   env_ptr: u32
}
```

Its size is 8 and its alignment is 4. On ABI-64 the two target words give size 16 and alignment 8.
`Value<F>::SIZE` and `Value<F>::ALIGN` report these values for every function type `F`; neither the
function signature nor its captured environment changes the closure value's own layout.

`code_index` is one closure-implementation identity. On Wasm it selects the closure-compatible
entry used by `call_indirect`. The generated module also associates that same identity with the
operations needed to clone and drop this implementation's environment. This association does not
put several pointers into `code_index`: a backend can, for example, use `code_index` to index the
call table and a parallel metadata table, or dispatch clone/drop through compiler-generated helper
code. The observable contract is only that a closure value provides one identity from which all
three operations can be selected:

- invoke the closure;
- clone its owned environment; and
- drop and deallocate its owned environment.

`env_ptr` is the owning pointer to the closure environment in linear memory. The environment
contains the runtime representations of captured hidden evidence and owned source values. Its
ordered shape is known at the closure construction site, but a generic capture tuple `B` may have
witness-derived size, alignment and field offsets. The environment therefore retains any dynamic
`Value<B>` evidence needed by the closure entry and its clone/drop operations. Statically known
evidence may instead be compiled into those operations.

`env_ptr` is zero exactly when the closure captures neither hidden evidence nor source values. A
non-zero environment pointer owns one allocation:

- construction moves the already-owned source captures into it;
- moving the closure transfers the pointer and clears the source;
- cloning the closure allocates a new environment, copies non-owning hidden evidence and clones the
  owned capture tuple through `Value<B>`;
- dropping the closure drops the owned capture tuple and deallocates the environment exactly once.

Invoking a closure borrows the closure value. It clones the owned capture tuple into a per-call
temporary, passes the temporary captures and stored hidden evidence to the function body, and
drops the temporary after both normal return and language failure. Consequently mutations of
captured values during one invocation do not persist into later invocations. A poisoning sandbox
violation follows the general non-semantic cleanup rules described above.

Every closure-compatible entry accepts `env_ptr` as its first closure-specific parameter, followed
by the parameters required by the standard function ABI. A function that can be materialized as a
first-class value needs such an entry; an ordinary direct-only function does not. A captureless
entry ignores its zero environment pointer. The environment argument can be eliminated only when
the compiler devirtualizes the complete indirect call into a direct call.

## Native

The code-identity representation and dispatch mechanism are target-specific. The closure value
still occupies two target words and follows the ownership contract above.

# Rust structural interoperability

The Rust-native rule above is sufficient when a Rust type is not structurally exposed: Ferlium
stores the real `T` and uses its registered operations. A Rust type intended to be structurally
interchangeable with a Ferlium-defined record or tuple additionally needs a representation
declaration or generated adapter that verifies the Ferlium field order, offsets, size and alignment.
`#[repr(C)]` with fields in Ferlium's canonical order is one possible implementation for records,
but the ABI does not prescribe the source annotation used to establish that contract.

Ferlium variants use case-specific payload offsets and are not C unions. A Rust enum is therefore
not structurally interchangeable merely because its cases have corresponding names and payloads;
it remains an ordinary non-structurally-exposed Rust-native type unless an adapter explicitly
implements the Ferlium variant representation.
