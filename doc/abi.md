# Ferlium ABI Specification

This document is draft of Felium ABI for future Ferlium-WASM (and native) interoperability.
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

The ABI presented here is stable across modules and compilation units.

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

# Calling conventions

## Wasm

### Parameters

Parameters are passed to Wasm functions in the order of their definitions.
Scalars are passed directly, while other types are passed as pointers to their data.

### Return values and panic

Each function can have effects, which might be polymorphic and represented by effect variables.
There are two cases:

- **No panic**: function’s effects contain no `Fallible` and no effect variables
- **May panic**: function’s effects contain `Fallible` or some effect variables

Also, functions can return different kinds of values:

- **No value**: `()`
- **Scalar value**: e.g., `Int`, `Float`
- **Caller-allocated value**: bigger types, polymorphic result

The calling convention for return values depends both on the effects and on the representation of the result type:

| May panic? | Return value kind          | ABI return form                                                    | Out-pointer needed? |
| ---------- | -------------------------- | ------------------------------------------------------------------ | ------------------- |
| ❌ **No**  | **No value**               | Returns **`()`** (no wasm result)                                  | ❌ No               |
| ❌ **No**  | **Scalar value**           | Returns the **scalar** directly as a wasm result                   | ❌ No               |
| ❌ **No**  | **Caller-allocated value** | Returns **`()`**; callee **writes result to out-ptr**              | ✔️ Yes              |
| ✔️ **Yes** | **No value**               | Returns **status**                                                 | ❌ No               |
| ✔️ **Yes** | **Scalar value**           | Returns **(status, scalar)** via multi-value                       | ❌ No               |
| ✔️ **Yes** | **Caller-allocated value** | Returns **status**; callee **writes result to out-ptr** on success | ✔️ Yes              |

When a function may panic, success is 0 on success, and non-zero on panic, and holds the error code.

## Native

To be defined later, possibly per platform.

# Scalar Representation

This section applies once the backend profile is selected.

- All scalars are stored in **little‑endian** format.
- Alignment must be respected.
- Memory is byte-addressable.
- Floating-point values are forbidden to be NaN.

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

Tagged unions (sum types) box their payloads to allow for recursive types.

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

Tags are stored as `u32` referring to interned strings within one compilation session.
Binary modules are not compatible across compilation sessions. 

## Payload layout

For each case:

- No payload is treated as unit: size 0, alignment 1
- Payload type follows record/tuple rules

## Variant representation

Payloads are boxed, to allow for recursive types.

```
struct Variant {
    void* payload; // pointer to payload data
    i32 tag;
}
```

This leads to:

* alignment = `max(4, align(void*))`
* size = 8 (32 bit targets) or 16 (64 bit targets)

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

# Strings

Strings in Ferlium are UTF-8 encoded byte arrays with capacity:

```
struct String {
   ptr : *u8,    // pointer to buffer of cap bytes
   len : usize,  // number of bytes currently used (0 <= len <= cap)
   cap : usize,  // total capacity in bytes
}
```

This leads to:

* alignment = 4 (32 bit targets) or 8 (64 bit targets)
* size = 12 (32 bit targets) or 24 (64 bit targets)

## Strings invariants

For any valid string value:

- `ptr` is either:
   - a valid pointer to a buffer of at least `cap` bytes, or
   - an undefined pointer if `cap` == 0.
- The inequality `0 <= len <= cap` holds.
- The first `len` bytes at `ptr` are a well-formed UTF-8 sequence.
- Bytes in the range `[len, cap)` are unspecified and may be uninitialized.
- The string is not NUL-terminated by convention; a '\0' byte is allowed and is treated like any other byte.
- The string is logically mutable:
   - Operations may modify bytes in `[0, len)` or change `len` (within `cap`).
   - If an operation needs more space than `cap`, it may allocate a new buffer, copy contents, free the old one, and update `ptr`, `len`, `cap`.

# Closures

## Wasm32

Ferlium represents all first-class functions uniformly as closures.
A closure is a two-word record:
```
{
   code_index: u32,
   env_ptr: u32
}
```

where `code_index` refers to an entry in the module’s function table and `env_ptr` points into linear memory to the closure’s environment.

The environment is a compiler-generated tuple containing the runtime representations of all variables captured by the function (including dictionaries for typeclass operations).
Each closure’s compiled code always takes the environment pointer as its first argument, followed by the function’s user-level arguments, and returns values using the standard ABI.

The environment’s layout is fully determined at the closure’s definition site and is opaque to callers; invoking a closure is always performed via `call_indirect` using `code_index` and passing `env_ptr` as the first parameter.
An empty environment is represented by setting `env_ptr` to zero.
Hence, when compiling a lambda that is a closure, the compiled code first extracts the values out of the environment, before executing the actual user-written code.
If the lambda is not a closure, the first argument is simply ignored.

Closures may be represented and passed as a single 64-bit word (`i64`), with `code_index` and `env_ptr` packed into the low and high 32 bits respectively, in order to treat closures as scalar values for parameter and return conventions.

In wasm modules, all exported named functions must have two versions:

- a `direct` version, that corresponds to the normal Ferlium function.
- a `closure`-compatible version, that drops their environment pointer argument, and calls the direct version internally.

When using a first-class function locally, if that function does not capture any variables, the compiler may optimise away the environment pointer argument.
When private functions will be added, espace analysis will be used to decide whether they too need the closure-compatible version.

## Native

To be defined later, possibly per platform.

# Rust FFI Guidelines

- Use `#[repr(C)]` for structs matching Ferlium records.
- Declare fields in Ferlium canonical order.
- Use macros like `#[ferlium_record]` to avoid mistakes.
- Use only backend-supported scalar sizes/alignments.
- Variants must use Ferlium tag numbers and payload layout.
