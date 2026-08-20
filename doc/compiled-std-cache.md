# Compiled standard-library cache

Ferlium caches the expensive Ferlium-source portion of the compiled standard library across
compiler processes. This is enabled by the default `std-cache` Cargo feature. Set
`FERLIUM_STD_CACHE_DISABLE` to any value to force the old compile-on-startup path, or set
`FERLIUM_STD_CACHE_DIR` to choose a cache directory. By default the cache lives in
the platform-standard per-user Ferlium cache directory, under `compiled-std` (for example,
`$XDG_CACHE_HOME/ferlium/compiled-std` on Linux).

The filesystem cache is not compiled for `wasm32-unknown-unknown`. Browser hosts compile std once
per Wasm instance and reuse Ferlium's existing in-memory initial-session state; they do not
currently persist the snapshot across page loads.

The portable DTO and Postcard encoding layer is the separate `std-snapshot` feature. `std-cache`
enables it and adds the native filesystem backend. This separation leaves room for browser storage
without coupling snapshot serialization to filesystem availability.

The cache is compiler-owned internal data, not a stable public format. Its header contains a
numeric schema version, a build-generated hash of every embedded `.fer` std source, a conservative
hash of the Rust compiler/runtime sources and active target/build configuration, and the exact
sorted sets of canonical native type and callable names. A mismatch, decoding error, missing native
type/callable, or detected invalid type/HIR reference is treated as a cache miss and falls back to
compilation. The format is trusted compiler-owned cache data rather than a hardened untrusted-input
format. Both hashes are part of the filename, allowing worktrees and branches to coexist in the
shared directory.

## Native/source loading order

Std construction historically interleaves native registration with three Ferlium-source
compilations. Loading preserves that ordering explicitly:

1. Rust registers the initial native types, traits, functions, and implementations.
2. The cached trait-declaration checkpoint is applied.
3. Rust registers the native operations that depend on those traits.
4. The cached core-language checkpoint is applied.
5. Rust registers the native operations that depend on source-declared types such as `Array` and
   `DataValue`.
6. The cached serialization checkpoint is applied.

Native trait objects and function pointers are never serialized. Native types are represented by
qualified stable names plus type arguments. Native functions receive their canonical name when
inserted into a module. Source functions store portable HIR entry IDs; compiler-generated
structural addressors store their field index.

The type snapshot is a graph of structural nodes. All nodes are re-interned in one operation, so
forward references and mutually recursive strongly connected components are restored correctly.
Strings are stored as owned UTF-8 data and re-interned on load. Native literals have explicit
portable codecs.

## Process coordination

Readers first try the final cache file. On a miss, processes contend for an OS-backed exclusive
lock on a persistent lock file while continuing to retry the final file. The kernel releases lock
ownership if a process exits, so crash recovery does not depend on deleting stale sentinel files.
The writer double-checks after acquiring the lock, compiles once, writes a process-unique temporary
file, flushes it, and atomically renames it into place. Freshly encoded bytes must decode and restore
successfully before publication. An invalid existing file is removed; a deterministic capture or
restore failure records a fingerprint-specific negative marker so subsequent processes compile std
directly instead of repeatedly attempting the same unusable cache. Cache IO is never fatal to
compiler startup.

Snapshot DTOs and reconstruction code live under `src/compiler/snapshot/`; runtime compiler data
structures contain only small provenance or access changes needed by that boundary.
