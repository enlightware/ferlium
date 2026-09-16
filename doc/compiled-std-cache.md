# Compiled standard-library cache

Ferlium caches the standard library's semantic HIR, raw MIR, optimized MIR, and optimized physical MIR
across compiler processes. Each stage is a separate artifact and is loaded only when requested.
This is enabled by the default `std-cache` Cargo feature. Set
`FERLIUM_STD_CACHE_DISABLE` to any value to force the old compile-on-startup path, or set
`FERLIUM_STD_CACHE_DIR` to choose a cache directory. By default the cache lives in
the platform-standard per-user Ferlium cache directory, under `compiled-std` (for example,
`$XDG_CACHE_HOME/ferlium/compiled-std` on Linux).

The filesystem cache is not compiled for `wasm32-unknown-unknown`. Browser hosts compile std once
per Wasm instance and reuse Ferlium's in-memory initial-session state.

The portable DTO and Postcard encoding layer is the separate `std-snapshot` feature. `std-cache`
enables it and adds the native filesystem backend. Snapshot serialization is independent of the
storage backend and filesystem availability.
Snapshot checksum and lineage metadata are likewise available on every target with `std-snapshot`;
only filesystem storage and automatic disk-cache loading are restricted to native hosts.

The cache is compiler-owned internal data, not a stable public format. Compatibility relies on
fingerprints, not manually maintained schema versions. Its header contains a build-generated hash
of every embedded `.fer` std source, a conservative hash of the Rust compiler/runtime sources
(including snapshot schemas), macro sources, dependency manifests/lockfile, compiler identity and
active target/build configuration (including Rust flags), and the exact
sorted sets of canonical native type and callable names. A mismatch, decoding error, missing native
type/callable, or detected invalid type/HIR reference is treated as a cache miss and falls back to
compilation. The format is trusted compiler-owned cache data rather than a hardened untrusted-input
format. Both hashes are part of the filename, allowing worktrees and branches to coexist in the
shared directory.

The file magic identifies the Ferlium cache format, not a particular module. Module IDs and paths
are stored inside the checksummed snapshot data and validated on restoration.

Each MIR stage records its parent's snapshot checksum: semantic HIR → raw MIR → optimized MIR →
physical MIR. The session retains each checksum needed to load the next stage. A stage built
without a published parent is not used to load or publish dependent stages. Invalidating a stage
discards its downstream caches, never its parents. Fresh snapshots are type-reinterned and verified
before atomic publication. Later semantic MIR loads trust checksum-matching compiler-owned bytes
and repeat structural restoration, not whole-corpus MIR verification.

Physical snapshots are valid only for the matching compiler/runtime build and target. They store
physical bodies and native layout/ABI requirements, but no code pointers or Rust type identities.
Loading rebinds native entries from the current runtime, reconstructs evidence catalogs, checks
the native contracts, and repeats physical readiness verification. An incompatibility is a cache
miss. Whole-program resolution remains session-local and is not persisted.

Std optimization is module-local. Its result may depend on std, compiler and target configuration,
all covered by the cache fingerprints, but not on unrelated modules later registered in a session.
Loading cached MIR does not reproduce per-pass std MIR tracing; disable the std cache when tracing
the construction of those artifacts.

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
