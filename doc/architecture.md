# Architecture

Ferlium is designed to be integrated into existing Rust codebases, web apps through WebAssembly, and in the future target static compilation. Therefore, it is designed with minimal runtime requirements. Essentially, the runtime consists of a small standard library. In particular, type information should not be necessary for running code.

The compiler parses source into an abstract syntax tree (AST), desugars it, and emits typed
high-level IR (HIR) while resolving symbols and checking types. Ferlium can execute final HIR with
its tree-walking interpreter or lower it to MIR for the MIR reference interpreter. Future machine
backends consume the backend-ready physical MIR stage specified in [mir-ir.md](mir-ir.md).

## Compiled runtime topology

Compiled execution uses one generated module for all Ferlium modules in a `CompilerSession`.
Independent compilation and dynamic linking of Ferlium modules are outside the current design.
Physical lowering processes each source module separately: every result is a relocatable
function table with dictionary and subscript catalogs. A target-independent assembly step creates a
resolved whole-program view over the unchanged module artifacts. It validates their imports and
interns referenced static evidence before an interpreter or machine backend executes them. Wasm,
Cranelift, and other machine backends assign their own target indexes and addresses later.

In the browser, the Rust runtime and generated Ferlium code are separate Wasm instances sharing
one linear memory supplied by the runtime:

```text
Rust runtime                            generated Ferlium module
------------                            -------------------------
shared memory  -----------------------> import memory
allocator      -----------------------> import alloc/realloc/dealloc
native code    -----------------------> import native C entries
diagnostics    -----------------------> import abort/reporting functions
                                         export module entrypoints
```

The loader resolves registered native C entries from the Rust instance's function table and
supplies them as direct function imports. JavaScript participates in linking, not in forwarding
each native call. Table indexes are instance-local; compiler function identities remain symbolic.

The compiled boundary is specified in [abi.md](abi.md). Memory accounting and reclamation are
specified in [runtime-memory-limits.md](runtime-memory-limits.md) and
[runtime-sandboxing.md](runtime-sandboxing.md). Native JIT execution uses the same physical MIR
lowering with native pointers and runtime wrappers.

## Source Layout

- `compiler/`: compiler orchestration, session state, diagnostics, and source-to-module pipeline code.
- `parser/`: source locations, escape handling, parser helpers, and the LALRPOP grammar.
- `ast/`: parsed and desugared AST definitions, AST visitors, AST utilities, and AST pretty-printing.
- `desugar/`: parsed-AST-to-desugared-AST lowering for syntax conveniences and module-level definitions.
- `types/`: type representation, effects, mutability, type inference, trait solving, coherence, substitutions, visitors, and schemes.
- `hir/`: the typed high-level IR, its tree-walking interpreter, HIR synthesis helpers, AST-to-HIR emission, borrow checking, dictionary passing, function representation, pattern-match lowering helpers, and runtime values.
- `eval/`: shared boxed storage, native and intrinsic call boundaries, and execution-domain limits and poisoning.
- `mir/`: the typed middle-level IR, including canonical functions, the construction-only builder,
  operations, terminators, values, verification, rewriting passes, and the MIR reference
  interpreter.
- `emit_mir.rs`: final-HIR-to-MIR lowering.
- `module/`: module identity, paths, imports, module environments, function metadata, trait impl metadata, and symbol lookup.
- `std/`: Rust-backed standard library modules and bundled Ferlium prelude source.
- `ide/`: IDE-facing compiler wrapper, annotations, diagnostics, execution result shaping, signatures, and source index helpers.
- Top-level helpers: small shared utilities such as `containers.rs`, `format.rs`, `graph.rs`, `assert.rs`, and `sync.rs`.

## Compiler Flow

The main phases are:

1. Parse source text into parsed AST.
2. Validate parsed AST features that are not accepted in user code.
3. Desugar parsed AST syntax and module declarations.
4. Resolve symbols and emit typed HIR while collecting type, effect, mutability, and trait constraints. Definite unreachable suffixes are reported as warnings and omitted without constraining inference. Source lints, such as needless returns in function-tail position, are collected alongside those warnings. Some HIR decisions, such as local storage ownership and value argument passing, may remain explicitly unresolved.
5. Unify type, effect, and mutability constraints.
6. Resolve deferred local storage decisions from the unified mutability facts, then activate the `Value` constraints required by finalized ownership and take-local semantics.
7. Simplify and default remaining trait constraints, then build final type schemes and hidden dictionary/evidence parameter lists.
8. Elaborate dictionaries, ownership and value dispatch, record field access, and call lifetime plans into final HIR.
9. Validate final-HIR ownership, literal, borrow, place-lifetime, and yield invariants.
10. Execute final HIR through the tree-walking interpreter, or lower it to MIR and execute it through the MIR reference interpreter. MIR execution optionally runs rewriting passes first, selected per session through `MirOptimization`; optimized bodies are stored beside the raw ones, so enabling optimization never changes what another session executes.

MIR's structure and invariants are specified in [mir-ir.md](mir-ir.md); the rewriting passes, the
order they run in, and the rules deciding where a pass belongs are in
[mir-optimization.md](mir-optimization.md).

Physical preparation lowers each module's optimized MIR to backend-ready physical MIR and resolves
the module dependency closure. The checked physical interpreter validates execution over ABI-layout
storage before the same physical MIR is consumed by machine-code backends.

Every compilation attempt stores severity-tagged source diagnostics on its module entry. Errors make
the attempt fail; warnings remain available through `ModuleInfo::diagnostics` on a successful
module. IDE compilation reports both and keep execution enabled when only warnings are present.
Replacing a compiled module revision marks its transitive consumers stale. A successful replacement
cascade-recompiles source-backed consumers against the new revision; a failed replacement leaves
them stale rather than allowing code compiled against different revisions to execute together.

The boxed HIR and MIR interpreters share storage, native adapters, and Buffer intrinsics, but
execute script calls in their own IR, including implicit capture cloning and destruction.
Each interpreter owns its frame state; a yielded HIR accessor retains its frame until resumed
or abandoned. Each interpreter dispatches its script calls; the shared runtime dispatches only
native and intrinsic calls. Call boundaries return a value or runtime error, not HIR control transfers.
HIR and MIR interpretation share `ExecutionLimits`; their boxed reference implementations add an
environment-cell guard. Runtime failure and poisoning semantics are specified in
[runtime-sandboxing.md](runtime-sandboxing.md), while the distinction between that guard and a real
memory quota is specified in [runtime-memory-limits.md](runtime-memory-limits.md).
