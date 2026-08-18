# Architecture

Ferlium is designed to be integrated into existing Rust codebases, web apps through WebAssembly, and in the future target static compilation. Therefore, it is designed with minimal runtime requirements. Essentially, the runtime consists of a small standard library. In particular, type information should not be necessary for running code.

The compiler transforms source code into a parsed abstract syntax tree (AST), desugars it into a source-level AST suitable for type inference, resolves symbols, infers and checks types while emitting typed high-level IR (HIR), then elaborates and validates final HIR. Ferlium can execute final HIR directly with its tree-walking interpreter or lower it to MIR and run the MIR reference interpreter. Future machine backends can consume the same MIR form.

## Source Layout

- `compiler/`: compiler orchestration, session state, diagnostics, and source-to-module pipeline code.
- `parser/`: source locations, escape handling, parser helpers, and the LALRPOP grammar.
- `ast/`: parsed and desugared AST definitions, AST visitors, AST utilities, and AST pretty-printing.
- `desugar/`: parsed-AST-to-desugared-AST lowering for syntax conveniences and module-level definitions.
- `types/`: type representation, effects, mutability, type inference, trait solving, coherence, substitutions, visitors, and schemes.
- `hir/`: the typed high-level IR, HIR synthesis helpers, AST-to-HIR emission, borrow checking, dictionary passing, function representation, pattern-match lowering helpers, and runtime values.
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

Future backend work may lower MIR to WebAssembly, bytecode, JIT, or native code.

Every compilation attempt stores severity-tagged source diagnostics on its module entry. Errors make
the attempt fail; warnings remain available through `ModuleInfo::diagnostics` on a successful
module. IDE compilation reports both and keep execution enabled when only warnings are present.
Replacing a compiled module revision marks its transitive consumers stale. A successful replacement
cascade-recompiles source-backed consumers against the new revision; a failed replacement leaves
them stale rather than allowing code compiled against different revisions to execute together.

HIR and MIR interpretation share `ExecutionLimits`; their boxed reference implementations add an
environment-cell guard. Runtime failure and poisoning semantics are specified in
[runtime-sandboxing.md](runtime-sandboxing.md), while the distinction between that guard and a real
memory quota is specified in [runtime-memory-limits.md](runtime-memory-limits.md).
