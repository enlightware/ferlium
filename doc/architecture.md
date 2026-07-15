# Architecture

Ferlium is designed to be integrated into existing Rust codebases, web apps through WebAssembly, and in the future target static compilation. Therefore, it is designed with minimal runtime requirements. Essentially, the runtime consists of a small standard library. In particular, type information should not be necessary for running code.

The compiler transforms source code into a parsed abstract syntax tree (AST), desugars it into a source-level AST suitable for type inference, resolves symbols, infers and checks types while emitting typed high-level IR (HIR), then elaborates and validates final HIR. Ferlium can execute final HIR directly with its tree-walking interpreter or lower it to SSA and run the SSA reference interpreter. Future machine backends can consume the same SSA form.

## Source Layout

- `compiler/`: compiler orchestration, session state, diagnostics, and source-to-module pipeline code.
- `parser/`: source locations, escape handling, parser helpers, and the LALRPOP grammar.
- `ast/`: parsed and desugared AST definitions, AST visitors, AST utilities, and AST pretty-printing.
- `desugar/`: parsed-AST-to-desugared-AST lowering for syntax conveniences and module-level definitions.
- `types/`: type representation, effects, mutability, type inference, trait solving, coherence, substitutions, visitors, and schemes.
- `hir/`: the typed high-level IR, HIR synthesis helpers, AST-to-HIR emission, borrow checking, dictionary passing, function representation, pattern-match lowering helpers, and runtime values.
- `ssa/`: SSA functions, instructions, values, validation, and the SSA reference interpreter.
- `emit_ssa.rs`: final-HIR-to-SSA lowering.
- `module/`: module identity, paths, imports, module environments, function metadata, trait impl metadata, and symbol lookup.
- `std/`: Rust-backed standard library modules and bundled Ferlium prelude source.
- `ide/`: IDE-facing compiler wrapper, annotations, diagnostics, execution result shaping, signatures, and source index helpers.
- Top-level helpers: small shared utilities such as `containers.rs`, `format.rs`, `graph.rs`, `assert.rs`, and `sync.rs`.

## Compiler Flow

The main phases are:

1. Parse source text into parsed AST.
2. Validate parsed AST features that are not accepted in user code.
3. Desugar parsed AST syntax and module declarations.
4. Resolve symbols and emit typed HIR while collecting type, effect, mutability, and trait constraints. Some HIR decisions, such as local storage ownership and value argument passing, may remain explicitly unresolved.
5. Unify type, effect, and mutability constraints.
6. Resolve deferred local storage decisions from the unified mutability facts, then activate the `Value` constraints required by finalized ownership and take-local semantics.
7. Simplify and default remaining trait constraints, then build final type schemes and hidden dictionary/evidence parameter lists.
8. Elaborate dictionaries, ownership and value dispatch, record field access, and call lifetime plans into final HIR.
9. Validate final-HIR ownership, literal, borrow, place-lifetime, and yield invariants.
10. Execute final HIR through the tree-walking interpreter, or lower it to SSA and execute it through the SSA reference interpreter.

Future backend work may lower SSA to WebAssembly, bytecode, JIT, or native code.

HIR and SSA interpretation use the same `ExecutionLimits` configuration for call depth and fuel.
Their `ReferenceInterpreterLimits` additionally cap entries in the boxed interpreters' shared
evaluation environment. This bounds interpreter storage roots rather than their indirectly-owned
heap allocation and is therefore not presented as a backend-neutral or byte-accurate memory budget.
A limit violation is host-enforced execution cancellation, not a source `Fallible` effect; normal
function ABI and cancellation propagation are separate concerns. If semantic cleanup itself raises
while a failure or cancellation is already unwinding, both reference interpreters hard-abort and
poison the executor as specified in [runtime-sandboxing.md](runtime-sandboxing.md).
A future common memory policy should account for actual runtime allocation independently of backend
representation.
