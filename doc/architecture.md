# Architecture

Ferlium is designed to be integrated into existing Rust codebases, web apps through WebAssembly, and in the future target static compilation. Therefore, it is designed with minimal runtime requirements. Essentially, the runtime consists of a small standard library. In particular, type information should not be necessary for running code.

The compiler transforms source code into a parsed abstract syntax tree (AST), desugars it into a source-level AST suitable for type inference, resolves symbols, infers and checks types while emitting typed high-level IR (HIR), performs HIR validation and elaboration, then executes the HIR. A bytecode VM, JIT, or native backend could later replace the current tree interpreter.

## Source Layout

- `compiler/`: compiler orchestration, session state, diagnostics, and source-to-module pipeline code.
- `parser/`: source locations, escape handling, parser helpers, and the LALRPOP grammar.
- `ast/`: parsed and desugared AST definitions, AST visitors, AST utilities, and AST pretty-printing.
- `desugar/`: parsed-AST-to-desugared-AST lowering for syntax conveniences and module-level definitions.
- `types/`: type representation, effects, mutability, type inference, trait solving, coherence, substitutions, visitors, and schemes.
- `hir/`: the typed high-level IR, HIR synthesis helpers, AST-to-HIR emission, borrow checking, dictionary passing, function representation, pattern-match lowering helpers, and runtime values.
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
8. Run borrow checking over HIR.
9. Elaborate dictionaries for trait resolution, record field access, value dispatch, and unresolved argument passing.
10. Execute HIR through the current interpreter.

Future backend work may add bytecode generation and VM execution, or JIT/native code generation.
