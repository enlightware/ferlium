# Architecture

Ferlium is designed to be integrated into existing Rust codebases, web apps through WebAssembly, and in the future target static compilation. Therefore, it is designed with minimal runtime requirements. Essentially, the runtime consists of a small standard library. In particular, type information should not be necessary for running code.

The compiler transforms source code into an abstract syntax tree (AST), desugars it, resolves and checks types, emits a typed high-level IR (HIR), performs HIR validation and elaboration, then executes the HIR. A bytecode VM, JIT, or native backend could later replace the current tree interpreter.

## Source Layout

- `compiler/`: compiler orchestration, session state, diagnostics, and source-to-module pipeline code.
- `parser/`: source locations, escape handling, parser helpers, AST definitions, and the LALRPOP grammar.
- `desugar/`: AST-to-desugared-AST lowering for syntax conveniences and module-level definitions.
- `types/`: type representation, effects, mutability, type inference, trait solving, coherence, substitutions, visitors, and schemes.
- `hir/`: the typed high-level IR, HIR synthesis helpers, AST-to-HIR emission, borrow checking, dictionary passing, function representation, pattern-match lowering helpers, and runtime values.
- `module/`: module identity, paths, imports, module environments, function metadata, trait impl metadata, and symbol lookup.
- `std/`: Rust-backed standard library modules and bundled Ferlium prelude source.
- `ide/`: IDE-facing compiler wrapper, annotations, error shaping, and source index helpers.
- Top-level helpers: small shared utilities such as `containers.rs`, `format.rs`, `graph.rs`, `assert.rs`, and `sync.rs`.

## Compiler Flow

The main phases are:

1. Parse source text into AST.
2. Desugar AST syntax and module declarations.
3. Resolve symbols and infer types, effects, mutability, and passing strategy.
4. Emit typed HIR for modules and optional top-level expressions.
5. Run borrow checking over HIR.
6. Elaborate dictionaries for trait resolution and record field access.
7. Execute HIR through the current interpreter.

Future backend work may add bytecode generation and VM execution, or JIT/native code generation.

## Future Splits

The last layout refactor kept large files intact. Good candidates for later splits are:

- `src/hir/emit_ir.rs`
- `src/compiler/error.rs`
- `src/parser/ast.rs`
- `src/types/type.rs`
- `src/module/mod.rs`
- `src/ide/mod.rs`
