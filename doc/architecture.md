# Architecture

Painturscript is designed to be integrated into existing Rust codebase, in web pages through WebAssembly, or eventually for static compilation. Therefore, it is designed with minimal runtime requirements. Essentially, the runtime consists of a small standard library. In particular, type information should not be necessary for running code.

Currently, Painturscript transforms the source code into an abstract syntax tree (AST), does some work on this tree, and then outputs a tree-based intermediate representation (IR), on which the executation happens. Alternatively, a just-in-time compiler could be used to do the execution.

## Compiler

The following phases (will 🚧) happen in the compiler:

- Lexing and parsing, the result is the AST.
- Type checking and inference 🚧
- ADT desugaring 🚧
- Optimisation 🚧
- Code generation, the result is IR.
- IR execution.
