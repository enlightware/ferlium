# Architecture

Painturscript is designed to be integrated into existing Rust codebase, in web pages through WebAssembly, or eventually for static compilation. Therefore, it is designed with minimal runtime requirements. Essentially, the runtime consists of a small standard library. In particular, type information should not be necessary for running code.

Currently, Painturscript transforms the source code into an abstract syntax tree (AST), does some work on this tree, and then outputs a tree-based intermediate representation (IR), on which the executation happens. Alternatively, a just-in-time compiler could be used to do the execution.

## Compiler

The following phases (will 🚧) happen in the compiler:

- Source code parsing
  - Lexing
  - Parsing and AST generation
- Analysis of the AST
  - Symbol resolution
  - Type checking and inference
  - ADT desugaring 🚧
  - IR generation
- IR optimisation 🚧
- IR execution.

In the future, to support async methods, we will do:
- Bytecode generation 🚧
- Code execution in VM 🚧

or:
- JIT native code generation
- Native code execution