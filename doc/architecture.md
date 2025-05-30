# Architecture

Ferlium is designed to be integrated into existing Rust codebase, in web pages through WebAssembly, or eventually for static compilation. Therefore, it is designed with minimal runtime requirements. Essentially, the runtime consists of a small standard library. In particular, type information should not be necessary for running code.

Currently, Ferlium transforms the source code into an abstract syntax tree (AST), does some work on this tree, and then outputs a tree-based intermediate representation (IR), on which the execution happens. Alternatively, a just-in-time compiler could be used to do the execution.

## Compiler

The following phases happen in the compiler:

- Source code parsing
  - Lexing
  - Parsing and AST generation
- AST desugaring
  - Minimalist symbol resolution
  - String formatting desugaring
  - Module call graph extraction
- AST to typed IR conversion
  - Complete symbol resolution
  - Type and passing strategy inference
  - ADT desugaring
  - IR generation
- Borrow checking on IR
- Dictionary elaboration (record field access and trait resolution) on IR
- IR optimisation 🚧
- IR execution.

In the future, to support async methods, we will do:
- Bytecode generation 🚧
- Code execution in VM 🚧

or:
- JIT native code generation
- Native code execution