# AGENTS.md

## Project Context

Ferlium is a functional scripting language with generics and static typing.
It aims at bringing the convenience of writing of Python, the safety of Rust, and the expressiveness of Haskell.
It achieves so by borrowing the type system from Haskell, the syntax from Rust, and a simple mutable value semantics.

## Preferred Commands
- Run all tests efficiently: `cargo nextest run`
- Validate IDE Lezer grammar: `make validate-grammar` in `playground/`
- Print content of std: `cargo run --example ferlium -- --print-std`

## Workflow Rules
- **IF** you modify the main parser file `src/parser.lalrpop`, **THEN** you must also update the IDE Lezer grammar file `playground/src/language/language.grammar` and validate it.