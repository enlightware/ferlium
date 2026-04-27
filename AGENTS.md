# AGENTS.md

## Project Context

Ferlium is a functional scripting language with generics and static typing.
It aims at bringing the convenience of writing of Python, the safety of Rust, and the expressiveness of Haskell.
It achieves so by borrowing the type system from Haskell, the syntax from Rust, and a simple mutable value semantics.

## Preferred Commands
- Run all tests efficiently: `cargo nextest run`
- Run the Rust linter: `cargo clippy`
- Validate IDE Lezer grammar: `make validate-grammar` in `playground/`
- Print content of std: `cargo run --example ferlium -- --print-std`
- Compile and run an expression: `echo "1 + 1" | cargo run --example ferlium` where `1 + 1 ` is your expression.

## Workflow Rules
- **IF** you modify the main parser file `src/parser.lalrpop`, **THEN** you must also update the IDE Lezer grammar file `playground/src/language/language.grammar` and validate it.
- **IF** we agree to remove a feature, **THEN** you must **NOT** add a unit test to make sure that this feature is removed.