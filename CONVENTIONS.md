# Coding Guidelines

Our conventions are based on the [Swift API Design Guidelines](https://www.swift.org/documentation/api-design-guidelines/) except for Rust.
This document only describes guidelines that are not covered there.

## Documentation

Documentation enables local reasoning - it's a shortcut for understanding so readers can avoid looking up implementation
or usages to infer meaning.

- Every declaration outside a function body must have a documentation comment that describes its contract.
  - Start with a summary sentence fragment.
    - Describe what a function or method does and what it returns.
    - Describe what a property or type is.
    - Separate the fragment from any additional documentation with a blank line and end it with a period.

  - Preconditions, postconditions and invariants obviously implied by the summary need not be explicitly documented.

  - Declarations that fulfill protocol requirements are exempted when nothing useful can be added to the documentation
    of the protocol requirement itself.

- Document the performance of every operation that doesn't execute in constant time and space, unless it's obvious from
  the summary.
- Test cases need not be documented, but should have a descriptive function name.

- Phrasing conventions:
  - Omit needless words: don't repeat the receiver's type, don't write `the`, `given`, `representing`, `of self`,
    `of the current object` when context makes these obvious.
  - Use `iff` instead of `if` where applicable.
  - Use `` `true` iff ...`` rather than `Whether ...`
  - Use `<...>, if any.` for optional values where the absence reason is obvious. Otherwise:
    `<...> if <condition>, nil otherwise.`
  - Document preconditions with `- Requires:`. If multiple preconditions apply, use a markdown list below `- Requires:`.
  - Avoid words like “describing,” “representing,” “record” (as a noun) etc, which are redundant with the fact that it is a type.
  - Just talk about the thing, not its ID when practical.
- Conformance implementations are exempt from documentation when nothing useful can be added beyond the protocol
  requirement itself.
- Test cases don't need to be documented, but should have a descriptive function name.
- For types, the summary should say what the type *is*. For functions and subscripts, it should say what they *do* (e.g. returns, yields ...).
- Describe if there is a significance in the element order of an array.

## Contracts

- Create the strictest contracts possible.
- A precondition must be something that is practically possible and efficient for a client to ensure, and that ensuring it often ends up being by construction. If the API author can reasonably predict that a check will be needed every time, well, it's not just a problem of preconditions; they have likely designed the wrong API.
- Preconditions and postconditions are relationships between components - think in terms of what the caller must provide
  and what the callee guarantees in return.
- Contract evolution: you may safely weaken preconditions and strengthen postconditions. The reverse breaks clients, so
  you must inspect all call sites before introducing the change.
- When a contract seems too strict to use correctly without accidentally breaking preconditions, you can either relax
  the preconditions (e.g. `demand_module(name:)` - gets or creates the module if it doesn't exist yet) or report an
  error/return an optional (e.g. `my_hashmap[key]` - returns nil if key is not found).

## Errors

Distinguish bugs from runtime errors:

- **Bug**: a programming mistake. Stop before more damage is done, using `panic`.
- **Runtime error**: postconditions can't be met despite correct usage. Respond by returning an optional/result.

## Safety

- When using an unsafe or unchecked/unsafe construct, include a comment that justifies the need and explains why it's safe.

## Algorithms

- Prefer named algorithms over inline loops. A loop is a mechanism; a named algorithm is a statement of intent.
- When a suitable algorithm doesn't exist, create one as an extension on the appropriate type with an extension trait) rather than inlining the loop at the call site.
- Structure data so efficient algorithms become possible (e.g. storing something in an ordered collection for binary
  search, or storing in a hashmap for O(1) lookup).

## Types

- Use strong types to encode invariants. If a value can only be valid in certain states, make invalid states
  unrepresentable.
- Every instance of a type should have exactly one clearly-defined value, expressed in terms of its operations.
- Keep the efficient basis of a type small and well-documented. All other operations should be derivable from it as
  `extension`s.
- Prefer value types.
- Avoid capturing or returning references to avoid lifetime complications.

## Naming and API design

- Name mutating methods with imperative verb phrases; name nonmutating variants with past participle or `ing` forms.
- No abbreviations in APIs unless universally known (e.g. `URL`, `ID`).
- Don't include the type in a binding's name.
- If the type is too weak, a qualified argument name can help (e.g. `f(output_directory: URL)`), but prefer making the
  type more strict to capture the invariants (e.g. `f(output: DirectoryURL)`).
- Single-letter names are fine in small scopes: `l`/`r` for binary operators, `n` for a syntax node, `m` for a module,
  `i`/`j` for indices.
- When naming a collection of objects, use a plural form (even in case of short names): `files`, `xs`, `ms`.
- Add explicit access specifiers to declarations, hiding as much as possible, unless there is a good reason to expose something. Exposing previously private details should be discussed during reviews.

## Testing

- All new code should be covered by tests.
- Tests should exercise the contract: verify postconditions under valid preconditions.
- If possible, add death tests for verifying that precondition violations
  uphold safety by crashing correctly on precondition violations.

## Formatting

- Indent with 4 spaces.
- Use the Rust-style `snake_case` style for identifiers, `UpperCamelCase` for types.
- Add blank lines inside type, extension, and enum declarations - leave one empty line after the opening brace and
  before the closing brace.
- Use single-expression function bodies over explicit return statements where possible.
- Avoid calling methods on the result of a function applied with trailing closure syntax:
  ```swift
  array.first { (e) in
    ...
  }.doSomething() // discouraged
  ```

- General guideline for declaration order:
  - nested types and aliases
  - static properties
  - member properties
  - initializers
  - computed properties
  - methods
  - static methods
