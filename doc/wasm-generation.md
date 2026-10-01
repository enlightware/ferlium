# Wasm generation: design decisions

## Share implementations after lowering

Distinct typed functions can have identical Wasm implementations. Layout queries are one example:
`Value<int>::SIZE` and `Value<int>::ALIGN` both return 4 on Wasm32. Sharing their typed MIR identities
would conflate different contracts. Instead, Wasm emission shares implementations while retaining
semantic function identities, calling-contract metadata and dictionary slots.

Equivalence requires the complete Wasm signature and exact encoded body, including local
declarations. Matching signatures or similar instruction shapes alone cannot establish equivalent
behavior. Exact comparison avoids a separate semantic-equivalence analysis and preserves details
such as the sign of floating-point zero. Current sharing is restricted to eligible generated
helpers and dictionary adapters.

Helpers are shared before dictionary adapters. Canonical helper indices can make adapters
identical even when they originally called different functions. This ordering captures that
opportunity without iterative deduplication or rewriting already encoded call indices. Eligible
direct helpers do not depend on other defined-function indices, so their encoding remains valid
when the function table is compacted.

## Keep source origins separate from implementation equality

Names and source locations describe an implementation's origins; they do not determine its
behavior. Including them in equality would prevent otherwise valid sharing. Shared generated
implementations therefore identify a canonical representative and the number of shared origins
in their generated names; unshared adapters retain their descriptive names. Source maps combine
the original locations and inline chains. Different region boundaries are split so lookup still
sees disjoint or identical byte ranges.

This preserves source navigation and makes sharing independent of whether debug information is
requested. It does not recover which semantic function a particular runtime invocation came
through; multiple source origins are not distinct runtime stack frames.
