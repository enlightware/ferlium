# Wasm generation: design decisions

## Borrow immutable literal handles only at known readers

The invocation's static-string table belongs to the instance and stays valid across native calls.
Literal handles passed only to the declared string materialization and literal-append helpers can
therefore be borrowed directly from that table. This includes temporary places initialized once
from a literal and read only within the same block. Other uses keep private copies:
neither an indirect call nor a derived address proves that a handle will remain read-only.
This borrows the immutable handle, while materialized strings still have owned mutable storage.

## Plan scratch locals before emission

For MIR bodies, scratch locals are reserved for the emission paths they need, after dictionary and
subscript selection. A use without a declared requirement panics as an internal compiler error.
They are assigned after value registers, so narrowing scratch reservations does not change which values
cross a projection's suspension boundary. Scratch contents are temporary and are never retained
across a yield.

## Share implementations after lowering

Distinct typed functions can have identical Wasm implementations. Layout queries are one example:
`Value<int>::SIZE` and `Value<int>::ALIGN` both return 4 on Wasm32. Sharing their typed MIR identities
would conflate different contracts. Instead, Wasm emission shares implementations while retaining
semantic function identities, calling-contract metadata and dictionary slots.

Equivalence requires the complete Wasm signature and exact encoded body, including local
declarations. Matching signatures or similar instruction shapes alone cannot establish equivalent
behavior. Exact comparison avoids a separate semantic-equivalence analysis and preserves details
such as the sign of floating-point zero. Sharing runs once all Wasm bodies have been emitted,
covering ordinary functions, generated helpers, thunks and adapters with the same rule.

Function references are compared using canonical callee identities, so sharing a callee can also
make its callers identical. Dependencies are processed before callers; recursive components use
local folding rounds. Distinct recursive graphs are not assumed equivalent merely because their
shapes look alike. This keeps the proof based on exact implementations rather than introducing
semantic or graph-equivalence analysis.

Function indices are compacted only after sharing has settled. Calls, exports and function-table
entries follow the remapping, while dictionary and callable table slots retain their identities.
Source ranges also follow any changes in encoded index width. Debug sections that depend on final
code offsets must be generated after this stage.

## Keep source origins separate from implementation equality

Names and source locations describe an implementation's origins; they do not determine its
behavior. Including them in equality would prevent otherwise valid sharing. Shared
implementations name the first original function in emission order and the number of shared
origins with an ASCII `xN` suffix; unshared adapters retain their descriptive names. Source maps combine
the original locations and inline chains. Different region boundaries are split so lookup still
sees disjoint or identical byte ranges.

This preserves source navigation and makes sharing independent of whether debug information is
requested. It does not recover which semantic function a particular runtime invocation came
through; multiple source origins are not distinct runtime stack frames.
