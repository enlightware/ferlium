# Wasm generation: design decisions

## Borrow immutable literal handles only at known readers

The invocation's static-string table belongs to the instance and stays valid across native calls.
Literal handles passed only to the declared string materialization and literal-append helpers can
therefore be borrowed directly from that table. This includes temporary places initialized once
from a literal and read only within the same block. Other uses keep private copies:
neither an indirect call nor a derived address proves that a handle will remain read-only.
This borrows the immutable handle, while materialized strings still have owned mutable storage.

## Rematerialize primitive literals

Primitive scalar places with one literal store dominating all reads and no exposed address emit
immediate literals; pointer, tag and aggregate representations retain existing rules. Repeated
`f64` literals can cost more bytes than local reads.

## Plan scratch locals before emission

For MIR bodies, scratch locals are reserved for the emission paths they may need, after dictionary and
subscript selection. A use without a declared requirement panics as an internal compiler error.
They are assigned after value registers, so narrowing scratch reservations does not change which values
cross a projection's suspension boundary. Scratch contents are temporary and are never retained
across a yield.

## Keep interpreter provenance separate from Wasm uses

Indexed physical addresses retain a logical index for interpreter provenance alongside their byte
offset. Unboxed interpreter storage still tracks element identity: distinct zero-sized elements can
have the same byte offset. Wasm uses only the byte address: the logical index does not expose
storage or prevent stackification at a real consumer. Scalar loads used only to supply that index
can be omitted, provided their removal does not discard deferred source work. Other producers retain
their effects and ownership work. The shared MIR keeps the logical index.

## Keep single-use addresses on the stack

Expression planning defers single-use addresses to memory operations and tag reads when ordering
permits and the consumer evaluates each address once. Materialized pointers used elsewhere retain
ordinary scalar planning. Literal aggregate initialization, selected method stores, aggregate
comparisons and witnessed moves retain address locals because they can reread an address or call
out before consuming it.

## Keep terminal scalar results on the stack

Infallible direct scalar returns need no output local when every use of the return place is a
supported final writer immediately before a normal return. Each writer leaves its result on the
operand stack, where it survives the existing epilogue. Other return-place uses retain ordinary
storage.

## Expand small copies without changing overlap behavior

Multi-chunk expansion is limited to fixed 12- and 16-byte copies; smaller single-chunk copies
remain in the peephole. Expansion happens during body emission, where storage and address locals
are still known. Fixed-layout replacement uses this same policy for its three copies, retaining
the exchange temporary and copy order.

Fixed-size copies can use scalar loads and stores, but must read every source chunk before any write
because valid source and destination ranges may overlap. Known frame or local bases reuse memory
offsets, including static field projections. Other bases are evaluated once and use reusable scratch
locals. Valid Ferlium copies are in bounds; partial destination contents after an invalid memory
access are not part of the language contract.

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

## Lower known primitive operations to intrinsics

Concrete builtin operations on primitive types can lower directly to Wasm instructions.
The known-callee registry establishes their identity independently of source or generated names.
Inline lowering preserves Ferlium semantics wherever they differ from Wasm instructions.
Other implementations and unresolved indirect calls retain the ordinary call path.
