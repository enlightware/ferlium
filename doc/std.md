# Standard Library Design

The standard library consists of Rust-backed modules (`src/std/*.rs`) and the bundled Ferlium prelude (`src/std/prelude/*.fer`).
This document records the design decisions behind its user-facing API and the alternatives that were weighed.
The source and the book remain authoritative for the API itself.

## Iteration

### Protocol

`Iterator::next(&mut Self) -> Option<Item>` is a pull step, and `Seq::iter` produces an iterator from a sequence.
`for x in c` desugars to `iter` and repeated `next`.
The consumers (`fold`, `sum`, `all`, `find`, `minimum`, …) route through `fold` and `iter`.
On arrays, `map`, `filter` and `filter_map` are eager and return arrays; on iterators they are lazy adaptor structs, as are `zip`, `enumerate`, `take`, `skip` and `chain`.

An iterator is an ordinary value.
It owns its source, so `for` traverses a snapshot, and it can be stored, stepped by hand and composed.

### Cost model

Semantically, iteration copies: the iterator owns a copy of the collection, and `next` returns an owned element.
Under mutable value semantics these copies are unobservable while the source stays alive and unchanged, and the optimizer removes them (see [mir-optimization.md](mir-optimization.md)).
`iter` and `next` are small, so once specialized they are inlined.
`for`, `fold` and adaptor pipelines then cost the same as a hand-written index loop, for any element type, including in a function that is itself not inlined.

Copies remain where the iterator's own code is opaque to the caller:

- an iterator or adaptor built by a call that is not inlined owns a copy of its source;
- a `next` that is not inlined returns a copy of each element, as does a `filter_map` callback that is not inlined;
- generic code that stays unspecialized pays both.

Removing these needs interprocedural ownership summaries: an optimization, not an API change.
Mutating the source inside its own loop, or keeping an element beyond it, requires a copy by value semantics.

### Mutation

There is no mutable iteration.
Arrays are updated by index (`for i in 0..len(a) { a[i] = f(a[i]) }`), and new collections are built with `map` and `filter`.
Should in-place updates of maps prove common, std functions taking a callback can provide them without language support.

### Alternatives considered

When every iterated element was still deep-copied, two protocol redesigns were studied:

- **Iteration by projection** ("yield-many"): a subscript yields a place for each element in turn, and the loop body runs inside the accessor's scope.
  A pull step cannot return a place without first-class references, which is why Rust needs lending iterators, but a scoped projection can.
  It would have given zero copies even in unspecialized code, a structural guarantee against mutating a collection while traversing it, and the state-machine lowering that async needs.
  It needed repeated suspension in MIR and Wasm, a new HIR node, a new yield-provenance rule, and adaptor inlining during elaboration, and adaptor chains would no longer be values.
- **Iteration by index**, as Swift's and Hylo's `Collection`: a copyable position and a scoped `element` subscript.
  It needed only subscripts as trait items, and every existing stream had a cheap position.
  But `for` over a stateful iterator would become eager, `for (k, v) in m` would lose its spelling, mutating a collection inside its own loop would stop compiling, and stored positions could go stale as in Swift.

**Decision:** keep `Iterator` and `Seq`.
The copies were a compiler problem, not a protocol problem: after clone elimination, the specialized protocol costs nothing measurable on Wasm, and the remaining copies are confined to opaque calls.
Both alternatives would have bought guarantees at those calls at the price of source breaks and substantial new machinery.

Two lessons came out of this:

- Compare a protocol with a hand-written loop under the optimizer, on the backend that matters.
- A value-returning protocol is compatible with copy-free traversal under value semantics wherever the compiler can prove the source alive and unchanged.

Revisit this if real code often hits the opaque cases above, if generic mutable iteration is needed, or if sources without cheap positions, such as tree traversals, need to be iterated without collecting.
Async is a separate reason to build yield-many's state-machine lowering, independent of copies.
