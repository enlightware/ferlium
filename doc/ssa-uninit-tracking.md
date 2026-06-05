# SSA interpreter: uninitialized-storage and drop tracking

How the SSA interpreter decides what storage is live, so it runs each `Value::drop` exactly once —
and the one invariant that makes the empty (zero-field) aggregate sound.

## Why the SSA interpreter tracks more than the HIR one

Both interpreters share the same runtime `Value` representation, but they reach liveness very
differently.

The HIR interpreter manipulates **whole values**. A local holds either a complete value or nothing;
a move or drop drains the *entire* local to `Value::Uninit`. Liveness is therefore a flat question —
"is this slot exactly `Uninit`?" — and that single check decides every drop.

The SSA interpreter models a **memory-explicit** IR (`alloca` / `project` / `store` / `load` /
`move` / `drop`; see `doc/ssa-ir.md` §5), the shape an eventual code generator targets. It exists to
validate that lowering, so it models how the IR touches storage: a single aggregate allocation is
built, moved, and dropped **one field at a time** (a field is drained to `Uninit` by `move`, a
non-trivial `load`, or `drop`; a `memcpy` preserves its source). Consequently a slot can sit in a
*mixed* state — some fields live, some already gone — that no flat check can describe. For example,
moving each field out of a struct individually leaves its storage with every field `Uninit` but the
aggregate still structurally present; the local's scope-exit cleanup must recognise that as dead and
skip it, rather than dropping already-moved fields.

So liveness in SSA is necessarily **structural and recursive**: it is read off the field leaves, not
off the slot as a whole. Everything below follows from that.

## The husk rule

A slot that carries nothing left to drop is a *husk*. The rule is purely structural — there is no
separate drop-flag bitmap:

- a flat `Uninit` is a husk;
- a non-empty aggregate is a husk iff all its fields are (recursively) husks;
- anything else is live.

A drop checks this rule, runs the user's `Value::drop` only on a live slot, and then leaves the
drained storage as a husk *skeleton* of the same shape — so it stays field-addressable if the same
storage is later reinitialised in place. That skeleton is itself a non-flat all-`Uninit` aggregate,
which is exactly why the liveness check has to look inside.

## The empty-aggregate invariant

A zero-field aggregate (`struct E {}`) is the one shape the structural rule cannot classify on its
own: with no field to read liveness from, "all fields are husks" is *vacuously true*, so an empty
aggregate would always look dead — and a constructed `E {}` would never be dropped.

The fix is a single representation choice, matching what the HIR interpreter already does:

> **A *live* empty aggregate is the empty tuple. A *husk* empty aggregate is flat `Uninit`.**

This is sound **as long as no husk is ever represented as an empty tuple** — i.e. every operation
that produces a husk collapses a zero-field aggregate to flat `Uninit`. Given that, the empty tuple
can only have come from construction, so the liveness check treats it as live.

Rather than re-derive that rule at each site (and eventually forget it somewhere), the husk-producing
operations funnel empties through **one** chokepoint that collapses them, and the single liveness
check carries the dual half (an empty tuple is live). The invariant then holds by construction: a
husk-builder *cannot* emit an empty tuple, so a future value-walker that joins the set inherits the
guarantee instead of having to remember a special case.

Construction is the mirror image: because there is no field store to mark empty storage live, the
emitter writes the empty-tuple marker explicitly when it builds an `E {}`.

## Unit `()` is not an empty aggregate

Unit (`()`) looks empty but is a different beast. A *value* of type `()` is a `Native(())` primitive,
**not** the empty tuple `Tuple([])` — they are distinct runtime representations of distinct types
(`()` the primitive vs. a zero-field `struct`/record), and both interpreters agree (`Value::unit()`
is `Native::<()>(())`). A `Native(())` is a live scalar: it is never a husk (only `Uninit` and
all-husk non-empty aggregates are), so it needs none of the empty-aggregate machinery above.

It does, however, share the same *construction* hazard for the same reason — there is no sub-field to
mark its storage live. A standalone unit is handled by making it phantom: a `()` local/return is the
non-dereferenceable unit place (`&()`, `UNIT_PLACE`), and `is_unit_place` shorts every `load`/`store`,
so its storage is never touched or read. But a unit that is a **leaf of a real aggregate** — e.g. the
`()` element of the `((),)` payload of `Continue(())` — sits in genuine, addressable storage that
*must* hold a live `Native(())`; left `Uninit`, a later read/clone/drop of that leaf (e.g. matching
`Continue(v)`, or `acc = value`) reads uninitialized storage and panics.

The rule is therefore the dual of the empty-aggregate one, but with the unit scalar as the live
marker rather than the empty tuple:

> **Lowering a `()` immediate into a destination stores a live `Native(())`** — exactly like any
> other primitive. (A store into the phantom unit place is discarded, so standalone unit stays free.)

This is uniform, not a special case: `()` flows through the same immediate-lowering path as `bool`
and `int`, so a unit leaf is marked live by the same store that would mark an `int` leaf. The variant
shell is built with an `Uninit` payload and the leaf store grows the skeleton in place
(`grow_value_to_path`), yielding `raw_variant(tag, Native(()))` - identical to the HIR interpreter's
`unit_variant`.

## Where this lives

- `src/ssa/interpreter.rs` — the liveness check, the husk skeleton builders, and the `aggregate_husk`
  chokepoint, with unit tests pinning the empty case; the `UNIT_PLACE` sentinel and `is_unit_place`
  short-circuit that keep a standalone `()` phantom.
- `src/emit_ssa.rs` — explicit construction of the live empty-aggregate marker, and the uniform
  immediate-lowering path (`K::Immediate`) that stores a live `Native(())` for unit leaves.
- `tests/language/value.rs` — end-to-end drop-count tests for empty structs (owned, reassigned,
  moved, as a record field, and the unconstructed case that must *not* drop).
