# Generic instantiation

How a call to a generic function records the way it instantiated that function, and why the record
is kept rather than recovered later.

## What a call site knows

A generic function is compiled once, with its type parameters left as quantified variables and its
trait constraints turned into hidden dictionary parameters. A call site supplies both halves:

- **type arguments** — the type each of the callee's quantifiers stands for at this call;
- **dictionaries** — which impl satisfies each of the callee's constraints at those types.

The second is a consequence of the first. Both are held in `FnInstData`, on the HIR call node.

## Why they are recorded together

They describe one instantiation, and using one without the other produces a callee whose evidence
and whose types disagree. Such a body executes correctly but is not internally consistent: any pass
that acts on the resolved evidence — folding a call the dictionary made direct, say — evaluates it at
the concrete instantiation and then has nowhere type-correct to put the result. Keeping the two in
one structure makes the mistake awkward to write. GHC's Core makes it inexpressible for the same
reason: a call applies types and dictionaries in one breath.

## Why they are recorded rather than recovered

The compiler knows the mapping exactly once, in `TypeScheme::instantiate_with_fresh_vars`, which
allocates a fresh inference variable per quantifier and returns the substitution. Nothing else ever
knows it directly. A later stage can only *recover* it, by structurally matching the callee's generic
signature against the call site's concrete one — work that is redone at every use and needs a matcher
the type system otherwise has no reason to have.

So the substitution is stored at the moment it is created. At that point its values are the fresh
variables; the end-of-inference substitution pass rewrites them into the types unification solved,
by the same walk that already concretizes the dictionary requirements.

This is the mainstream choice: rustc carries `GenericArgs` in the type of the callee operand, and
Swift's SIL carries a `SubstitutionMap` on `apply`.

## The arguments live in the caller's type environment

`ty_args` are written in terms of whatever type variables are in scope *at the call site*, so a
generic function calling another generic function records its own quantifiers rather than concrete
types:

```
fn twice_it<T>(x: T) -> T where T: Num, T: Value { x + x }

fn concrete(n: int) -> int { twice_it(n) }        // records [int]
fn forwarding<U>(y: U) -> U where .. { twice_it(y) }  // records [U]
```

This is what lets instantiation compose. Instantiating `forwarding` at `int` rewrites every type in
its body, including the `[U]` recorded on the inner call, which becomes `[int]` — so a call that was
generic becomes concrete without anything having to reason about nesting. Specialization therefore
proceeds outward-in, each round making the next one's call sites concrete.

Over the standard library the split is roughly 58% of instantiating call sites fully concrete and
42% carrying variables, so the second case is the common one rather than a corner.

## Encoding

Both argument lists are **positional** against the callee's quantifiers: `ty_args[i]` instantiates
`ty_scheme.ty_quantifiers[i]`. Positional rather than a map because the list is canonical and cheaply
hashable, which matters when it becomes a specialization cache key.

`eff_quantifiers` is a set and so has no inherent order; the encoding uses sorted order, which is
what `TypeScheme`'s `Hash` impl already uses, so there is one canonical order rather than two.

A thunk that forwards to a function at that function's own signature records the *identity*
instantiation — every quantifier standing for itself — rather than an empty list, so that the
argument lists are always as long as the quantifier lists.
