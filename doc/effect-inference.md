# Effect inference

How the compiler infers effects: the shape of effect rows, how values relate their effects, how
constraints are solved, and how a solution is published in a type scheme.

## Effect rows

An effect row is a set of primitive effects (`read`, `write`, `fallible`) and at most one effect
variable; `()` is the pure row. A row with two variables is not a type: a declaration naming two
effect variables in one row is rejected, and so is a function whose effects would combine two
declared effect variables (`fn both<! A, B>(f: () -> int ! A, g: () -> int ! B) { f(); g() }`); such
declarations share one effect parameter instead. This is Koka's row shape, but function values are
related by inclusion rather than unified.

A function type `(A) -> R ! E` performs at most `E`, so a function with fewer effects can be used
where one with more is expected: function types are covariant in their own row and contravariant
in their parameters' rows. Widening the row of a first-class callable is a typing step only; it
needs no runtime adapter (see [abi.md](abi.md)).

## Where constraints come from

- **Function values** (arguments, returns, bindings, annotations, fields): the value's row is
  included in the expected one, recursively through parameter and result types.
- **Joins** (branches of a match or `if`, array elements, loop exits, writes to a mutable local):
  a type variable receiving a callable gives it a fresh effect variable that each contributor's row
  is included in. Joins never equate the contributors' effects with each other.
- **Invariant positions** (effect arguments of named types, duplicate trait applications in one
  scope, the types behind `&mut` parameters, which are also written back): equality. Where it is
  exact, it unifies the two rows so that equal types stay syntactically equal: two lone
  variables merge, and a lone variable becomes the other row. Other equalities, such as
  `(read, a) = (read, b)`, which does not imply `a = b`, are kept as two inclusions.
- **Trait outputs**: the implementation's output effect relates to the requested one by the
  polarity of its occurrences in the trait's methods. An effect the methods perform is positive:
  the implementation's row is included in the requested one, so a pure `next` serves where a
  fallible one is allowed. An effect the methods receive through callbacks is negative and
  included the other way. An effect in both positions, or in an invariant one, is equal.

Declared effect variables (function, implementation and trait default effect parameters) are rigid
atoms: the body is checked against them and can neither specialize nor widen them.

## Solving

Each inclusion is split per solvable variable into three kinds of constraints over atoms (primitive
effects and rigid variables): lower bounds, ceilings (several ceilings on a variable all apply), and
masked inclusions `a ⊆ (M, b)`, by which the contents of `a` outside `M` flow into `b`. All are Horn
clauses, so the system has a least solution, which the solver maintains incrementally; every growth
and every ceiling is checked at once, so the result does not depend on the order in which
constraints arrive. An inclusion into a row with two solvable variables is a disjunction; it is
deferred and, if it does not hold by the end, satisfied conservatively.

The solution is least over atoms, with rigid variables kept opaque: the solver never asks which
primitive effects a rigid variable stands for. This matches the rows, which cannot name part of a
rigid variable either. If `A` is rigid, `A ⊆ (fallible, b)` gives `b` all of `A`, the smallest row
containing the part of `A` other than `fallible`. Solving over the contents of rigid variables would
find solutions that no row expresses, leaving publication to choose among approximations. It would
also treat the current primitive effects as the only ones, whereas a rigid variable stands for any
effects, including ones added later: adding a primitive effect would then reject programs accepted
before.

While inference runs, a variable reads as its least solution plus itself, or as its row once its
bounds determine it; only facts are baked into rewritten constraints.

## Publication

Published schemes carry no effect constraints, so the solution is encoded by substitution, using
three documented approximations:

- **Ceilings**: a variable bounded above, directly or through the variables it flows into, takes
  the largest row its ceilings allow (their intersection).
- **Lower bounds**: the other variables related by inclusions merge into one variable, a declared
  one if their least solution holds exactly one, and each takes its least solution plus that
  variable. `fn compose(f, g) { |x| g(f(x)) }` publishes one variable for `f`, `g` and the result;
  callers still pass callbacks with different effects.
- **Masked inclusions** are published as inclusions.

Variables occurring only in effects that the published type performs, never in effects it
receives, take their least solution, as do the variables of a body that its type cannot observe.
Every retained constraint is then checked against the published rows; this validation makes each
published signature sound.
