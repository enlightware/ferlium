# Inference

How the compiler relates types, mutability, and effects: the constraints produced by expressions,
how the solvers interpret them, and how effect solutions are published in type schemes.
See [generic-instantiation.md](generic-instantiation.md) for how callers instantiate those schemes.

## Foundation

Ferlium's theoretical foundation is HM(X), as developed by Odersky, Sulzmann, and Wehr in
[Type Inference with Constrained Types](https://infoscience.epfl.ch/bitstreams/599e87e9-0212-49ea-ae4d-6a497b5b5259/download).
HM(X) parameterizes Hindley–Milner inference by a constraint domain and its solver. Ferlium's
type, trait, mutability, and effect constraints belong to that language-specific domain.
The framework's principal-type guarantees depend on conditions on the domain and solver;
citing HM(X) does not establish those guarantees for every implementation choice below.

## Compilation environment

Trait selection and coherence use the current module, std, and the modules imported or referenced anywhere in the source, together with their dependencies.
This environment is fixed for the whole compilation, including the optional final expression.
Unrelated loaded modules cannot change inference.

## Effects and trait selection

Changing only effect annotations or inferred effect bounds cannot select a different impl. It can
change the effects of that impl's application, or make the application ill-typed. An effect is an
upper bound used for checking, so an approximation must not change what a program runs.

So selection has two steps. It first finds the impl by structure, with all effects ignored, in the
head and throughout prerequisites. Coherence uses the same view, so impls that differ only by
effects overlap, and improvement does not let effects decide what gets inferred. The effects are
then checked on that impl, and a mismatch is an error: never a reason to try another impl or to
derive one.

To keep this true by construction, each effect in an impl's inputs must be a variable of the impl,
used once. An impl whose methods perform such an effect exposes it as an output effect of its trait.

Derived dictionaries are shared at erased effects, which is valid as derivable traits have no outputs
and an impl method cannot perform an effect its trait does not expose. Source impls that a derivation
needs for a member are still applied with the real effects, so that their prerequisites hold.

## Publication policy

Type subtyping and effect inclusion follow the same design choice: retain directional constraints
while inferring a body, then publish a scheme in the existing language, without residual subtype
or effect-inclusion bounds. Existing trait constraints remain part of schemes. Preserving principal
types across publication boundaries is not a goal; readable signatures and a simpler scheme
representation take precedence over retaining every valid typing.

Publication may conservatively strengthen constraints through eligible polarity-based substitutions
and by merging related inference variables. Every original obligation must then hold for **every
instantiation allowed by the published scheme**, under its environment and declared constraints.
Finding one satisfying assignment is insufficient. Reject publication if its choices cannot be
validated; never silently discard a bound. Rigid parameters, captured variables, invariance, and
trait obligations restrict the choices. This strengthening belongs at publication, not in eager
constraint propagation, where it could reintroduce order dependence.

For types, `fn choose(c, f, g) { if c { f } else { g } }` can publish `(bool, a, a) -> a`
instead of retaining subtype bounds between three separate variables. Call-site subtyping can
still join `() -> Never` and `() -> int` at a fresh `a`. Some generality is lost, however:
invariant containers can prevent call-site widening from recovering distinctions merged at
publication. The policy accepts that limitation; validation preserves soundness, not completeness
or principal types. Order independence of publication still needs its own validation.

The type and [effect](#publication) solvers implement this contract with different reduction rules.
Type publication selects representable joins and meets, and may strengthen remaining relationships
to equal type structure. Every original bound must remain satisfied after these choices. Explicit type
parameters must remain distinct and polymorphic. Ferlium has no top type or general union/intersection
constructors, so joins such as `int` with `bool` can fail.

Structural constraints made resolvable by a pass are retried before trait improvement. In particular,
a projection must reveal its connection to a written generic before an impl can narrow its result.

### Public requirements

Before publishing an exported function or implementation, requirements mentioning private types or
traits are reduced in the defining module. An impl can be selected only if it applies uniformly,
without choosing unresolved input types, and no other candidate could apply after instantiation.
Independent variables remain generic, including those occurring only in a function's result and
outputs supplied by public prerequisites. A uniformly selected impl may determine its own outputs;
these substitutions also reach the impl head and bodies. A cycle of output dependencies alone does
not establish determination.

The compiler records these choices and elaboration replays them without selecting impls again.
The defining body constructs private dictionaries from the public evidence its caller supplies.
Ground public requirements are discharged in the provider; retained public requirements are solved
in the caller's scope, even if the provider has a private impl for the caller's type. Published
requirements therefore mention only public names, and callers need no access to private impls.

Missing evidence and reductions exceeding the work limit are errors at the definition. Recursive
`Value` construction may pass through custom impls when it refers back to a generated dictionary:
the custom dictionary is built inside a generated entry using its self evidence. This preserves the
custom methods without eagerly building cyclic captures. Cycles consisting only of source impl
prerequisites remain errors. Other derivations currently require ground inputs.

As with other inferred requirements, changing a private helper may tighten the published contract.

## Type relations

The structural solver in `src/types/type_inference/unify.rs` uses three relations:

| Relation | Contract |
| --- | --- |
| `SubType` | The current value is usable where the expected type is required. |
| `SameTypeWithSubEffects` | Equal type structure and mutability, with directional callable effects. |
| `SameType` | Exact equality, including nested callable effects and mutability. |

Function subtyping is contravariant in arguments and covariant in results and effects. An argument
the actual callee may mutate requires a mutable contract and an invariant type. Read-only arguments
remain contravariant even when the expected contract permits mutation. The same rules apply to
subscript arguments. Named type arguments use exact equality: without variance analysis, a parameter
might occur in an argument or mutable position in its definition.

Subscript results are covariant only when the expected capability does not expose a mutable
member. A mutable result permits replacing the stored value, so its complete type, including nested
callable effects, must match exactly. A coercion may discard mutable access and widen the readable
result. This depends on the expected result capability, whereas argument write-back depends on the
actual callee's access.

Value ascriptions check subtyping and expose the annotated value type; place ascriptions require
exact equality so writes preserve storage identity. Mutable call arguments require the reverse
compatibility check whenever the actual callee can write.

Type variables are normalized through the unification table before comparing structure. Recursive
types are compared with an active set of ordered type pairs and their relation; a comparison under
subtyping cannot discharge one that requires equality. The active set tracks the current recursion
path rather than caching successes across later variable bindings.

## Bounds and selection

Unknown subtype endpoints remain directional bounds. Concrete lower and upper bounds propagate
through variables; variable cycles become equalities. Structural comparison decomposes concrete
pairs into further obligations.

Selection coordinates with trait and projection solving. It defers choices that still depend on
pending outputs, including dependencies through nested types and projected members. A symbolic
join or meet is usable only when its constructor decisions hold for every remaining instantiation;
otherwise the bounds stay unresolved until conservative publication.

Eligible numeric and unit defaults run before publication. Defaults made eligible by publication
are retried in both expressions and function bodies, and the resulting obligations are rechecked.
Defaulting respects the current signature, explicit parameters and their connected constraints;
delaying a subtype relation must not make a generic variable appear local.

## Never

`Never` is bottom only in the subtype relation: `Never <: T` holds for every type, but a concrete
type other than `Never` cannot satisfy `T <: Never`. Both equality relations require `Never` to match `Never`.
This is structural identity, not an analysis equating all uninhabited types.

For an unresolved inference variable `a`, `Never <: a` imposes no restriction; another branch
can determine its type. Conversely, `a <: Never` and equality with `Never` bind `a` to `Never`.
Defaulting to `Never` happens in separate steps with their own eligibility checks: unconstrained
diverging returns, unused variant payloads, and finally type variables of a body or its closures
that no signature reaches and no obligation depends on, such as the parameter of a closure never
called. A `Value` obligation depends on a variable only through the evidence its dictionary needs,
so the element type of an empty array stays undetermined. Bottom is neither an inference wildcard
nor a universal default.
In particular, selection does not resolve incompatible upper bounds, such as `a <: int` and
`a <: [b]` from `a[a]`, to their meet `Never` or to a type containing it: that is a type error.

With `diverge: () -> Never` and `one: () -> int`, either contributor order in
`if c { one } else { diverge }` infers a callable returning `int`. Callable joins may also infer
`Never` arguments when that is the representable common contract. Such a callable value can be
stored, but an ordinary inhabited argument cannot be passed to it. Eligible numeric defaulting
runs before the fallback for an otherwise unconstrained diverging expression.

Value returns, annotations, and match arms use directional compatibility. Structural projections,
trait identities, and invariant type positions retain structural equality. A place-returning or
yielding expression that diverges before producing a place needs no equality check for that place;
its effects are still retained.

A callable returning `Never` is itself an ordinary function value. Return covariance permits
`() -> Never` to satisfy `() -> int`, subject to effect inclusion, but not the reverse. In
particular, a mutable local storing `() -> Never` cannot receive a boolean-returning replacement.
Containing `Never` does not bypass named-parameter invariance or mutable-argument checks, and a
fallible diverging callable cannot satisfy a pure callable requirement.

These rules follow the standard [bottom subtype rule](https://www.seas.upenn.edu/~cis5000/cis500-f02/lectures/1106-4up.pdf).
The distinction between bottom-to-any compatibility and equality with an inference variable is
also described in the [Rust compiler's coercion documentation](https://rustc-dev-guide.rust-lang.org/hir-typeck/coercions.html).

## Mutability and places

Mutability constraints distinguish having at least the required access from having exactly the
same mutability. A mutable place can satisfy a read-only requirement; a read-only place cannot
satisfy a mutable requirement. Both same-type relations require equal mutability. The solver
resolves mutability constraints before structural type relations, so callable comparisons know
which arguments require invariance. Mutability is not abstracted over in type schemes.

Returning a value and exposing a place have different typing requirements. A value may be widened
by subtyping, while an exposed place preserves its referent type so writes remain valid.
`TypingEnv::return_requires_place()` exposes this semantic requirement to expression inference;
callers do not inspect the result transport convention. A diverging expression supplies neither
a value nor a place, but its effects and control-flow behavior must still be preserved.

## Effect inference

### Effect rows

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

### Where constraints come from

- **Function values** (arguments, returns, bindings, annotations, fields): the value's row is
  included in the expected one, recursively through parameter and result types.
- **Joins** (branches of a match or `if`, array elements, loop exits, writes to a mutable local):
  a type variable receiving a top-level callable gives it a fresh effect variable that each
  contributor's row is included in. This widening does not descend into named type arguments:
  joining already-typed `Box<Pure>` and `Box<Fallible>` requires equal callback effects and is
  rejected when those effects differ (see [Design choices](#design-choices)).
- **Invariant positions** (type and effect arguments of named types, the outputs of equal
  trait applications in one scope, the types behind `&mut` parameters, which are also written
  back): equality. Where it is exact, it unifies the two rows so that equal types stay
  syntactically equal: two lone variables merge, and a lone variable becomes the other row. Other
  equalities, such as `(read, a) = (read, b)`, which does not imply `a = b`, are kept as two
  inclusions.
- **Trait outputs**: the implementation's output effect relates to the requested one by the
  polarity of its occurrences in the trait's methods. An effect the methods perform is positive:
  the implementation's row is included in the requested one, so a pure `next` serves where a
  fallible one is allowed. An effect the methods receive through callbacks is negative and
  included the other way. An effect in both positions, or in an invariant one, is equal.
  Equal applications of a trait in one scope denote one implementation, so they share the output
  effects still being inferred. Fixed ones, such as those written in `where` clauses, are bounds
  that this implementation must all fit: performed bounds intersect, received ones unite, and the
  shared effect takes the result.

Declared effect variables (function, implementation and trait default effect parameters) are rigid
atoms: the body is checked against them and can neither specialize nor widen them.

An effect left unwritten in an annotation of a function or inside its body, or in a requirement
of the `where` clause of a function or of an implementation, is inferred, and never stands for a
declared variable: it is an inference variable of that annotation or requirement alone. So
`fn h<T>(x: T) -> int where T: Run { 1 }` accepts any implementation, and the effect of `Run`
joins the effects of `h` only if its body performs it. The signature of a trait method is fixed,
also when the method has a default body: an effect left unwritten there is the empty one, as it
is in a type definition.

A recursive group with declared effect variables behaves, for effects, as its unrolling: each
function calling copies of the others, down to functions that call nothing. It is inferred in three
steps. Joint inference of the group gives the types of each signature, and the places of the
effects left to infer. From the contracts of functions that call nothing, each body is then
inferred alone against the current contracts of the group, by ordinary inference, which gives its
next contract, until none changes; a contract only gets weaker, so this ends. Each body is finally
checked alone against these fixed contracts, with its declared variables rigid, which makes the
result sound whatever the previous steps proposed. In the last two steps each call in the group
instantiates its callee's contract. Only effects are instantiated per call in this way; types keep
one instance per group. The joint inference still solves effects with one instance per function,
and rejects a group that it cannot solve so.

### Solving

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

### Publication

Following the shared [publication policy](#publication-policy), published schemes carry no effect
constraints. The solution is encoded by substitution, using three documented approximations:

- **Ceilings**: a variable bounded above, directly or through the variables it flows into, takes
  the largest row its ceilings allow (their intersection).
- **Lower bounds**: the other variables related by inclusions merge into one variable, a declared
  one if their least solution holds exactly one, and each takes its least solution plus that
  variable. `fn compose(f, g) { |x| g(f(x)) }` publishes one variable for `f`, `g` and the result;
  callers still pass callbacks with different effects.
- **Masked inclusions** are published as inclusions.

Variables occurring only in effects that the published type performs, never in effects it
receives, take their least solution, as do the variables of a body that its type cannot observe.
What is observable depends on what is published: a function's signature and the constraints over
its type variables; an implementation method's head, as the method is quantified over it alone; a
top-level expression's type, as it is not generalized. Derived implementations take the effects of
the callables in their input types at their least solution, as no derived method calls them.
Every retained constraint is then checked against the published rows; this validation makes each
published signature sound.

### Design choices

Rejected alternatives: residual effect constraints in published schemes (principal, but needs a
scheme language, a simplifier and a display), restricting only by polarity (a positive trait slot
can still be pinned invariantly elsewhere), and an ambiguity diagnostic for disjunctions (it would
reject ordinary joins). The accepted cost is that merged variables and replaced ceilings make some
signatures coarser, and sometimes give a may-fail convention where a finer type would not.
Type and effect arguments of named types are invariant; this includes effects nested inside a
type argument. For example, `Consumer<(() -> int)>` cannot become
`Consumer<(() -> int ! fallible)>` when `Consumer<T>` stores a function accepting `T`:
the stored function may require a pure callback. Invariance also rejects some safe conversions,
such as widening a callback already stored in `Box<T>`; a variance analysis of named types could
relax this. Order independence of solving is tested, not proved, and whether validation can reject a
function without declared effect variables is open: a counterexample is to be investigated, not
answered by weakening validation.
