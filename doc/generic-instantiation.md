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

For an ordinary call the compiler knows the mapping exactly once, in
`TypeScheme::instantiate_with_fresh_vars`, which allocates a fresh inference variable per quantifier
and returns the substitution. Nothing later knows it directly. A later stage can only *recover* it,
by structurally matching the callee's generic signature against the call site's concrete one — work
that is redone at every use and needs a matcher the type system otherwise has no reason to have.

So the substitution is stored at the moment it is created. At that point its values are the fresh
variables; the end-of-inference substitution pass rewrites them into the types unification solved,
by the same walk that already concretizes the dictionary requirements.

Recursive calls may precede finalization of the callee's requirements. Their late instantiation
retains the relationships between variant types and case payloads, even when those relationships
need no separate runtime parameter. Caller and callee variable numbers belong to different scopes;
coinciding numbers alone do not establish a correspondence.

Compiler-generated blanket-method thunks have a second, analogous source: matching the blanket
implementation already computes its substitution. The trait solver preserves that result and
projects the generic method's quantifiers through it when building the forwarding call. Blanket
implementation normalization gives type variables canonical numeric identities, and registration
requires every blanket method callable to quantify all implementation type variables in
`0..ty_var_count` order. “All” matters: a variable introduced through an implementation constraint
need not occur in the trait-reconstructed method signature, but it remains a quantifier of the actual
callable. Effect quantifiers are unordered in `TypeScheme`, so every instantiation encodes them in
sorted `EffectVar` order, as described under Encoding below. The thunk can therefore build the
application from the blanket key and matched substitution without duplicating the callable's
quantifier list in the implementation record or matching concrete signatures.

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

## Sharing compiler-generated open dictionaries

Some runtime dictionaries are generated while their input type still contains variables. A
compiler-derived `Value<X>` dictionary closes over the external `Value` evidence at `X`'s leaves;
recursive occurrences use the dictionary itself. Thus `Value<Tree<T>>` is constructed from
`Value<T>` rather than becoming another requirement of a generic function. A representation-open
named type owned by another module is an opaque leaf supplied by its owner's dictionary. The
`SIZE` and `ALIGN` entries are generated functions over the same captures when the layout is open.
Function fields remain opaque to the structural code. Blanket trait applications can likewise be
materialized with output effect variables that the unconstrained query later defaults.

Caller-local variable identities do not distinguish such generated code. Before using an open
input as a generated-artifact cache key, the compiler alpha-canonicalizes type, mutability and effect
variables in deterministic first-occurrence order. Concrete types and primitive effects remain in
the key, as does the equality pattern between repeated variables. Thus two independently numbered
open rows share an artifact, while a row containing `fallible` remains distinct from one without it.

A generated trait dictionary is a static definition plus an ordered capture schema. The schema and
each entry's mapping from hidden parameters to captures are canonicalized with the open input and
must agree when a cached definition is reused. A runtime use closes that shared definition over the
caller's evidence in schema order; its identity is therefore the definition together with the
recursive captured evidence, not the caller-local type-variable numbers.

This canonicalization is deliberately confined to generated artifacts. It does not alter the
caller's semantic type or ordinary trait-impl lookup. A reused dictionary expression is typed with
the caller's actual input; its stored methods remain generic over the canonical variables.

Trait-output resolution during inference and defaulting is not a runtime-artifact retention point.
Such a query uses the ordinary trait-selection rules in a scratch HIR arena, copies the associated
type and effect outputs, then rolls back any dictionaries, methods, getters, or cache entries that
selection provisionally generated. The final HIR elaboration of a dictionary or method reference
performs the materializing query. Consequently, effect rows considered and later rejected or
defaulted during inference cannot leave orphaned module functions that the MIR optimizer would
treat as roots.

Materialized blanket applications whose output effects depend on the application use a separate
cache from concrete trait implementations. The concrete cache is keyed only by input types, so
putting a defaulted output there could leak that default into a later query with explicit output
bindings. Inference-only output queries populate neither cache. When final HIR actually requires a
runtime dictionary, applications with no requested outputs can share through the
unconstrained-application cache; materializations carrying explicit output bindings remain
independent.

## Trait defaults and enclosing-impl evidence

A default method is checked and compiled once in the trait's module, even if no impl uses it.
Its contract is its declared signature together with the enclosing trait, parent and `where`
constraints. The body must preserve the generality of the declared types and effects and cannot
impose additional requirements on implementations. Names resolve in the trait's module.

An omitted method gets a forwarding function in its dictionary slot. The forwarder instantiates
the checked default and supplies the implementation's own dictionary, so sibling calls use that
implementation's overrides. Written methods use the same enclosing-impl evidence. This works for
concrete, header-less and generic impls without requiring the impl to be globally selectable while
its methods are checked.

Compiler-defined `Value` has a Rust-built HIR default for `ne`, available before source std is
compiled. Native and derived implementations complete omitted defaulted slots with calls to the
same default; explicit implementations take precedence. Existing required methods retain their
calling conventions, while forwarding entries receive the evidence they need.

Self evidence is a body assumption, not an implementation prerequisite. An impl's parent and
`where` obligations are checked independently; its own dictionary cannot justify those obligations.
At runtime, self evidence comes from the selected dictionary itself, without a cyclic heap
allocation. Evidence requirements belong to individual methods: using a default does not add a
hidden parameter to unrelated leaf methods. Inference tracks which methods use which assumptions,
conservatively retaining evidence when a generated obligation's owner is unknown.

Supplied assumptions (givens) take precedence over ordinary impl lookup when their trait and input
types match exactly. Equal trait/input applications must agree on their output types and effects;
list order cannot choose between them. If unresolved inputs could still match a given, the solver
defers the obligation before ordinary lookup. It must not bind independent input parameters merely
to select evidence. Genuinely ambiguous applications still require a type annotation or a declared
functional dependency.

Recursion analysis includes dictionary calls and implicit clone/drop operations as well as static
calls. Known call cycles and unresolved dispatch require call-depth guards. A conservative guard
alone does not prevent inlining; its check must survive the rewrite. Native entries cannot re-enter
the current execution. Declared parameter generality is currently
checked after inference; rigid checking for more precise diagnostics is tracked in
[#185](https://github.com/enlightware/ferlium/issues/185).
