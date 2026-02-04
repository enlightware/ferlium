# Type Abstraction

Ferlium provides powerful type abstraction without requiring heavy type syntax.
In practice, you write normal code, and the compiler infers [polymorphic types](https://en.wikipedia.org/wiki/Parametric_polymorphism), tracks trait constraints from operations, and applies sensible defaults when some types remain ambiguous.

## Recap: inferred polymorphism

From the user perspective, polymorphism in Ferlium is mostly automatic.
When a function body does not force a specific concrete type, Ferlium keeps the function general.

```ferlium
fn id(x) { x }

(id(1), id(true), id("hi"))
```

This works because Ferlium infers one generalized type for `id` and instantiates it at each call site.
Inference is whole-module, so functions are inferred together and can constrain each other.

## Traits: shared behavior across types

A **trait** describes behavior that multiple types can support.
By behavior, we mean a set of functions that can be performed on values of that type.
Operations and standard functions rely on traits rather than concrete types.
For example:

- numeric operations rely on numeric behavior (`Num` trait)
- ordering operations rely on ordered behavior (`Ord` trait)

Another useful way to think of a trait is as a **relation over types**.

- Many traits relate one main type to behavior (for example numeric and ordering behavior).
- Some traits relate multiple types at once.
- Some traits also expose output type slots (often called associated types).

### Traits relating multiple types

A good example of trait relating multiple types is `Cast`, which relates a source type and a target type.
You use it with explicit `as` casts:

```ferlium
let i: int = 5;
let f = i as float;  // Cast(From = int, To = float)
let j = 5.3 as int;  // Cast(From = float, To = int)

(f, j)
```

### Associated types

Traits can also carry associated type information. In the standard library, iterator and sequence traits use this idea:

- `Iterator` has an associated `Item` type (the element type produced by `next`).
- `Seq` links a sequence type to both its element type and its iterator type.

This helps explain annotations: when the IDE shows inferred constraints, you may see that some types are not independent, but connected through trait relations.

## Constraints: how operations shape types

When you use an operation, you introduce a **constraint**.
A constraint says: “this type must implement a given trait”.

Examples:

- `x + y` adds numeric constraints, meaning that `x` and `y` must be of the same type and implement the `Num` trait.
- `x < y` adds ordering constraints, meaning that `x` and `y` must be of the same type and implement the `Ord` trait.
- `x as float` adds a cast constraint, meaning the source type must be castable to `float`.

So this function gets a numeric constraint from `+`:

```ferlium
fn twice(x) { x + x }
```

and this one gets an ordering constraint from `<`:

```ferlium
fn min_like(a, b) {
    if a < b { a } else { b }
}
```

In the IDE (including the playground), inferred type information and constraints are shown as inline annotations, which helps explain *why* a function is accepted or rejected.

For iterator-style code, these annotations are especially useful because associated types are inferred for you:

```ferlium
let mut it = iter([1, 2, 3]);
next(it)
```

Here, the element type (`Item`) is inferred as `int`, and the return type of `next` follows as `None | Some(int)`.

## Implementing existing traits

At the moment, traits are defined in the standard library, and user code can implement those existing traits for user-defined types.

```ferlium
struct S;

impl Serialize {
    fn serialize(x: S) {
        None
    }
}
```

Another example:

```ferlium
struct S;

impl Deserialize {
    fn deserialize(v) {
        S
    }
}
```

When writing an `impl`, the method signatures and behavior must match the requirements of the trait.

## Partial type annotations with `_`

You can annotate only the parts you care about and leave the rest to inference using `_`, which acts as a type hole.

```ferlium
fn id_array(x: [_]) { x }
fn pair(v) -> (_, _) { v }
fn keep_shape(x) -> [_] { x }
```

This is useful when you want to constrain structure (for example, “array of something” or “pair of something”) without naming every type explicitly.

You can also use `_` in local annotations:

```ferlium
fn f(x) {
    let a: [_] = x;
    a
}
```

## Defaulting of ambiguous types

Sometimes inference leaves a type variable unconstrained enough that multiple choices would fit.
Ferlium applies defaulting rules so code remains ergonomic.

### Numeric defaulting

If an unconstrained numeric type is only known to satisfy the `Num` trait, Ferlium defaults it to`int`.

```ferlium
let n = 0;
n
```

Here `n` defaults to `int` unless later context requires a different numeric type.
If context does require one, that context wins:

```ferlium
let f: float = 1;
f
```

### Open sum defaulting

For open sum-type information that remains unconstrained, Ferlium defaults to a closed minimal sum type: the smallest set of constructors required by the code.

```ferlium
let v = Some("text");
v
```

In this situation, Ferlium can close the type to the minimal constructor set needed by the expression, instead of leaving it indefinitely open.

### Known limitations

Currently, numeric and open sum defaulting do not combine well.
When both need to apply to the same expression, compilation can fail.
This is a known limitation.

## What you cannot write explicitly yet

Today, type abstraction is largely inference-driven.
In particular:

- you cannot write explicit generic parameter lists on functions
- you cannot define new traits in user code yet
- you cannot write explicit user-level trait constraint clauses for functions

You still get polymorphism and trait-based behavior through inference and standard-library traits.

## Looking ahead

As Ferlium evolves, explicit generic syntax will be added on top of the current inference-first model.
For now, the intended workflow is: write ordinary code, let inference produce the general type, and use lightweight annotations (including `_`) only when they improve clarity.

## What comes next

The next chapter introduces effects, describing how functions can interact with their environment beyond pure computation.


