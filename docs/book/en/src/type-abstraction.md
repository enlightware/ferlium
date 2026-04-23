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

Traits are also called [type classes](https://en.wikipedia.org/wiki/Type_class) in some languages, and they are a powerful way to achieve polymorphism and code reuse without inheritance.

### A common standard trait: `Value`

One important standard trait is `Value`.
It describes types that support:

- semantic equality
- conversion to string
- hashing

In everyday code, this trait is what supports operations and functions such as:

- `left == right`
- `to_string(value)`
- `hash(value, state)`

Many built-in types implement `Value`, including `bool`, `int`, `float`, `string`, and arrays whose elements also implement `Value`.
Structured data also participates naturally:

- tuples and records support `Value` structurally
- `struct` and `enum` types derive `Value` from their fields or variants when their components do

For product types, hashing follows the type-defined field order.
For sum types, hashing includes the active variant together with its payload.

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

When you use a function from a trait, you introduce a **constraint**.
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

## Defining your own traits

User code can also define traits.
A simple trait with one main input type looks like this:

```ferlium
trait Double<Self> {
    fn double(value: Self) -> Self;
}
```

Traits may also expose output type slots and carry `where` clauses that specify constraints:

```ferlium
trait Project<Self |-> Output>
where
    Self: Value
{
    fn project(value: Self) -> Output;
}
```

This reads as a relation over types:

- `Double` relates one input type, `Self`
- `Project` relates one input type, `Self`, to one output type, `Output`

The method signatures form the contract that implementations must satisfy.

## Implementing traits

Once a trait exists, you can implement it for suitable types.
For example, using the trait defined above:

```ferlium
trait Double<Self> {
    fn double(value: Self) -> Self;
}

impl Double for int {
    fn double(value: int) -> int {
        value * 2
    }
}

double(21)
```

You can also implement standard-library traits for your own types:

```ferlium
struct Wrapper(int)

impl Ord for Wrapper {
    fn cmp(left: Wrapper, right: Wrapper) {
        cmp(left.0, right.0)
    }
}
```

When writing an `impl`, the method signatures and behavior must match the requirements of the trait.
Impls can also be generic, and Ferlium supports explicit trait input and output bindings in impl headers.

A later chapter, [Trait Implementations and Coherence](./trait-implementations-and-coherence.md), covers this in detail.

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

## Looking ahead

Ferlium continues to evolve by layering explicit syntax on top of the current inference-first model.
The intended workflow remains: write ordinary code, let inference produce the general type, and use explicit binders, `where` clauses, and lightweight annotations (including `_`) when they improve clarity.

## What comes next

The next chapter introduces Ferlium's explicit type syntax, including explicit annotations, generic parameter lists, and `where` clauses.
