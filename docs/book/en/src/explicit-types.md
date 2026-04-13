# Explicit Types

Ferlium lets you write types explicitly when doing so improves clarity or constrains inference.

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

## Functions

### Generic parameters on functions

You can also make a function's generic parameters explicit.
This is useful when you want the surface syntax to show that a function is polymorphic, or when you want annotations inside the function body to refer to those generic parameters by name.

```ferlium
fn keep<T>(value: T) -> T {
    let same_value: T = value;
    same_value
}

(keep(1), keep(true))
```

This does not turn off inference.
The body is still type-checked as usual, but the explicit parameter list fixes the names and scope of the generic parameters used by the signature and by type annotations in the body.

Function generics compose naturally with inference for the rest of the signature.
You may annotate as much or as little as you want.

### Function-level `where` clauses

Functions may also carry an explicit `where` clause.
This makes trait requirements part of the function's declared interface rather than leaving them entirely implicit.

```ferlium
fn keep_ord<T>(value: T) -> T
where
    T: Ord
{
    value
}
```

This is especially useful when a function's behavior depends on trait-supported operations and you want that dependency to be visible in the source.
The body is still checked against the declared constraints, so an invalid call is rejected just as it would be for an inferred constraint.

## Nominal types

Named types can themselves be generic.
This lets you define one `struct` or `enum` shape that works for many concrete types, while still keeping nominal identity.

### Generic `struct`

Generic parameters are written in angle brackets after the type name:

```ferlium
struct Box<T>(T)

struct Pair<A, B> {
    first: A,
    second: B,
}
```

You use a generic named type by applying concrete type arguments:

```ferlium
let a = Box(1); // produces a Box<int>
let b = Pair { first: 1, second: "hi" }; // produces a Pair<int, string>
```

### Generic `enum`

Enums can be generic as well:

```ferlium
enum MaybeValue<T> {
    Absent,
    Present(T),
}
```

Construction and matching work the same way as for non-generic enums:

```ferlium
# enum MaybeValue<T> {
#     Absent,
#     Present(T),
# }
let value: MaybeValue<int> = MaybeValue::Present(41);

match value {
    Present(x) => x,
    Absent => 0,
}
```

### `where` clauses in nominal types

Generic named types can have `where` clauses.
These constrain which type arguments are allowed.

```ferlium
struct TransformIter<I, T, O>
where
    I: Iterator<Item = T>
{
    iterator: I,
    mapper: (T) -> O,
}
```

This says that `TransformIter<I, T, O>` only makes sense when `I` is an iterator producing `T`.

The `where` clause can mention:

- trait constraints on the generic parameters
- associated type bindings such as `Item = T`
- multi-parameter trait constraints, as described later in the type abstraction chapters

## What can be explicit today

Ferlium still has an inference-first design, but several parts of type abstraction can now be written explicitly:

- you can write explicit generic parameter lists on functions
- you can write function-level `where` clauses
- you can define generic `struct` and `enum` types
- you can add `where` clauses to generic type definitions
- you can write generic `impl` blocks for existing traits
- you can add `where` clauses to those `impl` blocks
- you can write explicit trait input and output bindings in impl headers

Some limitations remain:

- you cannot define new traits in user code yet
- you cannot write per-method generic parameter lists or method-local `where` clauses inside trait impls

You still get polymorphism and trait-based behavior through inference and standard-library traits, and explicit syntax mainly serves to document or constrain that inferred structure.

## What comes next

The next chapter introduces trait implementations and coherence, describing how you can implement existing traits for your types, and how Ferlium ensures that trait resolution remains predictable across module boundaries.