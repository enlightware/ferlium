# Trait Implementations and Coherence

Ferlium lets user code implement both standard-library traits and user-defined traits.
This chapter covers the surface syntax for `impl`, generic impls, explicit trait bindings, and the rules that keep trait resolution unambiguous.

## Basic impl syntax

For a simple single-input trait with no explicit output types, the syntax is:

```ferlium
struct Counter(int)

impl SizedSeq for Counter {
    fn len(counter: Counter) {
        counter.0
    }
}
```

This is the compact form of an impl header.
It works well for traits that conceptually operate on one main type.
You can think of it as sugar for an explicit binding such as `impl SizedSeq for <Self = Counter> { ... }`.

## Generic impls

Impls can introduce their own generic parameters with Rust-like binder syntax:

```ferlium
struct Bag<T>([T])

impl<T> SizedSeq for Bag<T> {
    fn len(bag: Bag<T>) {
        len(bag.0)
    }
}
```

Here the impl says: for every `T`, `Bag<T>` is a sized sequence.
The same binder syntax also works for more involved generic impls, including iterator-like types.
The next sections show those richer impl headers.

## Impl-level `where` clauses

Impls may also carry their own `where` clause.
This is useful when an implementation only applies under extra trait assumptions:

```ferlium
struct Wrapper<T>(T)

impl<T> SizedSeq for Wrapper<T>
where
    T: Iterator<Item = int>
{
    fn len(wrapper: Wrapper<T>) {
        count(wrapper.0)
    }
}
```

The extra constraints become part of the impl itself.
They participate in trait selection and in coherence checking, just like the types named in the impl header.

## Explicit bindings

Some traits relate more than one input type, or also expose output slots.
In those cases, an impl header can spell the bindings explicitly.

### Multi-input traits

For multi-parameter traits such as `Cast`, named bindings are usually the clearest choice:

```ferlium
struct Wrapper<T>(T)

impl<T> Cast for <From = T, To = Wrapper<T>> {
    fn cast(value: T) -> Wrapper<T> {
        Wrapper(value)
    }
}
```

Ferlium also accepts positional input bindings such as `impl<T> Cast for <T, Wrapper<T>> { ... }`.
Named bindings are usually easier to read, and they line up naturally with traits that also have output slots.

### Traits with output types

Traits such as `Iterator` have output slots.
You may write them explicitly:

```ferlium
struct TransformIter<I, T, O>
where
    I: Iterator<Item = T>
{
    iterator: I,
    mapper: (T) -> O,
}

impl<I, T, O> Iterator for <Self = TransformIter<I, T, O> |-> Item = O> {
    fn next(it: &mut TransformIter<I, T, O>) -> None | Some(O) {
        match next(it.iterator) {
            Some(value) => Some(it.mapper(value)),
            None => None,
        }
    }
}
```

Writing output bindings is optional.
If you omit them, Ferlium infers them from the method signatures.
If you write them explicitly, they must agree with the inferred ones.

## Coherence

Ferlium uses a strict coherence rule for trait implementations:

- for any given trait application, there must be at most one applicable impl
- overlapping impls are rejected

This keeps trait resolution predictable.
The compiler never has to choose arbitrarily between two equally valid impls.

For example, this is rejected because both impls target the same trait and type:

```ferlium,compile_fail
struct Wrapper(int)

impl Serialize for Wrapper {
    fn serialize(value: Wrapper) {
        None
    }
}

impl Serialize for Wrapper {
    fn serialize(value: Wrapper) {
        None
    }
}
```

The same rule also rejects overlapping generic impls.
For example, if two generic impl declarations could both apply to the same types, Ferlium rejects them.

## The orphan rule

Ferlium does not let an arbitrary module implement an existing foreign trait for arbitrary foreign input types.
In practice, when you implement an existing trait, at least one input type in the impl must be a local named type that belongs to your module.

This restriction is called the orphan rule.
More generally:

- a local trait may be implemented freely
- a foreign trait requires at least one local named input type in the impl

This is allowed, because `Counter` is local to the current module:

```ferlium
struct Counter(int)

impl SizedSeq for Counter {
    fn len(counter: Counter) {
        counter.0
    }
}
```

This is rejected, because both the trait and the input type are foreign:

```ferlium,compile_fail
impl SizedSeq for int {
    fn len(value: int) {
        1
    }
}
```

The orphan rule prevents unrelated modules from attaching competing impls to the same foreign types.
Combined with coherence, it keeps trait resolution predictable across module boundaries, which is important for separate compilation.

## Current scope

Today, user code can:

- implement standard-library and user-defined traits
- write generic impls
- write impl-level `where` clauses
- use explicit trait input and output bindings in impl headers

User code still cannot:

- write per-method generic parameter lists inside traits or impls
- write method-local `where` clauses inside trait impls

## What comes next

The next chapter introduces Ferlium's module system — how items in different modules refer to one another with `::` paths, how `use` declarations bring names into scope, and the role the host application plays in deciding what modules exist.
