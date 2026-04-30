# Unordered Collections

Ferlium's standard library includes two unordered collection types: `set` and `map`.
They are useful when membership or key lookup matters more than position.
Both are hash-based collections.

## Sets

A set stores unique values of one element type.
Its type is written `set<T>`.

```ferlium
let values = set { 1, 2, 3 };
```

Set literals use braces, but their contents are plain values rather than named fields.
Duplicate elements are ignored:

```ferlium
let values = set { 1, 2, 3, 2 };
len(values)
```

Set values can be arbitrary expressions, not just literals:

```ferlium
fn f(value) { value }
set { f("hi"), f("ho") }
```

An empty set needs type context:

```ferlium
let values: set<int> = set {};
```

## Maps

A map stores key-value pairs.
Its type is written `map<K, V>`.

```ferlium
let labels = map { 1 => "one", 2 => "two" };
```

Inside a map literal, each entry is written `key => value`.
Keys are unique; if the same key appears more than once, the later value wins:

```ferlium
let labels = map { 1 => "one", 2 => "two", 1 => "uno" };
map_get(labels, 1)
```

Map entries can also use arbitrary expressions:

```ferlium
fn key(value) { value + 1 }
fn label(value) { value }
map { key(0) => label("hi"), key(1) => label("lo") }
```

An empty map needs type context:

```ferlium
let labels: map<int, string> = map {};
```

## Building from sequences

`collect()` can build a set or map from a sequence or iterator.

```ferlium
([1, 2, 3] |> iter() |> collect(): set<_>)
```

For maps, the input sequence must yield `(K, V)` pairs:

```ferlium
([(1, "one"), (2, "two")] |> iter() |> collect(): map<_, _>)
```

This is often the easiest way to move from sequence processing into an unordered collection when the data already exists as a pipeline.

## Common operations

The standard library provides a few helpers for working with these collections:

- `empty()` creates an empty set or map when the target type is known
- `len(collection)` returns the number of stored elements or entries
- `set_insert(collection, value)` inserts a value into a mutable set and returns whether it was new
- `set_contains(collection, value)` tests set membership
- `map_insert(collection, key, value)` inserts or replaces a key and returns the previous value if there was one
- `map_get(collection, key)` looks up a key and returns `None` when it is absent
- `map_contains_key(collection, key)` tests key membership

For example:

```ferlium
let mut values: set<int> = empty();
set_insert(values, 1);
set_insert(values, 1);
set_contains(values, 1)
```

```ferlium
let mut labels: map<int, string> = empty();
map_insert(labels, 1, "one");
map_insert(labels, 1, "uno");
map_get(labels, 1)
```

The second example replaces the earlier value for key `1`, so it evaluates to `Some("uno")`.

## Order

Sets and maps do not preserve a meaningful order.
Use them when you care about uniqueness or association, not position.
If you need a stable, indexed sequence, use arrays instead.

## What comes next

The next chapter covers Ferlium's numeric types, their literal forms, and conversions.
