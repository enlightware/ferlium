# Sequence Processing

After learning about functions as values and trait-based abstraction, you can use Ferlium's standard-library sequence combinators more effectively. This chapter covers the main transformation and reduction functions over collections and iterators, and explains when results are built eagerly versus lazily.

## Transforming sequences

Ferlium provides `map`, `filter`, and `filter_map` for both collections and iterators.

As a reminder, the pipeline operator rewrites left-to-right function calls:

- `value |> f()` means `f(value)`
- `value |> f(arg)` means `f(value, arg)`

### Collections transform eagerly

When you call these functions on an array, Ferlium rebuilds an array immediately:

```ferlium
[1, 2, 3] |> map(|x| x + 1)
```

```ferlium
[1, 2, 3] |> filter(|x| x > 1)
```

```ferlium
[1, 2, 3] |> filter_map(|x| if x > 1 { Some(x * x) } else { None })
```

This is useful when you want to stay in the collection world and keep working with arrays directly.

### Iterators transform lazily

When you call the same functions on an iterator, you get back another iterator adaptor:

```ferlium
let mut it = [1, 2, 3] |> iter() |> map(|x| x + 1);
(next(it), next(it), next(it), next(it))
```

This evaluates to:

```ferlium
(Some(2), Some(3), Some(4), None)
```

The same eager/lazy distinction applies to `filter` and `filter_map`.

### Callback purity

Callbacks passed to `map`, `filter`, and `filter_map` are currently required to be pure.

## Collecting results

Use `collect()` to turn a sequence or iterator into a target collection.
The target collection type must be known from context:

```ferlium
let xs: [_] = 0..3 |> collect();
xs
```

```ferlium
let ys: [_] = [1, 2, 3] |> iter() |> map(|x| x as float) |> collect();
ys
```

This is especially useful when you want to switch back from lazy iterator code to an eager collection value.

## Reducing sequences

Ferlium also includes reduction-style functions that consume a sequence and produce a summary value.

### Quantifiers and search

Use `all` and `any` to test predicates over a whole sequence:

```ferlium
[0, 1, 2] |> all(|x| x >= 0)
```

```ferlium
[0, 1, 2] |> any(|x| x > 1)
```

Use `find` to retrieve the first matching element, and `position` to retrieve its index:

```ferlium
[0, 1, 3] |> find(|x| x > 1)
```

```ferlium
[0, 1, 3] |> position(|x| x > 1)
```

### Counting and aggregation

Use `count` to count elements and `sum` to add them:

```ferlium
2..5 |> count()
```

```ferlium
[2, 5] |> sum()
```

`average` divides the sum by the count:

```ferlium
[2.0, 4.0, 6.0] |> average()
```

Use `join` to concatenate a sequence of concatenable values with a separator between elements:

```ferlium
join(["a", "b", "c"], ",")
```

When the sequence is empty, `join` returns `default()` for the element type.

### Minimum and maximum

Use `minimum` and `maximum` when the element type is ordered:

```ferlium
[3, 1, 2] |> minimum()
```

```ferlium
[3, 1, 2] |> maximum()
```

These functions require a non-empty sequence and panic on an empty one.

## Choosing between collections and iterators

A good rule of thumb is:

- use arrays directly when you want eager results
- use `iter(...)` when you want lazy pipelines
- use `collect()` when you want to switch from lazy iteration back to an eager collection

This keeps code readable and makes evaluation timing explicit from the shape of the pipeline.

## What comes next

The next chapter introduces effects, showing how Ferlium tracks interactions such as reading, writing, and failure alongside ordinary values.
