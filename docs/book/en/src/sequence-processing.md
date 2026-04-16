# Sequence Processing

After learning about functions as values and trait-based abstraction, you can use Ferlium's standard-library sequence combinators more effectively. This chapter covers the main transformation and reduction functions over collections and iterators, and explains when results are built eagerly versus lazily.

## Sorting

Sorting comes in two forms:

- `sort(array)` sorts an array in place
- `sorted(array)` returns a sorted copy

For example:

```ferlium
let mut xs = [3, 1, 2, 1];
sort(xs);
xs
```

```ferlium
sorted([3, 1, 2, 1])
```

Ferlium's array sort is stable, so equal elements keep their relative order.

When you need a custom ordering, use `sort_by` or `sorted_by`:

```ferlium
let mut xs = [(1, "b"), (0, "x"), (1, "a")];
sort_by(xs, |left, right| cmp(left.0, right.0));
xs
```

```ferlium
sorted_by([(1, "b"), (0, "x"), (1, "a")], |left, right| cmp(left.0, right.0))
```

## Reversing

Arrays also support reversal in two forms:

```ferlium
let mut xs = [1, 2, 3];
reverse(xs);
xs
```

```ferlium
reversed([1, 2, 3])
```

`reverse` mutates an array in place.
`reversed` returns a reversed copy.

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

Callbacks passed to `map`, `filter`, and `filter_map` and `sort` functions are currently required to be pure.

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

You can also give explicit types using the expression annotation syntax.
For example, to collect into an array:

```ferlium
([1, 2, 3] |> iter() |> map(|x| x as float) |> collect(): [_])
```

## Combining and slicing sequences

Ferlium includes functions to process sequences, producing iterators.

### Pairing with `zip`

`zip` pairs elements from two sequences into tuples, stopping at the shorter one:

```ferlium
([0, 1, 2] |> zip(["first", "second", "third"]) |> collect(): [_])
```

### Indexing with `enumerate`

`enumerate` pairs each element with its zero-based index:

```ferlium
(["zero", "one", "two"] |> enumerate() |> collect(): [_])
```

This is useful for iterating over a collection with the index of the elements:

```ferlium
for (i, name) in ["zero", "one", "two"] |> enumerate() {
    log(f"{i} = {name}")
}
```

### Limiting with `take` and `skip`

`take(n)` keeps only the first `n` elements; `skip(n)` drops them:

```ferlium
(0..10 |> take(3) |> collect(): [_])
```

```ferlium
(0..5 |> skip(2) |> collect(): [_])
```

If `n` exceeds the sequence length, `take` returns all elements and `skip` returns none.

### Concatenating with `chain`

`chain` appends a second sequence after the first:

```ferlium
(chain([1, 2], [3, 4, 5]) |> collect(): [_])
```

```ferlium
(chain(0..3, 3..6) |> collect(): [_])
```

```ferlium
(chain(["Hello", "world"], ["how", "are", "you", "?"]) |> collect(): [_])
```

Both sequences must have the same element type, but the sequences themselves can be of different types:

```ferlium
(chain(0..2, [2, 3]) |> collect(): [_])
```

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

When the sequence is empty, `join` returns `empty()` for the element type.

You can combine `join` with other functions:

```ferlium
join(chain(["Hello", "world"], ["how", "are", "you", "?"]), " ")
```

### Minimum and maximum

Use `minimum` and `maximum` when the element type is ordered:

```ferlium
[3, 1, 2] |> minimum()
```

```ferlium
[3, 1, 2] |> maximum()
```

These functions require a non-empty sequence and panic on an empty one.

## Splitting sequences

Use `split` to divide a value around a non-empty separator and collect the parts into an array.

### Splitting strings

`split` on a `string` with a `string` separator returns `[string]`:

```ferlium
split("a,b,c", ",")
```

This evaluates to `["a", "b", "c"]`. Like in most languages, if the separator appears at the start, end, or consecutively, empty strings are produced as parts:

```ferlium
split(",a,,", ",")
```

This evaluates to `["", "a", "", ""]`.

### Splitting arrays

`split` on `[A]` with an element separator `A` returns `[[A]]`:

```ferlium
split([0, 1, 0, 2, 0], 0)
```

This evaluates to `[[], [1], [2], []]`.

You can also split with a subarray separator:

```ferlium
split([1, 0, 0, 2, 0, 0, 3], [0, 0])
```

This evaluates to `[[1], [2], [3]]`.

### The separator must be non-empty

Passing an empty separator is a runtime error:

```ferlium,should_panic 
split("abc", "")   // error: separator must not be empty
# ;
split([1, 2], [])  // error: separator must not be empty
```

### Relationship to `join`

`split` and `join` are inverses: splitting a value and then joining the parts with the same separator reconstructs the original:

```ferlium
join(split_iterator("a,b,c", ","), ",")
```

This evaluates to `"a,b,c"`. Note the use of `split_iterator` here, which returns a lazy iterator over the parts rather than collecting them into an array.

## Choosing between collections and iterators

A good rule of thumb is:

- use arrays directly when you want eager results
- use `iter(...)` when you want lazy pipelines
- use `collect()` when you want to switch from lazy iteration back to an eager collection

This keeps code readable and makes evaluation timing explicit from the shape of the pipeline.

## What comes next

The next chapter introduces effects, showing how Ferlium tracks interactions such as reading, writing, and failure alongside ordinary values.
