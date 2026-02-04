# User-Defined Types

Ferlium lets you model domain data with your own types: product types for combining fields and sum types for choosing between alternatives.
This chapter introduces these constructs and shows how naming types improves readability and safety.

## Type Aliases

Type aliases give a name to an existing type expression:

```ferlium
type UserId = int;
type Point = (int, int);
type PersonView = { name: string, age: int };
```

Aliases improve readability, but they do not create a new nominal type.
For type checking, they are treated as the underlying type.

## Product Types

Product types group several values into a single value.
They are called “product” types because the number of possible values is the product of the possibilities of their components.

### Tuples

A tuple stores values by position.

```ferlium
let point = (10, 20);
let x = point.0;
let y = point.1;
```

Tuple access uses numeric projections (`.0`, `.1`, ...).

```ferlium
let nested = (1, (3, (2, 4, 5)));
let value = nested.1.1.2;
```

Each element can have a different type:

```ferlium
let mixed = (1, "hello", true);
```

### Records

A record stores values by field name.

```ferlium
let person = { name: "Ada", age: 36 };
let n = person.name;
let a = person.age;
```

Record access uses field projections (`.field_name`).

```ferlium
let cfg = { host: "localhost", port: 8080 };
cfg.port
```

### Inference with product type values

Inference works naturally with tuples and records: the compiler infers field and element types from their construction and usage.

```ferlium
let pair = (1, true);              // inferred as (int, bool)
let user = { name: "A", age: 30 }; // inferred as { name: string, age: int }
```

## Sum Types

Variants or sum types let a value be one of several alternatives.
Each alternative has a name and an optional payload of associated data.
The name of the alternative is called a **tag**.

```ferlium,ignore
None           // tag: None, no data
Some(42)       // tag: Some, data: int
RGB(255, 0, 0) // tag: RGB, data: (int, int, int)
```

At runtime, a value of a sum type carries exactly one tag, together with the payload of that alternative.
These types are called “sum” types because their number of possible values is the sum of the possibilities of their alternatives.

You can also define a sum type with an alias when you want to limit the alternatives to a specific set:

```ferlium
type Shape = Circle(float) | Rectangle { width: float, height: float };

let a: Shape = Circle(5.0);
```

### Inference with sum type values

Inference works with sum types as well.
The compiler infers the type of a tagged value from its construction and usage.
For example, the function:

```ferlium
fn none() {
    None
}
```

returns a value whose type includes the `None` alternative, because the caller may choose any compatible sum type that contains `None`.

If you want to specify a particular sum type, you can add an annotation:
```ferlium
fn none() -> None | Some(int) {
    None
}
```

As we will see later, matching on a sum type value also narrows its type to the relevant alternative, which is how you can access the payload data. Also, this can constrain the set of valid alternatives.

## Nominal Types

Nominal types, sometimes called “newtypes”, are defined with a name and a structure, and they are distinct from other types even if their underlying structure is the same.
They make domain intent explicit and prevent accidental mixing of values that share the same underlying representation.

### Nominal Product Types: `struct`

A `struct` defines a new nominal product type.
It supports empty, tuple, and record forms:

```ferlium
struct Empty {}
struct Point(int, int)
struct Person { name: string, age: int }
```

Using a struct gives nominal identity to the type, so even if two structs have the same underlying fields, they are not the same type:

```ferlium
struct UserId(int)
struct ProductId(int)

let u = UserId(10);
let p = ProductId(10);

let raw = u.0;
```

Here, `UserId` and `ProductId` are distinct types, even though both wrap `int`.

### Nominal Sum Types: `enum`

An `enum` defines a new nominal sum type.
Each alternative can have its own payload:

```ferlium
enum Message {
    Quit,
    Write(string),
    Move { x: int, y: int }
}
```

Enum variants can be:

- unit-like, as with `Quit`
- tuple-like, as with `Write(string)`
- record-like, as with `Move { x: int, y: int }`

Construction uses `TypeName::VariantName`:

```ferlium
# enum Message {
#     Quit,
#     Write(string),
#     Move { x: int, y: int }
# }
let m1 = Message::Quit;
let m2 = Message::Write("hello");
let m3 = Message::Move { x: 10, y: 20 };
```

## Structural vs Nominal Types

As seen in this chapter, Ferlium supports both structural and nominal reasoning.

- Tuples, records and sum types are structural: compatibility depends on shape.
- Named types — `struct` and `enum` — are nominal: compatibility depends on the declared type name rather than on structure alone.

Example:

```ferlium
struct Age(int)
struct Person1 { age: Age }
struct Person2 { age: Age }

fn age_value(d) { d.age.0 }      // works for values with compatible structure
fn age1(d: Person1) { d.age.0 }  // requires exactly Person1
```

`age_value` can be used with either `Person1` or `Person2` because it depends only on the required structure.
`age1` is explicitly nominal and accepts only `Person1`.

### Note on `Repr`

Ferlium includes an internal marker concept called `Repr` that links a named type to the value representation it exposes. In practice, this is why projections and pattern matching behave uniformly across structural and nominal data, while named types remain distinct during type checking.

You do not write or define `Repr` yourself.

## What comes next

The next chapter expands pattern matching for structured data, so you can inspect and branch on tuples, records, and enum variants directly.
