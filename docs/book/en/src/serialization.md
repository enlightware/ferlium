# Serialization

Ferlium serializes typed values through a dynamic data model named `DataValue`.
The `Serialize` trait converts a typed value to `DataValue`, and `Deserialize` converts a `DataValue` back to an expected typed value.

```ferlium
let data = serialize({ host: "localhost", port: 8080 });
let config: { host: string, port: int } = deserialize(data);
```

## Data Values

`DataValue` is an interchange tree used by serialization codecs:

```ferlium,ignore
DataValue::Null
DataValue::Unit
DataValue::Bool(true)
DataValue::Int(1)
DataValue::Float(1.5)
DataValue::String("hello")
DataValue::Array([DataValue::Int(1), DataValue::Int(2)])
DataValue::Tuple([DataValue::Int(1), DataValue::String("x")])
DataValue::Object([("host", DataValue::String("localhost"))])
DataValue::Set([DataValue::String("a"), DataValue::String("b")])
DataValue::Map([(DataValue::String("a"), DataValue::Int(1))])
DataValue::EnumVariant { name: "Some", payload: DataValue::Tuple([DataValue::Int(1)]) }
```

`Null` represents external null data, such as JSON `null`.
`Unit` represents the Ferlium value `()`.

Arrays, tuples, objects, sets, maps, and enum variants keep distinct shapes in `DataValue`.
JSON may still encode several of these as arrays or objects because JSON has fewer data shapes.

## JSON

JSON is a codec over `DataValue`.

```ferlium
let text = json_encode({ host: "localhost", port: 8080 });
let config: { host: string, port: int } = json_decode(text);
```

JSON input maps to `DataValue` as follows:

- `null` becomes `Null`
- booleans, numbers, and strings become `Bool`, `Int` or `Float`, and `String`
- arrays become `Array`
- objects become `Object`

Maps are encoded to JSON as arrays of key-value pairs.
This keeps the representation valid even when keys are not strings.

## Ferlium Data Text

Ferlium data text is a human-readable codec over `DataValue`.
It accepts inert value syntax only; it does not evaluate Ferlium expressions.

```ferlium
let text = data_text_encode({
    host: "localhost",
    port: 8080,
    retry: Some(3),
});

let config: { host: string, port: int, retry: Option<int> } = data_text_decode(text);
```

Data text supports:

- `null`, `()`, booleans, numbers, and strings
- arrays: `[1, 2, 3]`
- tuples: `(1, "x")`
- objects: `{ host: "localhost", port: 8080 }`
- enum variants: `None`, `Some(1)`
- sets: `set { 1, 2, 3 }`
- maps: `map { "a" => 1, "b" => 2 }`
- comments and trailing commas

It does not support operators, function calls, bindings, control flow, imports, or string interpolation.
The expected target type guides deserialization.
