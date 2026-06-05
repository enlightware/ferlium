// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use indoc::indoc;
use test_log::test;
use ustr::ustr;

use crate::harness::{TestSession, bool, float, int, string, unit, variant_0, variant_t1};
use ferlium::{
    compiler::error::RuntimeErrorKind,
    hir::value::Value,
    std::option::{none, some},
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn serde_serialize() {
    let mut session = TestSession::new();
    // basic types
    assert_val_eq!(session.run("serialize(())"), variant_0("Unit"));
    assert_val_eq!(
        session.run("serialize(true)"),
        variant_t1("Bool", bool(true))
    );
    assert_val_eq!(session.run("serialize(1)"), variant_t1("Int", int(1)));
    assert_val_eq!(
        session.run("serialize(1.0)"),
        variant_t1("Float", float(1.0))
    );
    assert_val_eq!(
        session.run(r#"serialize("hello")"#),
        variant_t1("String", string("hello"))
    );
    assert_val_eq!(
        session.run("serialize([1])"),
        variant_t1("Array", array![variant_t1("Int", int(1))])
    );
    assert_val_eq!(
        session.run("serialize([1.0])"),
        variant_t1("Array", array![variant_t1("Float", float(1.0))])
    );

    // variants
    assert_val_eq!(
        session.run("serialize(None)"),
        Value::raw_variant(ustr("Variant"), tuple!(string("None"), variant_0("Unit")))
    );
    assert_val_eq!(
        session.run("serialize(Some(1.0))"),
        Value::raw_variant(
            ustr("Variant"),
            tuple!(
                string("Some"),
                variant_t1("Tuple", array![variant_t1("Float", float(1.0))])
            )
        )
    );

    // tuples
    assert_val_eq!(
        session.run("serialize((1, ))"),
        variant_t1("Tuple", array![variant_t1("Int", int(1))])
    );
    assert_val_eq!(
        session.run("serialize((1, 2))"),
        variant_t1(
            "Tuple",
            array![variant_t1("Int", int(1)), variant_t1("Int", int(2))]
        )
    );
    assert_val_eq!(
        session.run("serialize((1, 2.0, true))"),
        variant_t1(
            "Tuple",
            array![
                variant_t1("Int", int(1)),
                variant_t1("Float", float(2.)),
                variant_t1("Bool", bool(true))
            ]
        )
    );

    // records
    assert_val_eq!(
        session.run("serialize({a: 1, })"),
        variant_t1(
            "Record",
            array![tuple!(string("a"), variant_t1("Int", int(1)))]
        )
    );
    assert_val_eq!(
        session.run("serialize({a: 1, b: 2})"),
        variant_t1(
            "Record",
            array![
                tuple!(string("a"), variant_t1("Int", int(1))),
                tuple!(string("b"), variant_t1("Int", int(2)))
            ]
        )
    );
    assert_val_eq!(
        session.run("serialize({a: 1, b: 2.0, c: true})"),
        variant_t1(
            "Record",
            array![
                tuple!(string("a"), variant_t1("Int", int(1))),
                tuple!(string("b"), variant_t1("Float", float(2.))),
                tuple!(string("c"), variant_t1("Bool", bool(true)))
            ]
        )
    );

    // named types, by default serialize as their inner type
    assert_val_eq!(
        session.run("struct Age(float) serialize(Age(1.0))"),
        session.run("serialize((1.0, ))")
    );
    assert_val_eq!(
        session.run(
            "struct Person { name: string, age: float } serialize( Person { name: \"Alice\", age: 30.0 })"
        ),
        session.run("serialize({name: \"Alice\", age: 30.0})")
    );
    assert_val_eq!(
        session.run("enum SimpleColor { Red, Green, Blue } serialize(SimpleColor::Blue)"),
        session.run("serialize(Blue)")
    )
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn serde_deserialize() {
    let mut session = TestSession::new();
    // basic types
    assert_val_eq!(
        session.run("(deserialize(serialize(())) : ())"),
        Value::unit()
    );
    assert_val_eq!(
        session.run("(deserialize(serialize(true)) : bool)"),
        bool(true)
    );
    assert_val_eq!(session.run("(deserialize(serialize(1)): int)"), int(1));
    assert_val_eq!(
        session.run("(deserialize(serialize(1.0)): float)"),
        float(1.0)
    );
    assert_val_eq!(
        session.run(r#"(deserialize(serialize("hello")): string)"#),
        string("hello")
    );
    assert_val_eq!(
        session
            .run("(deserialize(DataValue::Array([DataValue::Int(1), DataValue::Int(1)])): [int])"),
        int_a![1, 1]
    );
    assert_val_eq!(
        session.run(
            "(deserialize(DataValue::Array([DataValue::Int(1), DataValue::Int(1)])): [float])"
        ),
        array![float(1.0), float(1.0)]
    );

    // variants
    // TODO: once https://github.com/enlightware/ferlium/issues/75 is fixed
    // add (deserialize(serialize(None)): None)
    assert_val_eq!(
        session.run("(deserialize(serialize(None)): None | Some(int))"),
        none()
    );
    assert_val_eq!(
        session.run("(deserialize(serialize(Some(1))): None | Some(int))"),
        some(int(1))
    );
    assert_val_eq!(
        session.run("(deserialize(serialize(Some((1: int)))): None | Some(int))"),
        some(int(1))
    );

    // tuples
    assert_val_eq!(
        session.run("(deserialize(serialize( (1, ) )): (int, ))"),
        tuple!(int(1))
    );
    assert_val_eq!(
        session.run("(deserialize(serialize( (1, 1, true) )): (int, float, bool))"),
        tuple!(int(1), float(1.0), bool(true))
    );

    // records
    assert_val_eq!(
        session.run("(deserialize(serialize( {a: 1, } )): {a: int})"),
        tuple!(int(1))
    );
    assert_val_eq!(
        session.run("(deserialize(serialize( {a: 1, } )): {a: float})"),
        tuple!(float(1.0))
    );
    assert_val_eq!(
        session.run("(deserialize(serialize( { b: true, a: 1 } )): {a: int, b: bool})"),
        tuple!(int(1), bool(true))
    );
    assert_val_eq!(
        session.run("(deserialize(serialize( { b: true, a: 1 } )): {a: int, b: bool})"),
        tuple!(int(1), bool(true))
    );

    // named types, by default de-serialize as their inner type
    assert_val_eq!(
        session.run("struct Age(float) (deserialize(serialize(Age(1.0))): Age)"),
        session.run("struct Age(float) (deserialize(serialize((1.0, ))): Age)")
    );
    assert_val_eq!(
        session.run(
            "struct Person { name: string, age: float } (deserialize(serialize( Person { name: \"Alice\", age: 30.0 })): Person)"
        ),
        session.run(
            "struct Person { name: string, age: float } (deserialize(serialize({name: \"Alice\", age: 30.0})): Person)"
        )
    );
    assert_val_eq!(
        session.run(
            "enum SimpleColor { Red, Green, Blue } (deserialize(serialize(SimpleColor::Blue)): SimpleColor)"
        ),
        session.run("enum SimpleColor { Red, Green, Blue } (deserialize(serialize(Blue)): SimpleColor)")
    );

    // errors
    session
        .fail_compilation(r#"deserialize(1)"#)
        .expect_trait_impl_not_found("Num", &["Self = DataValue"]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn serialize_with_type_ascription() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run("fn test() -> DataValue { DataValue::Array([serialize(0)]) } test()"),
        variant_t1("Array", array![variant_t1("Int", int(0))])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn json_serialization_roundtrip() {
    let mut session = TestSession::new();
    // bool, low-level JSON functions
    assert_val_eq!(
        session.run("(deserialize(parse_json(to_json(serialize(true)))): bool)"),
        bool(true)
    );
    // bool
    assert_val_eq!(
        session.run("(json_decode(json_encode(true)): bool)"),
        bool(true)
    );
    // unit
    assert_val_eq!(
        session.run("(json_decode(json_encode(())): ())"),
        Value::unit()
    );
    // int
    assert_val_eq!(session.run("(json_decode(json_encode(42)): int)"), int(42));
    // float
    assert_val_eq!(
        session.run("(json_decode(json_encode(3.14)): float)"),
        float(3.14)
    );
    // string
    assert_val_eq!(
        session.run(r#"(json_decode(json_encode("hello")): string)"#),
        string("hello")
    );
    assert_val_eq!(
        session.run(
            r#"to_json(DataValue::Record([("quoted key", DataValue::String("hello \"world\"\n"))]))"#
        ),
        string(r#"{"quoted key":"hello \"world\"\n"}"#)
    );
    // array of ints
    assert_val_eq!(
        session.run("(json_decode(json_encode([1, 2, 3])): [int])"),
        int_a![1, 2, 3]
    );
    // array of floats
    assert_val_eq!(
        session.run("(json_decode(json_encode([1.5, 2.5, 3.5])): [float])"),
        float_a![1.5, 2.5, 3.5]
    );
    // None variant
    assert_val_eq!(
        session.run("(json_decode(json_encode(None)): None | Some(int))"),
        none()
    );
    // Some(int) variant
    assert_val_eq!(
        session.run("(json_decode(json_encode(Some((42: int)))): None | Some(int))"),
        some(int(42))
    );
    // tuple
    assert_val_eq!(
        session.run("(json_decode(json_encode((1, 2.0, true))): (int, float, bool))"),
        tuple!(int(1), float(2.0), bool(true))
    );
    // record
    assert_val_eq!(
        session.run(r#"(json_decode(json_encode({a: 1, b: true})): {a: int, b: bool})"#),
        tuple!(int(1), bool(true))
    );
    // raw JSON parsing - simple object
    assert_val_eq!(
        session.run(r#"(json_decode("{\"a\": 1, \"b\": true}"): {a: int, b: bool})"#),
        tuple!(int(1), bool(true))
    );
    // complex object roundtrip with nested array
    assert_val_eq!(
        session.run(indoc! { r#"
            (
                json_decode(json_encode({name: "Alice", age: 30, is_student: false, scores: [85.5, 92.0, 78.0]})):
                {age: int, is_student: bool, name: string, scores: [float]}
            )
        "# }),
        tuple!(int(30), bool(false), string("Alice"), float_a![85.5, 92.0, 78.0])
    );
    // raw JSON parsing - complex object with nested array
    let json_str =
        r#"{"name": "Alice", "age": 30, "is_student": false, "scores": [85.5, 92.0, 78.0]}"#;
    assert_val_eq!(
        session.run(&format!(
            r#"(json_decode("{}"): {{age: int, is_student: bool, name: string, scores: [float]}})"#,
            json_str.replace('"', "\\\"")
        )),
        tuple!(
            int(30),
            bool(false),
            string("Alice"),
            float_a![85.5, 92.0, 78.0]
        )
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn json_rejects_non_finite_float() {
    let mut session = TestSession::new();
    assert_eq!(
        session.fail_run(r#"json_decode("1e999")"#),
        RuntimeErrorKind::InvalidArgument("Invalid number in JSON: 1e999".into())
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn data_text_serialization_roundtrip() {
    let mut session = TestSession::new();

    assert_val_eq!(
        session.run("to_data_text(serialize((1, 2)))"),
        string("(1, 2)")
    );
    assert_val_eq!(
        session.run("to_data_text(serialize([1, 2]))"),
        string("[1, 2]")
    );
    assert_val_eq!(
        session.run("to_data_text(serialize(Some((42: int))))"),
        string("Some(42)")
    );
    assert_val_eq!(
        session.run(r#"(data_text_decode("Some(42)"): Option<int>)"#),
        some(int(42))
    );
    assert_val_eq!(
        session.run(indoc! { r#"
            (data_text_decode("{ // comment
                port: 8080,
                enabled: true,
            }"): {enabled: bool, port: int})"#
        }),
        tuple!(bool(true), int(8080))
    );
    assert_val_eq!(
        session.run(indoc! { r#"
            let decoded: HashSet<int> = data_text_decode("set { 1, 2, }");
            len(decoded)
        "# }),
        int(2)
    );
    assert_val_eq!(
        session.run(indoc! { r#"
            let decoded: HashMap<string, int> = data_text_decode("map { \"a\" => 1, \"b\" => 2, }");
            len(decoded) == 2
                and map_get(decoded, "a") == Some(1)
                and map_get(decoded, "b") == Some(2)
        "# }),
        bool(true)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn data_text_codec_source_like_shapes() {
    let mut session = TestSession::new();

    assert_val_eq!(
        session.run(r#"to_data_text(parse_data_text("set {}"))"#),
        string("set {}")
    );
    assert_val_eq!(
        session.run(r#"to_data_text(parse_data_text("map {}"))"#),
        string("map {}")
    );
    assert_val_eq!(
        session.run(r#"to_data_text(parse_data_text("(1,)"))"#),
        string("(1,)")
    );
    assert_val_eq!(
        session.run(r#"to_data_text(parse_data_text("(1)"))"#),
        string("1")
    );
    assert_val_eq!(
        session.run(r#"to_data_text(parse_data_text("{\"host-name\": \"localhost\"}"))"#),
        string(r#"{ "host-name": "localhost" }"#)
    );
    assert_val_eq!(
        session.run(r#"to_data_text(parse_data_text("{enabled: true, port: 8080}"))"#),
        string(r#"{ enabled: true, port: 8080 }"#)
    );
    assert_val_eq!(
        session.run(r#"to_data_text(parse_data_text("\"hello\\nworld\""))"#),
        string(r#""hello\nworld""#)
    );
    assert_val_eq!(
        session.run(r#"to_data_text(DataValue::String("quote: \", slash: \\, tab: \t"))"#),
        string(r#""quote: \", slash: \\, tab: \t""#)
    );
    assert_val_eq!(
        session.run(r#"to_data_text(DataValue::String("newline: \n, carriage: \r"))"#),
        string(r#""newline: \n, carriage: \r""#)
    );
    assert_val_eq!(
        session.run(r#"to_data_text(DataValue::String("nul: \u{0}, unit: \u{1f}"))"#),
        string(r#""nul: \u{0}, unit: \u{1f}""#)
    );
    assert_val_eq!(
        session.run(r#"to_data_text(parse_data_text("\"nul: \\u{0}, unit: \\u{1f}\""))"#),
        string(r#""nul: \u{0}, unit: \u{1f}""#)
    );
    assert_val_eq!(
        session.run(indoc! { r#"
            let decoded: HashSet<int> = data_text_decode("set {}");
            len(decoded)
        "# }),
        int(0)
    );
    assert_val_eq!(
        session.run(indoc! { r#"
            let decoded: HashMap<string, int> = data_text_decode("map {}");
            len(decoded)
        "# }),
        int(0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn data_value_variant_record_payload_is_direct() {
    let mut session = TestSession::new();

    assert_val_eq!(
        session.run(indoc! { r#"
            let value = DataValue::Variant {
                name: "Some",
                payload: DataValue::String("hello"),
            };
            to_data_text(value)
        "# }),
        string(r#"Some("hello")"#)
    );
    assert_val_eq!(
        session.run(indoc! { r#"
            {
                let value = DataValue::Variant {
                    name: "Some",
                    payload: DataValue::String("hello"),
                };
                ();
            }
        "# }),
        unit()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn set_and_map_serialization_roundtrip() {
    let mut session = TestSession::new();

    assert_val_eq!(
        session.run(indoc! { r#"
            let mut values = hash_set_new();
            set_insert(values, 1);
            set_insert(values, 2);
            let text = data_text_encode(values);
            let decoded: HashSet<int> = data_text_decode(text);
            len(decoded) == 2 and set_contains(decoded, 1) and set_contains(decoded, 2)
        "# }),
        bool(true)
    );
    assert_val_eq!(
        session.run(indoc! { r#"
            let mut values = hash_map_new();
            map_insert(values, "a", 1);
            map_insert(values, "b", 2);
            let text = data_text_encode(values);
            let decoded: HashMap<string, int> = data_text_decode(text);
            len(decoded) == 2
                and map_get(decoded, "a") == Some(1)
                and map_get(decoded, "b") == Some(2)
        "# }),
        bool(true)
    );
    assert_val_eq!(
        session.run(indoc! { r#"
            let mut values = hash_set_new();
            set_insert(values, 1);
            data_text_encode(values)
        "# }),
        string("set { 1 }")
    );
    assert_val_eq!(
        session.run(indoc! { r#"
            let mut values = hash_map_new();
            map_insert(values, "a", 1);
            data_text_encode(values)
        "# }),
        string(r#"map { "a" => 1 }"#)
    );
}
