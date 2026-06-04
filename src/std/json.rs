// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use core::panic;
use std::{
    io::{Cursor, Read},
    str::FromStr,
};

use super::string::String as Str;
use crate::{
    compiler::error::RuntimeErrorKind,
    hir::function::{UnaryNativeFnRFV, UnaryNativeFnRN},
    hir::value::Value,
    module::{Module, Visibility},
    std::{
        array::array_value_from_vec,
        data_value::data_value_type,
        math::{float_value, int_value},
        string::{string_type, string_value},
    },
    types::effects::{PrimitiveEffect, effect, no_effects},
};
use enum_as_inner::EnumAsInner;
use json_event_parser::ReaderJsonParser;
use ustr::ustr;

fn escape_json_string(input: &Str) -> Str {
    let mut output = String::new();
    output.push('"');
    for ch in input.as_ref().chars() {
        match ch {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            '\u{08}' => output.push_str("\\b"),
            '\u{0c}' => output.push_str("\\f"),
            ch if ch.is_control() => output.push_str(&format!("\\u{:04x}", ch as u32)),
            ch => output.push(ch),
        }
    }
    output.push('"');
    Str::new(&output)
}

fn next_event<R: Read>(
    reader: &'_ mut ReaderJsonParser<R>,
) -> Result<json_event_parser::JsonEvent<'_>, RuntimeErrorKind> {
    reader
        .parse_next()
        .map_err(|e| RuntimeErrorKind::InvalidArgument(format!("Failed to parse JSON: {}", e)))
}

#[derive(Debug, EnumAsInner)]
enum ParseResult {
    Value(Value),
    Key(Str),
    EndArray,
    EndObject,
}

fn parse_json_stream<R: Read>(
    reader: &mut ReaderJsonParser<R>,
) -> Result<ParseResult, RuntimeErrorKind> {
    let variant = |tag, value| Value::tuple_variant(ustr(tag), [value]);
    let event = next_event(reader)?;
    use json_event_parser::JsonEvent::*;
    let value = match event {
        Null => Value::unit_variant(ustr("Null")),
        Boolean(b) => variant("Bool", Value::native(b)),
        Number(n) => {
            if let Ok(i) = n.parse::<isize>() {
                variant("Int", int_value(i))
            } else if let Ok(f) = n.parse::<f64>()
                && f.is_finite()
            {
                variant("Float", float_value(f))
            } else {
                return Err(RuntimeErrorKind::InvalidArgument(format!(
                    "Invalid number in JSON: {}",
                    n
                )));
            }
        }
        String(s) => variant("String", string_value(&s)),
        StartArray => {
            let mut items = Vec::new();
            loop {
                let item = parse_json_stream(reader)?;
                match item {
                    ParseResult::Value(v) => items.push(v),
                    ParseResult::Key(_) => panic!("Unexpected object key in array"),
                    ParseResult::EndArray => break,
                    ParseResult::EndObject => panic!("Unexpected end of object in array"),
                }
            }
            variant("Array", array_value_from_vec(items))
        }
        EndArray => return Ok(ParseResult::EndArray),
        StartObject => {
            let mut fields = Vec::new();
            loop {
                let key_or_end = parse_json_stream(reader)?;
                let key = match key_or_end {
                    ParseResult::Value(_) => panic!("Unexpected value in object"),
                    ParseResult::Key(k) => k,
                    ParseResult::EndArray => panic!("Unexpected end of array in object"),
                    ParseResult::EndObject => break,
                };
                let value = parse_json_stream(reader)?
                    .into_value()
                    .expect("Expected value in object");
                let tuple = Value::tuple([string_value(key.as_ref()), value]);
                fields.push(tuple);
            }
            variant("Record", array_value_from_vec(fields))
        }
        EndObject => return Ok(ParseResult::EndObject),
        ObjectKey(s) => return Ok(ParseResult::Key(Str::from_str(&s).unwrap())),
        Eof => panic!("Unexpected end of JSON input"),
    };
    Ok(ParseResult::Value(value))
}

fn parse_json(input: &Str) -> Result<Value, RuntimeErrorKind> {
    let reader = Cursor::new(input.as_ref().as_bytes());
    let mut reader = ReaderJsonParser::new(reader);
    let value = parse_json_stream(&mut reader)?;
    let eof_event = next_event(&mut reader)?;
    if let json_event_parser::JsonEvent::Eof = eof_event {
        Ok(value.into_value().unwrap())
    } else {
        panic!(
            "Expected end of input after JSON value, found {:?}",
            eof_event
        )
    }
}

pub fn add_to_module(to: &mut Module) {
    to.add_function_with_visibility(
        ustr("escape_json_string"),
        UnaryNativeFnRN::description_with_ty(
            escape_json_string,
            ["value"],
            "Escapes a string as a JSON string literal.",
            string_type(),
            string_type(),
            no_effects(),
        ),
        Visibility::Module,
    );
    to.add_function(
        ustr("parse_json"),
        UnaryNativeFnRFV::description_with_ty(
            parse_json,
            ["json"],
            "Parses JSON into a data value.",
            string_type(),
            data_value_type(),
            effect(PrimitiveEffect::Fallible),
        ),
    );
}
