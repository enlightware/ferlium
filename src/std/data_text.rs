// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ustr::ustr;

use crate::{
    compiler::error::RuntimeErrorKind,
    hir::{
        function::{UnaryNativeFnRFV, UnaryNativeFnRN},
        value::Value,
    },
    module::{Module, Visibility},
    std::{
        array::array_value_from_vec,
        data_value::data_value_type,
        math::{float_value, int_value},
        string::{String as Str, string_type, string_value},
    },
    types::effects::{PrimitiveEffect, effect, no_effects},
};

fn data_variant(tag: &str, value: Value) -> Value {
    Value::tuple_variant(ustr(tag), [value])
}

fn data_unit_variant(tag: &str) -> Value {
    Value::unit_variant(ustr(tag))
}

fn data_array_variant(tag: &str, values: Vec<Value>) -> Value {
    data_variant(tag, array_value_from_vec(values))
}

fn data_object_entry(name: &str, value: Value) -> Value {
    Value::tuple([string_value(name), value])
}

fn data_map_entry(key: Value, value: Value) -> Value {
    Value::tuple([key, value])
}

fn data_enum_variant(name: &str, payload: Value) -> Value {
    let record = Value::tuple([string_value(name), payload]);
    Value::raw_variant(ustr("EnumVariant"), record)
}

fn escape_string(value: &str) -> String {
    let mut output = String::new();
    output.push('"');
    for ch in value.chars() {
        match ch {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            ch if ch.is_control() => output.push_str(&format!("\\u{{{:x}}}", ch as u32)),
            ch => output.push(ch),
        }
    }
    output.push('"');
    output
}

fn is_object_data(value: &Value) -> bool {
    value
        .as_variant()
        .is_some_and(|variant| variant.tag.as_str() == "Object")
}

fn escape_data_text_string(input: &Str) -> Str {
    Str::new(&escape_string(input.as_ref()))
}

struct Parser<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, pos: 0 }
    }

    fn parse(mut self) -> Result<Value, RuntimeErrorKind> {
        let value = self.parse_value()?;
        self.skip_ws_and_comments()?;
        if self.pos == self.input.len() {
            Ok(value)
        } else {
            Err(self.error("Expected end of input"))
        }
    }

    fn error(&self, message: &str) -> RuntimeErrorKind {
        RuntimeErrorKind::InvalidArgument(format!("{message} at byte {}", self.pos))
    }

    fn peek_char(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    fn bump_char(&mut self) -> Option<char> {
        let ch = self.peek_char()?;
        self.pos += ch.len_utf8();
        Some(ch)
    }

    fn consume_char(&mut self, expected: char) -> bool {
        if self.peek_char() == Some(expected) {
            self.bump_char();
            true
        } else {
            false
        }
    }

    fn expect_char(&mut self, expected: char) -> Result<(), RuntimeErrorKind> {
        if self.consume_char(expected) {
            Ok(())
        } else {
            Err(self.error(&format!("Expected `{expected}`")))
        }
    }

    fn starts_with(&self, value: &str) -> bool {
        self.input[self.pos..].starts_with(value)
    }

    fn skip_ws_and_comments(&mut self) -> Result<(), RuntimeErrorKind> {
        loop {
            while self.peek_char().is_some_and(char::is_whitespace) {
                self.bump_char();
            }
            if self.starts_with("//") {
                while self.peek_char().is_some_and(|ch| ch != '\n') {
                    self.bump_char();
                }
            } else if self.starts_with("/*") {
                self.pos += 2;
                while !self.starts_with("*/") {
                    if self.bump_char().is_none() {
                        return Err(self.error("Unterminated block comment"));
                    }
                }
                self.pos += 2;
            } else {
                return Ok(());
            }
        }
    }

    fn parse_value(&mut self) -> Result<Value, RuntimeErrorKind> {
        self.skip_ws_and_comments()?;
        match self.peek_char() {
            Some('"') => self
                .parse_string()
                .map(|s| data_variant("String", string_value(&s))),
            Some('[') => self
                .parse_sequence('[', ']')
                .map(|values| data_array_variant("Array", values)),
            Some('(') => self.parse_paren_value(),
            Some('{') => self.parse_object(),
            Some('-' | '0'..='9') => self.parse_number(),
            Some(ch) if is_identifier_start(ch) => self.parse_identifier_value(),
            Some(_) => Err(self.error("Expected data value")),
            None => Err(self.error("Expected data value")),
        }
    }

    fn parse_paren_value(&mut self) -> Result<Value, RuntimeErrorKind> {
        self.expect_char('(')?;
        self.skip_ws_and_comments()?;
        if self.consume_char(')') {
            return Ok(data_unit_variant("Unit"));
        }
        let first = self.parse_value()?;
        self.skip_ws_and_comments()?;
        if !self.consume_char(',') {
            self.skip_ws_and_comments()?;
            self.expect_char(')')?;
            return Ok(first);
        }
        let mut values = vec![first];
        loop {
            self.skip_ws_and_comments()?;
            if self.consume_char(')') {
                break;
            }
            values.push(self.parse_value()?);
            self.skip_ws_and_comments()?;
            if self.consume_char(',') {
                continue;
            }
            self.expect_char(')')?;
            break;
        }
        Ok(data_array_variant("Tuple", values))
    }

    fn parse_object(&mut self) -> Result<Value, RuntimeErrorKind> {
        self.expect_char('{')?;
        let mut entries = Vec::new();
        loop {
            self.skip_ws_and_comments()?;
            if self.consume_char('}') {
                break;
            }
            let name = if self.peek_char() == Some('"') {
                self.parse_string()?
            } else {
                self.parse_identifier()?
            };
            self.skip_ws_and_comments()?;
            self.expect_char(':')?;
            let value = self.parse_value()?;
            entries.push(data_object_entry(&name, value));
            self.skip_ws_and_comments()?;
            if self.consume_char(',') {
                continue;
            }
            self.expect_char('}')?;
            break;
        }
        Ok(data_array_variant("Object", entries))
    }

    fn parse_sequence(&mut self, open: char, close: char) -> Result<Vec<Value>, RuntimeErrorKind> {
        self.expect_char(open)?;
        let mut values = Vec::new();
        loop {
            self.skip_ws_and_comments()?;
            if self.consume_char(close) {
                break;
            }
            values.push(self.parse_value()?);
            self.skip_ws_and_comments()?;
            if self.consume_char(',') {
                continue;
            }
            self.expect_char(close)?;
            break;
        }
        Ok(values)
    }

    fn parse_identifier_value(&mut self) -> Result<Value, RuntimeErrorKind> {
        let ident = self.parse_identifier()?;
        match ident.as_str() {
            "null" => Ok(data_unit_variant("Null")),
            "true" => Ok(data_variant("Bool", Value::native(true))),
            "false" => Ok(data_variant("Bool", Value::native(false))),
            "set" => {
                self.skip_ws_and_comments()?;
                let values = self.parse_sequence('{', '}')?;
                Ok(data_array_variant("Set", values))
            }
            "map" => {
                self.skip_ws_and_comments()?;
                let pairs = self.parse_map_entries()?;
                Ok(data_array_variant("Map", pairs))
            }
            _ => {
                self.skip_ws_and_comments()?;
                if self.consume_char('(') {
                    self.skip_ws_and_comments()?;
                    if self.consume_char(')') {
                        return Ok(data_enum_variant(&ident, data_unit_variant("Unit")));
                    }
                    let mut args = Vec::new();
                    loop {
                        args.push(self.parse_value()?);
                        self.skip_ws_and_comments()?;
                        if self.consume_char(',') {
                            self.skip_ws_and_comments()?;
                            if self.consume_char(')') {
                                break;
                            }
                            continue;
                        }
                        self.expect_char(')')?;
                        break;
                    }
                    let payload = if args.len() == 1 && is_object_data(&args[0]) {
                        args.pop().expect("single argument exists")
                    } else {
                        data_array_variant("Tuple", args)
                    };
                    Ok(data_enum_variant(&ident, payload))
                } else {
                    Ok(data_enum_variant(&ident, data_unit_variant("Unit")))
                }
            }
        }
    }

    fn parse_map_entries(&mut self) -> Result<Vec<Value>, RuntimeErrorKind> {
        self.expect_char('{')?;
        let mut entries = Vec::new();
        loop {
            self.skip_ws_and_comments()?;
            if self.consume_char('}') {
                break;
            }
            let key = self.parse_value()?;
            self.skip_ws_and_comments()?;
            if !self.starts_with("=>") {
                return Err(self.error("Expected `=>`"));
            }
            self.pos += 2;
            let value = self.parse_value()?;
            entries.push(data_map_entry(key, value));
            self.skip_ws_and_comments()?;
            if self.consume_char(',') {
                continue;
            }
            self.expect_char('}')?;
            break;
        }
        Ok(entries)
    }

    fn parse_identifier(&mut self) -> Result<String, RuntimeErrorKind> {
        self.skip_ws_and_comments()?;
        let Some(first) = self.peek_char() else {
            return Err(self.error("Expected identifier"));
        };
        if !is_identifier_start(first) {
            return Err(self.error("Expected identifier"));
        }
        let start = self.pos;
        self.bump_char();
        while self.peek_char().is_some_and(is_identifier_continue) {
            self.bump_char();
        }
        Ok(self.input[start..self.pos].to_string())
    }

    fn parse_string(&mut self) -> Result<String, RuntimeErrorKind> {
        self.expect_char('"')?;
        let mut output = String::new();
        loop {
            let Some(ch) = self.bump_char() else {
                return Err(self.error("Unterminated string"));
            };
            match ch {
                '"' => return Ok(output),
                '\\' => output.push(self.parse_escape()?),
                ch => output.push(ch),
            }
        }
    }

    fn parse_escape(&mut self) -> Result<char, RuntimeErrorKind> {
        let Some(ch) = self.bump_char() else {
            return Err(self.error("Unterminated escape"));
        };
        match ch {
            '"' => Ok('"'),
            '\\' => Ok('\\'),
            'n' => Ok('\n'),
            'r' => Ok('\r'),
            't' => Ok('\t'),
            'u' => {
                self.expect_char('{')?;
                let start = self.pos;
                while self.peek_char().is_some_and(|ch| ch != '}') {
                    self.bump_char();
                }
                let digits = &self.input[start..self.pos];
                self.expect_char('}')?;
                let code = u32::from_str_radix(digits, 16)
                    .map_err(|_| self.error("Invalid unicode escape"))?;
                char::from_u32(code).ok_or_else(|| self.error("Invalid unicode scalar value"))
            }
            _ => Err(self.error("Invalid escape")),
        }
    }

    fn parse_number(&mut self) -> Result<Value, RuntimeErrorKind> {
        let start = self.pos;
        self.consume_char('-');
        while self.peek_char().is_some_and(|ch| ch.is_ascii_digit()) {
            self.bump_char();
        }
        let mut is_float = false;
        if self.consume_char('.') {
            is_float = true;
            while self.peek_char().is_some_and(|ch| ch.is_ascii_digit()) {
                self.bump_char();
            }
        }
        if self.peek_char().is_some_and(|ch| ch == 'e' || ch == 'E') {
            is_float = true;
            self.bump_char();
            if self.peek_char().is_some_and(|ch| ch == '+' || ch == '-') {
                self.bump_char();
            }
            while self.peek_char().is_some_and(|ch| ch.is_ascii_digit()) {
                self.bump_char();
            }
        }
        let text = &self.input[start..self.pos];
        if is_float {
            let value = text
                .parse::<f64>()
                .map_err(|_| self.error("Invalid float literal"))?;
            if !value.is_finite() {
                return Err(self.error("Invalid non-finite float literal"));
            }
            Ok(data_variant("Float", float_value(value)))
        } else {
            let value = text
                .parse::<isize>()
                .map_err(|_| self.error("Invalid int literal"))?;
            Ok(data_variant("Int", int_value(value)))
        }
    }
}

fn is_identifier_start(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphabetic()
}

fn is_identifier_continue(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphanumeric()
}

fn parse_data_text(input: &Str) -> Result<Value, RuntimeErrorKind> {
    Parser::new(input.as_ref()).parse()
}

pub fn add_to_module(to: &mut Module) {
    to.add_function_with_visibility(
        ustr("escape_data_text_string"),
        UnaryNativeFnRN::description_with_ty(
            escape_data_text_string,
            ["value"],
            "Escapes a string as a Ferlium data-text string literal.",
            string_type(),
            string_type(),
            no_effects(),
        ),
        Visibility::Module,
    );
    to.add_function(
        ustr("parse_data_text"),
        UnaryNativeFnRFV::description_with_ty(
            parse_data_text,
            ["text"],
            "Parses Ferlium data text into a data value.",
            string_type(),
            data_value_type(),
            effect(PrimitiveEffect::Fallible),
        ),
    );
}
