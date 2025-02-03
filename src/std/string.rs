// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    fmt::{self, Display},
    ops::Deref,
    rc::Rc,
    str::FromStr,
};

use ustr::ustr;

use crate::{
    cached_primitive_ty,
    effects::no_effects,
    function::{
        BinaryNativeFnMNN, BinaryNativeFnNNN, TernaryNativeFnNNNN, UnaryNativeFnNN, UnaryNativeFnVN,
    },
    module::Module,
    r#type::Type,
    value::{NativeDisplay, Value},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct String(Rc<std::string::String>);

impl String {
    pub fn new() -> Self {
        Self(Rc::new(std::string::String::new()))
    }

    pub fn any_to_string(value: Value) -> Self {
        struct FormatInToString<'a>(pub &'a Value);
        impl fmt::Display for FormatInToString<'_> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                self.0.format_as_string(f)
            }
        }
        let string = format!("{}", FormatInToString(&value));
        Self(Rc::new(string))
    }

    pub fn push_str(&mut self, value: Self) {
        Rc::make_mut(&mut self.0).push_str(value.0.as_str());
    }

    pub fn concat(l: &Self, r: &Self) -> Self {
        let mut new = l.clone();
        new.push_str(r.clone());
        new
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn sub_string(&self, start: isize, end: isize) -> Self {
        let start = self.to_unsigned_index(start).min(self.len());
        let end = self.to_unsigned_index(end).min(self.len());
        if end <= start {
            Self::new()
        } else {
            let new = self.0[start..end].to_string();
            Self(Rc::new(new))
        }
    }

    fn to_unsigned_index(&self, index: isize) -> usize {
        if index < 0 {
            (self.len() as isize + index) as usize
        } else {
            index as usize
        }
    }
}

impl FromStr for String {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(Rc::new(s.to_string())))
    }
}

impl From<std::string::String> for String {
    fn from(value: std::string::String) -> Self {
        Self(Rc::new(value))
    }
}

impl From<String> for std::string::String {
    fn from(value: String) -> Self {
        value.0.deref().clone()
    }
}

impl AsRef<str> for String {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

impl Display for String {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Default for String {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeDisplay for String {
    fn fmt_as_literal(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"{}\"", self.0)
    }
    fn fmt_in_to_string(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub fn string_type() -> Type {
    cached_primitive_ty!(String)
}

pub fn add_to_module(to: &mut Module) {
    to.types.set("string", string_type());

    to.functions.insert(
        ustr("to_string"),
        UnaryNativeFnVN::description_with_default_ty(
            String::any_to_string,
            ["value"],
            None,
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("string_push_str"),
        BinaryNativeFnMNN::description_with_default_ty(
            String::push_str,
            ["target", "suffix"],
            None,
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("string_concat"),
        BinaryNativeFnNNN::description_with_default_ty(
            |a: String, b: String| String::concat(&a, &b),
            ["left", "right"],
            None,
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("string_len"),
        UnaryNativeFnNN::description_with_default_ty(
            |a: String| a.len() as isize,
            ["string"],
            None,
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("string_is_empty"),
        UnaryNativeFnNN::description_with_default_ty(
            |a: String| a.is_empty() as isize,
            ["string"],
            None,
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("string_replace"),
        TernaryNativeFnNNNN::description_with_default_ty(
            |s: String, from: String, to: String| {
                let mut new = s.clone();
                new.0 = Rc::new(new.0.replace(from.as_ref(), to.as_ref()));
                new
            },
            ["string", "from", "to"],
            None,
            no_effects(),
        ),
    );
    to.functions.insert(
        ustr("string_sub_string"),
        TernaryNativeFnNNNN::description_with_default_ty(
            |s: String, start: isize, end: isize| s.sub_string(start, end),
            ["string", "start", "end"],
            None,
            no_effects(),
        ),
    );
}
