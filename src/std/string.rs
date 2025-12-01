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

use unicode_segmentation::UnicodeSegmentation;
use ustr::ustr;

use crate::{
    cached_primitive_ty,
    containers::b,
    effects::no_effects,
    function::{
        BinaryNativeFnMNN, BinaryNativeFnNNN, Function, TernaryNativeFnNNNN, UnaryNativeFnNN,
        UnaryNativeFnVN,
    },
    module::Module,
    std::contains::CONTAINS_TRAIT,
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
        Self(Rc::new(value.to_string_repr()))
    }

    pub fn push_str(&mut self, value: Self) {
        Rc::make_mut(&mut self.0).push_str(value.0.as_str());
    }

    pub fn concat(l: &Self, r: &Self) -> Self {
        let mut new = l.clone();
        new.push_str(r.clone());
        new
    }

    /// Returns the number of grapheme clusters (user-perceived characters) in the string.
    /// This is O(n) as it requires iterating through the string.
    pub fn grapheme_count(&self) -> usize {
        self.0.graphemes(true).count()
    }

    /// Returns the byte length of the string. This is O(1).
    pub fn byte_len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns a substring from grapheme index `start` to grapheme index `end`.
    /// Indices are grapheme-based (user-perceived characters), not byte-based.
    /// Negative indices count from the end of the string.
    pub fn slice(&self, start: isize, end: isize) -> Self {
        let graphemes: Vec<&str> = self.0.graphemes(true).collect();
        let len = graphemes.len() as isize;

        let start = Self::normalize_index(start, len);
        let end = Self::normalize_index(end, len);

        if end <= start {
            Self::new()
        } else {
            let result: std::string::String = graphemes[start..end].concat();
            Self(Rc::new(result))
        }
    }

    fn normalize_index(index: isize, len: isize) -> usize {
        if index < 0 {
            (len + index).max(0) as usize
        } else {
            (index as usize).min(len as usize)
        }
    }

    pub fn sub_string(&self, start: isize, end: isize) -> Self {
        let start = self.index_to_unsigned(start).min(self.byte_len());
        let end = self.index_to_unsigned(end).min(self.byte_len());

        let start = self.floor_char_boundary(start);
        let end = self.floor_char_boundary(end);

        if end <= start {
            Self::new()
        } else {
            let new = self.0[start..end].to_string();
            Self(Rc::new(new))
        }
    }

    fn floor_char_boundary(&self, index: usize) -> usize {
        let mut index = index;
        while index > 0 && !self.0.is_char_boundary(index) {
            index -= 1;
        }
        index
    }

    pub fn uppercase(&self) -> Self {
        Self(Rc::new(self.0.to_uppercase()))
    }

    pub fn lowercase(&self) -> Self {
        Self(Rc::new(self.0.to_lowercase()))
    }

    fn index_to_unsigned(&self, index: isize) -> usize {
        if index < 0 {
            (self.grapheme_count() as isize + index) as usize
        } else {
            index as usize
        }
    }

    fn contains(s: Self, substring: Self) -> bool {
        s.as_ref().contains(substring.as_ref())
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
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"{}\"", self.0)
    }
    fn fmt_in_to_string(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub fn string_type() -> Type {
    cached_primitive_ty!(String)
}

pub fn string_value(s: &str) -> Value {
    Value::native(String::from_str(s).unwrap())
}

pub fn add_to_module(to: &mut Module) {
    to.type_aliases.set("string", string_type());

    to.add_concrete_impl(
        CONTAINS_TRAIT.clone(),
        [string_type()],
        [string_type()],
        [b(BinaryNativeFnNNN::new(String::contains)) as Function],
    );

    to.add_named_function(
        ustr("to_string"),
        UnaryNativeFnVN::description_with_default_ty(
            String::any_to_string,
            ["value"],
            "Converts any value to its string representation.",
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("string_push_str"),
        BinaryNativeFnMNN::description_with_default_ty(
            String::push_str,
            ["target", "suffix"],
            "Appends `suffix` to the end of `target`.",
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("string_concat"),
        BinaryNativeFnNNN::description_with_default_ty(
            |a: String, b: String| String::concat(&a, &b),
            ["left", "right"],
            "Concatenates `left` and `right` strings.",
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("string_len"),
        UnaryNativeFnNN::description_with_default_ty(
            |a: String| a.grapheme_count() as isize,
            ["string"],
            "Returns the number of characters in the string.",
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("string_byte_len"),
        UnaryNativeFnNN::description_with_default_ty(
            |a: String| a.byte_len() as isize,
            ["string"],
            "Returns the length of the string in bytes.",
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("string_is_empty"),
        UnaryNativeFnNN::description_with_default_ty(
            |a: String| a.is_empty() as isize,
            ["string"],
            "Returns `true` if the string is empty, otherwise `false`.",
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("string_replace"),
        TernaryNativeFnNNNN::description_with_default_ty(
            |s: String, from: String, to: String| {
                let mut new = s.clone();
                new.0 = Rc::new(new.0.replace(from.as_ref(), to.as_ref()));
                new
            },
            ["string", "from", "to"],
            "Returns a new string with all occurrences of `from` replaced by `to`.",
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("string_slice"),
        TernaryNativeFnNNNN::description_with_default_ty(
            |s: String, start: isize, end: isize| s.slice(start, end),
            ["string", "start", "end"],
            "Returns the slice of `string` from character index `start` to index `end`. Negative indices count from the end.",
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("uppercase"),
        UnaryNativeFnNN::description_with_default_ty(
            |s: String| s.uppercase(),
            ["string"],
            "Returns the uppercase equivalent of this string.",
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("lowercase"),
        UnaryNativeFnNN::description_with_default_ty(
            |s: String| s.lowercase(),
            ["string"],
            "Returns the lowercase equivalent of this string.",
            no_effects(),
        ),
    );
}
