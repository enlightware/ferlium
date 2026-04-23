// Copyright 2026 Enlightware GmbH
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

use unicode_normalization::UnicodeNormalization;
use unicode_segmentation::UnicodeSegmentation;
use ustr::ustr;

use crate::{
    cached_primitive_ty, cached_ty,
    containers::b,
    effects::{PrimitiveEffect, effect, no_effects},
    error::RuntimeErrorKind,
    function::{
        BinaryNativeFnMNN, BinaryNativeFnNMN, BinaryNativeFnNNFN, BinaryNativeFnNNN,
        BinaryNativeFnNNV, Function, NullaryNativeFnN, TernaryNativeFnNNNN, UnaryNativeFnMV,
        UnaryNativeFnNN, UnaryNativeFnNV,
    },
    module::{Module, ModuleFunction},
    std::{
        core_traits_names::ORD_TRAIT_NAME,
        default::DEFAULT_TRAIT,
        empty::EMPTY_TRAIT,
        hash::Hasher,
        logic::bool_type,
        math::{float_type, float_value, int_type, int_value},
        ordering::compare,
        value::{VALUE_TRAIT, equal},
    },
    r#type::{FnType, Type},
    type_scheme::TypeScheme,
    value::{NativeDisplay, Value},
};

use super::option::{none, option_type, some};

/// A UTF-8 encoded string type that supports Unicode grapheme clusters and normalization.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct String(
    /// Referenced-counted and normalized UTF-8 string data.
    Rc<std::string::String>,
);

impl String {
    pub fn new(s: &str) -> Self {
        Self(Rc::new(s.nfc().collect()))
    }

    pub fn push_str(&mut self, value: Self) {
        let needs_normalization = value
            .0
            .chars()
            .next()
            .map(unicode_normalization::char::is_combining_mark)
            .unwrap_or(false);

        if needs_normalization {
            self.0 = Rc::new(self.0.chars().chain(value.0.chars()).nfc().collect());
        } else {
            Rc::make_mut(&mut self.0).push_str(value.0.as_str());
        }
    }

    pub fn concat(l: &Self, r: &Self) -> Self {
        Self(Rc::new(l.0.chars().chain(r.0.chars()).nfc().collect()))
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
            Self::default()
        } else {
            // Our initial string is already normalized to NFC,
            // and slicing by grapheme clusters won't break that normalization,
            // so we can safely return the slice as-is without re-normalizing.
            let result = graphemes[start..end].concat();
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

    pub fn replace(&self, from: Self, to: Self) -> Self {
        Self(Rc::new(
            self.0.replace(from.as_ref(), to.as_ref()).nfc().collect(),
        ))
    }

    pub fn uppercase(&self) -> Self {
        Self::new(&self.0.to_uppercase())
    }

    pub fn lowercase(&self) -> Self {
        Self::new(&self.0.to_lowercase())
    }

    pub fn trim(&self) -> Self {
        Self(Rc::new(self.0.trim().to_owned()))
    }

    fn starts_with(value: Self, prefix: Self) -> bool {
        value.as_ref().starts_with(prefix.as_ref())
    }

    fn ends_with(value: Self, suffix: Self) -> bool {
        value.as_ref().ends_with(suffix.as_ref())
    }

    fn contains_substring(haystack: Self, needle: Self) -> bool {
        haystack.as_ref().contains(needle.as_ref())
    }

    fn parse_int(value: Self) -> Value {
        value
            .as_ref()
            .parse::<isize>()
            .ok()
            .map(int_value)
            .map(some)
            .unwrap_or_else(none)
    }

    fn parse_int_descr() -> ModuleFunction {
        UnaryNativeFnNV::description_with_ty(
            Self::parse_int,
            ["value"],
            "Parses `value` as a decimal integer, returning `Some` on success and `None` otherwise.",
            string_type(),
            option_type(int_type()),
            no_effects(),
        )
    }

    fn parse_float(value: Self) -> Value {
        value
            .as_ref()
            .parse::<f64>()
            .ok()
            .filter(|value| value.is_finite())
            .map(float_value)
            .map(some)
            .unwrap_or_else(none)
    }

    fn parse_float_descr() -> ModuleFunction {
        UnaryNativeFnNV::description_with_ty(
            Self::parse_float,
            ["value"],
            "Parses `value` as a finite floating-point number, returning `Some` on success and `None` otherwise.",
            string_type(),
            option_type(float_type()),
            no_effects(),
        )
    }

    fn parse_bool(value: Self) -> Value {
        match value.as_ref() {
            "true" => some(Value::native(true)),
            "false" => some(Value::native(false)),
            _ => none(),
        }
    }

    fn parse_bool_descr() -> ModuleFunction {
        UnaryNativeFnNV::description_with_ty(
            Self::parse_bool,
            ["value"],
            "Parses `value` as a boolean, accepting only `true` and `false`.",
            string_type(),
            option_type(bool_type()),
            no_effects(),
        )
    }

    /// Creates an iterator over the grapheme clusters of the string.
    pub fn iter(&self) -> StringIterator {
        StringIterator {
            string: self.0.clone(),
            indices: self.grapheme_indices(),
            position: 0,
        }
    }

    /// Collect byte offsets of each grapheme cluster
    fn grapheme_indices(&self) -> Vec<usize> {
        self.0.grapheme_indices(true).map(|(idx, _)| idx).collect()
    }

    fn grapheme_boundaries(&self) -> Vec<usize> {
        let mut indices = self.grapheme_indices();
        indices.push(self.0.len());
        indices
    }

    fn split_iterator(&self, separator: Self) -> Result<StringSplitIterator, RuntimeErrorKind> {
        if separator.is_empty() {
            return Err(RuntimeErrorKind::InvalidArgument(ustr(
                "separator must not be empty",
            )));
        }
        let separator_grapheme_len = separator.grapheme_count();

        Ok(StringSplitIterator {
            string: self.0.clone(),
            boundaries: self.grapheme_boundaries(),
            separator: separator.0,
            separator_grapheme_len,
            next_start: 0,
            finished: false,
        })
    }

    fn iter_descr() -> ModuleFunction {
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_by_val(
            [string_type()],
            string_iter_type(),
            no_effects(),
        ));
        UnaryNativeFnNN::description_with_ty_scheme(
            |s: Self| s.iter(),
            ["string"],
            "Creates an iterator over the characters of the string.",
            ty_scheme,
        )
    }

    fn split_iter_descr() -> ModuleFunction {
        BinaryNativeFnNNFN::description_with_ty_scheme(
            |value: Self, separator: Self| value.split_iterator(separator),
            ["value", "separator"],
            "Creates an iterator over the parts of `value` separated by `separator`.",
            TypeScheme::new_just_type(FnType::new_by_val(
                [string_type(), string_type()],
                string_split_iter_type(),
                effect(PrimitiveEffect::Fallible),
            )),
        )
    }
}

impl FromStr for String {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::new(s))
    }
}

impl From<std::string::String> for String {
    fn from(s: std::string::String) -> Self {
        Self::new(&s)
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
        Self(Rc::new(std::string::String::new()))
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

/// An iterator over the grapheme clusters of a string.
/// Stores the original string and byte indices of each grapheme cluster.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringIterator {
    string: Rc<std::string::String>,
    indices: Vec<usize>,
    position: usize,
}

impl StringIterator {
    pub fn next_value(&mut self) -> Value {
        match self.next() {
            Some(value) => some(Value::native(value)),
            None => none(),
        }
    }

    fn next_value_descr() -> ModuleFunction {
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_mut_resolved(
            [(string_iter_type(), true)],
            option_type(string_type()),
            no_effects(),
        ));
        UnaryNativeFnMV::description_with_ty_scheme(
            Self::next_value,
            ["iterator"],
            "Gets the next character of the string iterator.",
            ty_scheme,
        )
    }
}

impl Iterator for StringIterator {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.indices.len() {
            let start = self.indices[self.position];
            let end = if self.position + 1 < self.indices.len() {
                self.indices[self.position + 1]
            } else {
                self.string.len()
            };
            self.position += 1;
            Some(String::from(self.string[start..end].to_string()))
        } else {
            None
        }
    }
}

impl NativeDisplay for StringIterator {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "StringIterator on \"{}\" @ {}",
            self.string, self.position
        )
    }
}

/// An iterator over the grapheme-aligned parts of a string separated by a substring.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringSplitIterator {
    string: Rc<std::string::String>,
    boundaries: Vec<usize>,
    separator: Rc<std::string::String>,
    separator_grapheme_len: usize,
    next_start: usize,
    finished: bool,
}

impl StringSplitIterator {
    fn slice_grapheme_range(&self, start: usize, end: usize) -> String {
        if end <= start {
            String::default()
        } else {
            String(Rc::new(
                self.string[self.boundaries[start]..self.boundaries[end]].to_string(),
            ))
        }
    }

    fn next_separator_start(&self) -> Option<usize> {
        let grapheme_count = self.boundaries.len().saturating_sub(1);
        if self.separator_grapheme_len > grapheme_count.saturating_sub(self.next_start) {
            return None;
        }

        let last_candidate = grapheme_count - self.separator_grapheme_len;
        for candidate_start in self.next_start..=last_candidate {
            let start = self.boundaries[candidate_start];
            let end = self.boundaries[candidate_start + self.separator_grapheme_len];
            if &self.string[start..end] == self.separator.as_ref() {
                return Some(candidate_start);
            }
        }
        None
    }

    pub fn next_value(&mut self) -> Value {
        match self.next() {
            Some(value) => some(Value::native(value)),
            None => none(),
        }
    }

    fn next_value_descr() -> ModuleFunction {
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_mut_resolved(
            [(string_split_iter_type(), true)],
            option_type(string_type()),
            no_effects(),
        ));
        UnaryNativeFnMV::description_with_ty_scheme(
            Self::next_value,
            ["iterator"],
            "Gets the next part of the string split iterator.",
            ty_scheme,
        )
    }
}

impl Iterator for StringSplitIterator {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        match self.next_separator_start() {
            Some(separator_start) => {
                let part = self.slice_grapheme_range(self.next_start, separator_start);
                self.next_start = separator_start + self.separator_grapheme_len;
                Some(part)
            }
            None => {
                let part = self.slice_grapheme_range(self.next_start, self.boundaries.len() - 1);
                self.finished = true;
                Some(part)
            }
        }
    }
}

impl NativeDisplay for StringSplitIterator {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "StringSplitIterator on \"{}\" by \"{}\" @ {}",
            self.string, self.separator, self.next_start
        )
    }
}

pub fn string_type() -> Type {
    cached_primitive_ty!(String)
}

pub fn string_iter_type() -> Type {
    cached_ty!(|| Type::native::<StringIterator>([]))
}

pub fn string_split_iter_type() -> Type {
    cached_ty!(|| Type::native::<StringSplitIterator>([]))
}

pub fn string_value(s: &str) -> Value {
    Value::native(String::from_str(s).unwrap())
}

fn hash_string(value: String, state: &mut Hasher) {
    state.write_bytes(value.as_ref().as_bytes());
}

pub fn add_to_module(to: &mut Module) {
    // Note: string alias is added in core.rs

    to.add_concrete_impl_no_locals(
        VALUE_TRAIT.clone(),
        [string_type()],
        [],
        [
            b(BinaryNativeFnNNN::new(equal::<String>)) as Function,
            b(UnaryNativeFnNN::new(|value: String| value)) as Function,
            b(BinaryNativeFnNMN::new(hash_string)) as Function,
        ],
    );
    let ord_trait = to.get_trait_str(ORD_TRAIT_NAME).unwrap().clone();
    to.add_concrete_impl_no_locals(
        ord_trait,
        [string_type()],
        [],
        [b(BinaryNativeFnNNV::new(compare::<String>)) as Function],
    );
    to.add_concrete_impl_no_locals(
        DEFAULT_TRAIT.clone(),
        [string_type()],
        [],
        [b(NullaryNativeFnN::new(String::default)) as Function],
    );
    to.add_concrete_impl_no_locals(
        EMPTY_TRAIT.clone(),
        [string_type()],
        [],
        [b(NullaryNativeFnN::new(String::default)) as Function],
    );
    to.add_function(ustr("parse_int"), String::parse_int_descr());
    to.add_function(ustr("parse_float"), String::parse_float_descr());
    to.add_function(ustr("parse_bool"), String::parse_bool_descr());
    to.add_function(
        ustr("string_push_str"),
        BinaryNativeFnMNN::description_with_default_ty(
            String::push_str,
            ["target", "suffix"],
            "Appends `suffix` to the end of `target`.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_concat"),
        BinaryNativeFnNNN::description_with_default_ty(
            |a: String, b: String| String::concat(&a, &b),
            ["left", "right"],
            "Concatenates `left` and `right` strings.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("contains_substring"),
        BinaryNativeFnNNN::description_with_default_ty(
            String::contains_substring,
            ["haystack", "needle"],
            "Returns `true` if `haystack` contains `needle` as a substring.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_trim"),
        UnaryNativeFnNN::description_with_default_ty(
            |s: String| s.trim(),
            ["string"],
            "Returns `string` with leading and trailing whitespace removed.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_starts_with"),
        BinaryNativeFnNNN::description_with_default_ty(
            String::starts_with,
            ["string", "prefix"],
            "Returns `true` if `string` starts with `prefix`.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_ends_with"),
        BinaryNativeFnNNN::description_with_default_ty(
            String::ends_with,
            ["string", "suffix"],
            "Returns `true` if `string` ends with `suffix`.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_len"),
        UnaryNativeFnNN::description_with_default_ty(
            |a: String| a.grapheme_count() as isize,
            ["string"],
            "Returns the number of characters in the string.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_byte_len"),
        UnaryNativeFnNN::description_with_default_ty(
            |a: String| a.byte_len() as isize,
            ["string"],
            "Returns the length of the string in bytes.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_is_empty"),
        UnaryNativeFnNN::description_with_default_ty(
            |a: String| a.is_empty(),
            ["string"],
            "Returns `true` if the string is empty, otherwise `false`.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_replace"),
        TernaryNativeFnNNNN::description_with_default_ty(
            |s: String, from: String, to: String| s.replace(from, to),
            ["string", "from", "to"],
            "Returns a new string with all occurrences of `from` replaced by `to`.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_slice"),
        TernaryNativeFnNNNN::description_with_default_ty(
            |s: String, start: isize, end: isize| s.slice(start, end),
            ["string", "start", "end"],
            "Returns the slice of `string` from character index `start` to index `end`. Negative indices count from the end.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("uppercase"),
        UnaryNativeFnNN::description_with_default_ty(
            |s: String| s.uppercase(),
            ["string"],
            "Returns the uppercase equivalent of this string.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("lowercase"),
        UnaryNativeFnNN::description_with_default_ty(
            |s: String| s.lowercase(),
            ["string"],
            "Returns the lowercase equivalent of this string.",
            no_effects(),
        ),
    );

    // Iterator
    to.add_type_alias_str("string_iterator", string_iter_type());
    to.add_type_alias_str("string_split_iterator", string_split_iter_type());
    to.add_function(ustr("string_iter"), String::iter_descr());
    to.add_function(ustr("string_split_iterator"), String::split_iter_descr());
    to.add_function(
        ustr("string_iterator_next"),
        StringIterator::next_value_descr(),
    );
    to.add_function(
        ustr("string_split_iterator_next"),
        StringSplitIterator::next_value_descr(),
    );
}
