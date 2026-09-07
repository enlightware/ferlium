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
    sync::LazyLock,
};

use regex::Regex;
use unicode_normalization::UnicodeNormalization;
use unicode_segmentation::UnicodeSegmentation;
use ustr::{Ustr, ustr};

use crate::{
    cached_primitive_ty, cached_ty,
    compiler::error::SourceFailureKind,
    containers::b,
    hir::function::{Function, NativeTrivialCopy, trivial_copy_private},
    hir::native_functions::{
        NativeFallibleFnMN, NativeFallibleOutFnN, NativeFallibleOutFnR, NativeFallibleOutFnRR,
        NativeFnMR, NativeFnR, NativeFnRM, NativeFnRR, NativeOptionalFnM, NativeOptionalFnR,
        NativeOutFn0, NativeOutFnR, NativeOutFnRNN, NativeOutFnRR, NativeOutFnRRR,
    },
    hir::value::{NativeDisplay, NativeValueType, Value},
    module::{Module, ModuleFunction, Visibility},
    std::{
        core_traits_names::{
            DEFAULT_TRAIT_NAME, EMPTY_TRAIT_NAME, INSPECT_TRAIT_NAME, TRIVIAL_COPY_TRAIT_NAME,
            VALUE_TRAIT_NAME,
        },
        hash::Hasher,
        logic::bool_type,
        math::{Float, float_type, int_type},
        ordering::compare,
        value::{
            native_layout_associated_consts, native_value_clone_function,
            native_value_drop_function,
        },
    },
    types::effects::{PrimitiveEffect, effect, no_effects},
    types::r#type::{FnType, Type, bare_native_type},
    types::type_scheme::TypeScheme,
};

use super::option::option_type;

pub(crate) const STRING_FROM_STATIC_FUNCTION_NAME: &str = "string_from_static";
pub(crate) const STRING_PUSH_STR_FUNCTION_NAME: &str = "string_push_str";
pub(crate) const STRING_PUSH_STATIC_STR_FUNCTION_NAME: &str = "string_push_static_str";

static SINGLE_UNICODE_LETTER: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"\A\p{L}\z").expect("valid Unicode letter regex"));
static SINGLE_UNICODE_DECIMAL_DIGIT: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"\A\p{Nd}\z").expect("valid Unicode decimal digit regex"));

/// Immutable compiler representation of a source string literal.
///
/// The text is escape-decoded by the parser and normalized to NFC here, matching
/// the source-level [`String`] constructor. `Ustr` makes this representation
/// copyable; unlike an owned `String`, it has no semantic clone or drop behavior.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct StaticStr(Ustr);

impl StaticStr {
    pub(crate) fn new(s: &str) -> Self {
        let normalized = s.nfc().collect::<std::string::String>();
        Self::from_normalized(&normalized)
    }

    /// Interns text which is already NFC-normalized.
    pub(crate) fn from_normalized(s: &str) -> Self {
        debug_assert!(
            unicode_normalization::is_nfc(s),
            "`StaticStr::from_normalized` requires NFC-normalized text"
        );
        Self(ustr(s))
    }

    pub(crate) fn as_str(self) -> &'static str {
        self.0.as_str()
    }
}

impl NativeDisplay for StaticStr {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"{}\"", self.0)
    }
}

impl trivial_copy_private::Sealed for StaticStr {}
// SAFETY: `StaticStr` is a copyable handle to immutable, process-lifetime text.
unsafe impl NativeTrivialCopy for StaticStr {}

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

    /// Wraps text that is *already* NFC-normalized, skipping normalization.
    ///
    /// The invariant is the caller's to uphold: this type's comparisons, hashing and grapheme
    /// handling all assume NFC, so passing unnormalized text produces a `String` that misbehaves
    /// against every other one. Debug builds check it.
    fn from_normalized(s: &str) -> Self {
        debug_assert!(
            unicode_normalization::is_nfc(s),
            "`String::from_normalized` requires NFC-normalized text"
        );
        Self(Rc::new(s.to_string()))
    }

    /// Materializes a string literal.
    ///
    /// `StaticStr::new` normalizes when the literal is interned — at compile time, once — so the
    /// text is already NFC here and normalizing again would repeat that work on every execution.
    /// This is the hot path it matters on: every string literal in a program lowers to a call here,
    /// and a literal inside a loop pays per iteration.
    ///
    /// Only *this* path may skip normalization. Strings built at run time must still normalize:
    /// NFC is not closed under concatenation, so joining two normalized strings can produce text
    /// that is not.
    fn from_static(value: StaticStr) -> Self {
        Self::from_normalized(value.as_str())
    }

    /// Appends `value`, preserving the string's NFC invariant and mutable value semantics.
    ///
    /// # Optimizer contract
    ///
    /// `mir::pass::string_accumulate` relies on pushing a string onto an empty string being
    /// semantically equivalent to that string, and on later pushes preserving append order, value
    /// semantics and normalization. It also relies on `string_from_static("")` producing that empty
    /// string, on the concrete `Value<string>::to_string` registered below producing an equivalent
    /// value, and on none of those calls having source-visible effects. [`Self::push_static_str`]
    /// is a builder append of the same standing and carries the same obligations. The optimization
    /// does not rely on this `Rc` representation, but a change to any of those contracts must
    /// review that pass and `doc/mir-optimization.md`.
    pub extern "C" fn push_str(&mut self, value: &Self) {
        self.push_normalized(value.0.as_str());
    }

    fn push_unicode_scalar(&mut self, value: isize) -> Result<(), SourceFailureKind> {
        let value = unicode_scalar(value)?;
        let mut encoded = [0; 4];
        let encoded = value.encode_utf8(&mut encoded);
        if unicode_normalization::is_nfc(encoded) {
            self.push_normalized(encoded);
        } else {
            let normalized = encoded.nfc().collect::<std::string::String>();
            self.push_normalized(&normalized);
        }
        Ok(())
    }

    /// Appends a string literal without materializing it as a [`String`] first.
    ///
    /// A `StaticStr` is NFC-normalized when it is interned, so it satisfies the same precondition
    /// as the contents of a `String` and appending it must observe the same rules. The two entry
    /// points therefore share one body: `push_str(&String::from_static(literal))` and
    /// `push_static_str(literal)` are required to produce identical values, and
    /// `mir::pass::string_accumulate` relies on that equality.
    pub(crate) extern "C" fn push_static_str(&mut self, value: &StaticStr) {
        self.push_normalized(value.as_str());
    }

    /// Appends already-NFC text, restoring the invariant when the join breaks it.
    ///
    /// NFC is not closed under concatenation. Only the suffix beginning at the existing string's
    /// final starter can interact with the appended text, so normalization retains the stable
    /// prefix instead of rescanning the whole string.
    fn push_normalized(&mut self, value: &str) {
        debug_assert!(
            unicode_normalization::is_nfc(value),
            "`String::push_normalized` requires NFC-normalized text"
        );
        let Some(first) = value.chars().next() else {
            return;
        };
        let Some(last) = self.0.chars().next_back() else {
            Rc::make_mut(&mut self.0).push_str(value);
            return;
        };

        let first_class = unicode_normalization::char::canonical_combining_class(first);
        let last_class = unicode_normalization::char::canonical_combining_class(last);
        let boundary_can_change = first_class != 0
            || (last_class == 0 && unicode_normalization::char::compose(last, first).is_some());
        if !boundary_can_change {
            Rc::make_mut(&mut self.0).push_str(value);
            return;
        }

        let string = Rc::make_mut(&mut self.0);
        let suffix_start = string
            .char_indices()
            .rev()
            .find_map(|(index, ch)| {
                (unicode_normalization::char::canonical_combining_class(ch) == 0).then_some(index)
            })
            .unwrap_or(0);
        let normalized_suffix = string[suffix_start..]
            .chars()
            .chain(value.chars())
            .nfc()
            .collect::<std::string::String>();
        string.truncate(suffix_start);
        string.push_str(&normalized_suffix);
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

    pub extern "C" fn is_empty(&self) -> bool {
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

    pub fn replace(&self, from: &Self, to: &Self) -> Self {
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

    extern "C" fn starts_with(value: &Self, prefix: &Self) -> bool {
        value.as_ref().starts_with(prefix.as_ref())
    }

    extern "C" fn ends_with(value: &Self, suffix: &Self) -> bool {
        value.as_ref().ends_with(suffix.as_ref())
    }

    extern "C" fn contains_substring(haystack: &Self, needle: &Self) -> bool {
        haystack.as_ref().contains(needle.as_ref())
    }

    fn parse_int_impl(value: &Self) -> Option<isize> {
        value.as_ref().parse::<isize>().ok()
    }

    fn parse_int_descr() -> ModuleFunction {
        NativeOptionalFnR::from_rust(Self::parse_int_impl, option_type(int_type())).description(
            ["value"],
            "Parses `value` as a decimal integer, returning `Some` on success and `None` otherwise.",
            no_effects(),
        )
    }

    fn parse_float_impl(value: &Self) -> Option<Float> {
        // Float::from_str rejects NaN and infinities through Float::new.
        value.as_ref().parse::<Float>().ok()
    }

    fn parse_float_descr() -> ModuleFunction {
        NativeOptionalFnR::from_rust(Self::parse_float_impl, option_type(float_type())).description(
            ["value"],
            "Parses `value` as a finite floating-point number, returning `Some` on success and `None` otherwise.",
            no_effects(),
        )
    }

    fn parse_bool_impl(value: &Self) -> Option<bool> {
        match value.as_ref() {
            "true" => Some(true),
            "false" => Some(false),
            _ => None,
        }
    }

    fn parse_bool_descr() -> ModuleFunction {
        NativeOptionalFnR::from_rust(Self::parse_bool_impl, option_type(bool_type())).description(
            ["value"],
            "Parses `value` as a boolean, accepting only `true` and `false`.",
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

    fn unicode_scalar_iter(&self) -> StringUnicodeScalarIterator {
        StringUnicodeScalarIterator {
            string: self.0.clone(),
            byte_position: 0,
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

    fn split_iterator(&self, separator: &Self) -> Result<StringSplitIterator, SourceFailureKind> {
        if separator.is_empty() {
            return Err(SourceFailureKind::InvalidArgument(
                "separator must not be empty".into(),
            ));
        }
        let separator_grapheme_len = separator.grapheme_count();

        Ok(StringSplitIterator {
            string: self.0.clone(),
            boundaries: self.grapheme_boundaries(),
            separator: separator.0.clone(),
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
        NativeOutFnR::from_rust(String::iter).description_with_ty_scheme(
            ["string"],
            "Creates an iterator over the characters of the string.",
            ty_scheme,
        )
    }

    fn unicode_scalar_iter_descr() -> ModuleFunction {
        NativeOutFnR::from_rust(String::unicode_scalar_iter).description(
            ["string"],
            "Creates an iterator over the Unicode scalar values of `string`.",
            no_effects(),
        )
    }

    fn split_iter_descr() -> ModuleFunction {
        NativeFallibleOutFnRR::from_rust(Self::split_iterator).description(
            ["value", "separator"],
            "Creates an iterator over the parts of `value` separated by `separator`.",
            effect(PrimitiveEffect::Fallible),
        )
    }
}

fn unicode_scalar(value: isize) -> Result<char, SourceFailureKind> {
    u32::try_from(value)
        .ok()
        .and_then(char::from_u32)
        .ok_or_else(|| {
            SourceFailureKind::InvalidArgument(format!("Invalid Unicode scalar value: {value}"))
        })
}

fn unicode_scalar_is_letter(value: isize) -> Result<bool, SourceFailureKind> {
    unicode_scalar(value).map(|value| {
        let mut encoded = [0; 4];
        SINGLE_UNICODE_LETTER.is_match(value.encode_utf8(&mut encoded))
    })
}

fn unicode_scalar_is_decimal_digit(value: isize) -> Result<bool, SourceFailureKind> {
    unicode_scalar(value).map(|value| {
        let mut encoded = [0; 4];
        SINGLE_UNICODE_DECIMAL_DIGIT.is_match(value.encode_utf8(&mut encoded))
    })
}

fn unicode_scalar_is_whitespace(value: isize) -> Result<bool, SourceFailureKind> {
    unicode_scalar(value).map(|value| value.is_whitespace())
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

/// An iterator over the Unicode scalar values of a string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StringUnicodeScalarIterator {
    string: Rc<std::string::String>,
    byte_position: usize,
}

impl NativeValueType for StringUnicodeScalarIterator {}

impl StringUnicodeScalarIterator {
    fn next_value_impl(&mut self) -> Option<isize> {
        self.next()
    }

    fn next_value_descr() -> ModuleFunction {
        NativeOptionalFnM::from_rust(Self::next_value_impl, option_type(int_type())).description(
            ["iterator"],
            "Gets the next Unicode scalar value.",
            no_effects(),
        )
    }
}

impl Iterator for StringUnicodeScalarIterator {
    type Item = isize;

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.string[self.byte_position..].chars().next()?;
        self.byte_position += value.len_utf8();
        Some(value as isize)
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

impl NativeValueType for StringIterator {}

impl StringIterator {
    fn next_value_impl(&mut self) -> Option<String> {
        self.next()
    }

    fn next_value_descr() -> ModuleFunction {
        NativeOptionalFnM::from_rust(Self::next_value_impl, option_type(string_type())).description(
            ["iterator"],
            "Gets the next character of the string iterator.",
            no_effects(),
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

impl NativeValueType for StringSplitIterator {}

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

    fn next_value_impl(&mut self) -> Option<String> {
        self.next()
    }

    fn next_value_descr() -> ModuleFunction {
        NativeOptionalFnM::from_rust(Self::next_value_impl, option_type(string_type())).description(
            ["iterator"],
            "Gets the next part of the string split iterator.",
            no_effects(),
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

pub fn string_type() -> Type {
    cached_primitive_ty!(String)
}

pub(crate) fn static_str_type() -> Type {
    cached_primitive_ty!(StaticStr)
}

pub fn string_iter_type() -> Type {
    cached_ty!(|| Type::native::<StringIterator>([]))
}

fn unicode_scalar_iter_type() -> Type {
    cached_ty!(|| Type::native::<StringUnicodeScalarIterator>([]))
}

pub fn string_split_iter_type() -> Type {
    cached_ty!(|| Type::native::<StringSplitIterator>([]))
}

pub fn string_value(s: &str) -> Value {
    Value::native(String::from_str(s).unwrap())
}

extern "C" fn hash_string(value: &String, state: &mut Hasher) {
    state.write_bytes(value.as_ref().as_bytes());
}

extern "C" fn equal_string(lhs: &String, rhs: &String) -> bool {
    lhs == rhs
}

extern "C" fn equal_unicode_scalar_iterator(
    lhs: &StringUnicodeScalarIterator,
    rhs: &StringUnicodeScalarIterator,
) -> bool {
    lhs == rhs
}

fn unicode_scalar_iterator_to_string(value: &StringUnicodeScalarIterator) -> String {
    String::new(&format!(
        "StringUnicodeScalarIterator on \"{}\" @ {}",
        value.string, value.byte_position
    ))
}

extern "C" fn hash_unicode_scalar_iterator(
    value: &StringUnicodeScalarIterator,
    state: &mut Hasher,
) {
    state.write_bytes(value.string.as_bytes());
    state.write_isize(value.byte_position as isize);
}

extern "C" fn equal_string_iterator(lhs: &StringIterator, rhs: &StringIterator) -> bool {
    lhs == rhs
}

fn string_iterator_to_string(value: &StringIterator) -> String {
    String::new(&format!(
        "StringIterator on \"{}\" @ {}",
        value.string, value.position
    ))
}

extern "C" fn hash_string_iterator(value: &StringIterator, state: &mut Hasher) {
    state.write_bytes(value.string.as_bytes());
    state.write_isize(value.position as isize);
}

extern "C" fn equal_string_split_iterator(
    lhs: &StringSplitIterator,
    rhs: &StringSplitIterator,
) -> bool {
    lhs == rhs
}

fn string_split_iterator_to_string(value: &StringSplitIterator) -> String {
    String::new(&format!(
        "StringSplitIterator on \"{}\" by \"{}\" @ {}",
        value.string, value.separator, value.next_start
    ))
}

extern "C" fn hash_string_split_iterator(value: &StringSplitIterator, state: &mut Hasher) {
    state.write_bytes(value.string.as_bytes());
    state.write_bytes(value.separator.as_bytes());
    state.write_isize(value.separator_grapheme_len as isize);
    state.write_isize(value.next_start as isize);
    state.write_bool(value.finished);
}

fn compare_string(lhs: &String, rhs: &String) -> std::cmp::Ordering {
    compare(lhs, rhs)
}

fn inspect_string(value: &String) -> String {
    let mut output = std::string::String::new();
    output.push('"');
    for ch in value.as_ref().chars() {
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
    String::new(&output)
}

extern "C" fn string_len(source: &String) -> isize {
    source.grapheme_count() as isize
}

extern "C" fn string_byte_len(source: &String) -> isize {
    source.byte_len() as isize
}

pub fn add_to_module(to: &mut Module) {
    let value_trait_id = to.expect_std_trait_id_in_current_module(VALUE_TRAIT_NAME);
    let inspect_trait_id = to.expect_std_trait_id_in_current_module(INSPECT_TRAIT_NAME);
    let default_trait_id = to.expect_std_trait_id_in_current_module(DEFAULT_TRAIT_NAME);
    let empty_trait_id = to.expect_std_trait_id_in_current_module(EMPTY_TRAIT_NAME);
    let trivial_copy_trait_id = to.expect_std_trait_id_in_current_module(TRIVIAL_COPY_TRAIT_NAME);
    // Note: string alias is added in core.rs
    to.add_private_bare_native_type_alias_str("StaticStr", bare_native_type::<StaticStr>());
    to.add_private_bare_native_type_alias_str(
        "string_unicode_scalar_iterator",
        bare_native_type::<StringUnicodeScalarIterator>(),
    );
    to.add_type_alias_str_with_doc(
        "string_iterator",
        string_iter_type(),
        "An iterator over the characters of a string.",
    );
    to.add_type_alias_str_with_doc(
        "string_split_iterator",
        string_split_iter_type(),
        "An iterator over substrings produced by splitting a string.",
    );

    to.add_native_concrete_impl(trivial_copy_trait_id, [static_str_type()], [], []);
    to.add_function_with_visibility(
        ustr(STRING_FROM_STATIC_FUNCTION_NAME),
        NativeOutFnR::from_rust(|value: &StaticStr| String::from_static(*value)).description(
            ["literal"],
            "Materializes an owned string from compiler constant data.",
            no_effects(),
        ),
        Visibility::Module,
    );

    to.add_concrete_impl_no_locals(
        value_trait_id,
        [string_type()],
        [],
        native_layout_associated_consts::<String>(),
        [
            b(NativeFnRR::new(equal_string)) as Function,
            // A string's textual representation is the string itself.
            b(NativeOutFnR::from_rust(String::clone)) as Function,
            b(NativeFnRM::new(hash_string)) as Function,
            native_value_clone_function::<String>(),
            native_value_drop_function::<String>(),
        ],
    );
    to.add_concrete_impl_no_locals(
        inspect_trait_id,
        [string_type()],
        [],
        [],
        [b(NativeFallibleOutFnR::from_rust_infallible(inspect_string)) as Function],
    );
    to.add_concrete_impl_no_locals(
        value_trait_id,
        [unicode_scalar_iter_type()],
        [],
        native_layout_associated_consts::<StringUnicodeScalarIterator>(),
        [
            b(NativeFnRR::new(equal_unicode_scalar_iterator)) as Function,
            b(NativeOutFnR::from_rust(unicode_scalar_iterator_to_string)) as Function,
            b(NativeFnRM::new(hash_unicode_scalar_iterator)) as Function,
            native_value_clone_function::<StringUnicodeScalarIterator>(),
            native_value_drop_function::<StringUnicodeScalarIterator>(),
        ],
    );
    to.add_concrete_impl_no_locals(
        inspect_trait_id,
        [unicode_scalar_iter_type()],
        [],
        [],
        [b(NativeFallibleOutFnR::from_rust_infallible(
            unicode_scalar_iterator_to_string,
        )) as Function],
    );
    to.add_concrete_impl_no_locals(
        value_trait_id,
        [string_iter_type()],
        [],
        native_layout_associated_consts::<StringIterator>(),
        [
            b(NativeFnRR::new(equal_string_iterator)) as Function,
            b(NativeOutFnR::from_rust(string_iterator_to_string)) as Function,
            b(NativeFnRM::new(hash_string_iterator)) as Function,
            native_value_clone_function::<StringIterator>(),
            native_value_drop_function::<StringIterator>(),
        ],
    );
    to.add_concrete_impl_no_locals(
        inspect_trait_id,
        [string_iter_type()],
        [],
        [],
        [b(NativeFallibleOutFnR::from_rust_infallible(
            string_iterator_to_string,
        )) as Function],
    );
    to.add_concrete_impl_no_locals(
        value_trait_id,
        [string_split_iter_type()],
        [],
        native_layout_associated_consts::<StringSplitIterator>(),
        [
            b(NativeFnRR::new(equal_string_split_iterator)) as Function,
            b(NativeOutFnR::from_rust(string_split_iterator_to_string)) as Function,
            b(NativeFnRM::new(hash_string_split_iterator)) as Function,
            native_value_clone_function::<StringSplitIterator>(),
            native_value_drop_function::<StringSplitIterator>(),
        ],
    );
    to.add_concrete_impl_no_locals(
        inspect_trait_id,
        [string_split_iter_type()],
        [],
        [],
        [b(NativeFallibleOutFnR::from_rust_infallible(
            string_split_iterator_to_string,
        )) as Function],
    );
    to.add_function_with_visibility(
        ustr("compare_string_code"),
        NativeFnRR::from_rust_ordering_code(compare_string).description(
            ["left", "right"],
            "Internal comparison code.",
            no_effects(),
        ),
        crate::module::Visibility::Module,
    );
    to.add_native_concrete_impl(
        default_trait_id,
        [string_type()],
        [],
        [b(NativeOutFn0::from_rust(String::default)) as Function],
    );
    to.add_native_concrete_impl(
        empty_trait_id,
        [string_type()],
        [],
        [b(NativeOutFn0::from_rust(String::default)) as Function],
    );
    to.add_function(ustr("parse_int"), String::parse_int_descr());
    to.add_function(ustr("parse_float"), String::parse_float_descr());
    to.add_function(ustr("parse_bool"), String::parse_bool_descr());
    to.add_function(
        ustr(STRING_PUSH_STR_FUNCTION_NAME),
        NativeFnMR::new(String::push_str).description(
            ["target", "suffix"],
            "Appends `suffix` to the end of `target`.",
            no_effects(),
        ),
    );
    to.add_function_with_visibility(
        ustr("string_push_unicode_scalar"),
        NativeFallibleFnMN::from_rust(String::push_unicode_scalar).description(
            ["target", "scalar"],
            "Appends a Unicode scalar value to a string.",
            effect(PrimitiveEffect::Fallible),
        ),
        Visibility::Module,
    );
    to.add_function_with_visibility(
        ustr("unicode_scalar_is_letter"),
        NativeFallibleOutFnN::from_rust(unicode_scalar_is_letter).description(
            ["scalar"],
            "Whether a Unicode scalar belongs to the general Letter category.",
            effect(PrimitiveEffect::Fallible),
        ),
        Visibility::Module,
    );
    to.add_function_with_visibility(
        ustr("unicode_scalar_is_decimal_digit"),
        NativeFallibleOutFnN::from_rust(unicode_scalar_is_decimal_digit).description(
            ["scalar"],
            "Whether a Unicode scalar belongs to the Decimal_Number category.",
            effect(PrimitiveEffect::Fallible),
        ),
        Visibility::Module,
    );
    to.add_function_with_visibility(
        ustr("unicode_scalar_is_whitespace"),
        NativeFallibleOutFnN::from_rust(unicode_scalar_is_whitespace).description(
            ["scalar"],
            "Whether a Unicode scalar is whitespace.",
            effect(PrimitiveEffect::Fallible),
        ),
        Visibility::Module,
    );
    to.add_function_with_visibility(
        ustr("string_unicode_scalar_iter"),
        String::unicode_scalar_iter_descr(),
        Visibility::Module,
    );
    to.add_function_with_visibility(
        ustr("string_unicode_scalar_iterator_next"),
        StringUnicodeScalarIterator::next_value_descr(),
        Visibility::Module,
    );
    // The f-string desugaring emits this for every literal segment, through ordinary path
    // resolution, so it must be nameable from the module being compiled. Naming it is all a user
    // can do with it: `StaticStr` has no source spelling, and a string literal is typed `string`,
    // so no source expression can produce the second argument.
    to.add_function(
        ustr(STRING_PUSH_STATIC_STR_FUNCTION_NAME),
        NativeFnMR::new(String::push_static_str).description(
            ["target", "literal"],
            "Appends the compiler constant `literal` to the end of `target`.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_concat"),
        NativeOutFnRR::from_rust(String::concat).description(
            ["left", "right"],
            "Concatenates `left` and `right` strings.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("contains_substring"),
        NativeFnRR::new(String::contains_substring).description(
            ["haystack", "needle"],
            "Returns `true` if `haystack` contains `needle` as a substring.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_trim"),
        NativeOutFnR::from_rust(String::trim).description(
            ["string"],
            "Returns `string` with leading and trailing whitespace removed.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_starts_with"),
        NativeFnRR::new(String::starts_with).description(
            ["string", "prefix"],
            "Returns `true` if `string` starts with `prefix`.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_ends_with"),
        NativeFnRR::new(String::ends_with).description(
            ["string", "suffix"],
            "Returns `true` if `string` ends with `suffix`.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_len"),
        NativeFnR::new(string_len).description(
            ["string"],
            "Returns the number of characters in the string.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_byte_len"),
        NativeFnR::new(string_byte_len).description(
            ["string"],
            "Returns the length of the string in bytes.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_is_empty"),
        NativeFnR::new(String::is_empty).description(
            ["string"],
            "Returns `true` if the string is empty, otherwise `false`.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_replace"),
        NativeOutFnRRR::from_rust(String::replace).description(
            ["string", "from", "to"],
            "Returns a new string with all occurrences of `from` replaced by `to`.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("string_slice"),
        NativeOutFnRNN::from_rust(String::slice).description(
            ["string", "start", "end"],
            "Returns the slice of `string` from character index `start` to index `end`. Negative indices count from the end.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("uppercase"),
        NativeOutFnR::from_rust(String::uppercase).description(
            ["string"],
            "Returns the uppercase equivalent of this string.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("lowercase"),
        NativeOutFnR::from_rust(String::lowercase).description(
            ["string"],
            "Returns the lowercase equivalent of this string.",
            no_effects(),
        ),
    );

    // Iterator
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invalid_unicode_scalars_are_source_failures_and_do_not_mutate_strings() {
        let expected =
            SourceFailureKind::InvalidArgument("Invalid Unicode scalar value: 55296".to_string());
        assert_eq!(unicode_scalar(0xd800), Err(expected.clone()));
        for predicate in [
            unicode_scalar_is_letter,
            unicode_scalar_is_decimal_digit,
            unicode_scalar_is_whitespace,
        ] {
            assert_eq!(predicate(0xd800), Err(expected.clone()));
        }
        let mut value = String::new("unchanged");
        assert_eq!(
            String::push_unicode_scalar(&mut value, 0xd800),
            Err(expected)
        );
        assert_eq!(value.as_ref(), "unchanged");
    }
}
