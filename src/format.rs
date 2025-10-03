// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::fmt::{self, Display};

use derive_new::new;

use crate::never::Never;

/// A wrapper to fmt::Display types that depend on third-party data
#[derive(new)]
pub struct FormatWithData<'a, T: ?Sized + 'a, D: ?Sized + 'a> {
    pub value: &'a T,
    pub data: &'a D,
}

pub trait FormatWith<X> {
    fn format_with<'a>(&'a self, data: &'a X) -> FormatWithData<'a, Self, X> {
        FormatWithData { value: self, data }
    }

    fn fmt_with(&self, f: &mut std::fmt::Formatter<'_>, data: &X) -> std::fmt::Result;
}

impl<X, T: FormatWith<X>> Display for FormatWithData<'_, T, X> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt_with(f, self.data)
    }
}

impl<X, U: ?Sized + FormatWith<X>> FormatWith<X> for &U {
    fn fmt_with(&self, f: &mut std::fmt::Formatter<'_>, data: &X) -> std::fmt::Result {
        (**self).fmt_with(f, data)
    }
}

impl<A, B, X> FormatWith<X> for (A, B)
where
    A: FormatWith<X>,
    B: FormatWith<X>,
{
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, data: &X) -> fmt::Result {
        f.write_str("(")?;
        self.0.fmt_with(f, data)?;
        f.write_str(", ")?;
        self.1.fmt_with(f, data)?;
        f.write_str(")")?;
        Ok(())
    }
}

impl<T, X> FormatWith<X> for [T]
where
    T: FormatWith<X>,
{
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, data: &X) -> fmt::Result {
        for (i, item) in self.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            item.fmt_with(f, data)?;
        }
        Ok(())
    }
}

impl<T, X> FormatWith<X> for Vec<T>
where
    T: FormatWith<X>,
{
    fn fmt_with(&self, f: &mut std::fmt::Formatter<'_>, data: &X) -> std::fmt::Result {
        self.as_slice().fmt_with(f, data)
    }
}

impl<K, V, X> FormatWith<X> for std::collections::HashMap<K, V>
where
    K: Display,
    V: FormatWith<X>,
{
    fn fmt_with(&self, f: &mut std::fmt::Formatter<'_>, data: &X) -> std::fmt::Result {
        for (k, v) in self {
            write!(f, "{k}: ")?;
            v.fmt_with(f, data)?;
            f.write_str(", ")?;
        }
        Ok(())
    }
}

impl<X> FormatWith<X> for Never {
    fn fmt_with(&self, f: &mut std::fmt::Formatter<'_>, _data: &X) -> std::fmt::Result {
        write!(f, "Never")
    }
}

pub(crate) fn type_variable_index_to_string(
    index: u32,
    first: u32,
    last: u32,
    fallback: &str,
) -> String {
    let unicode_char = first + index;
    if unicode_char <= last {
        char::from_u32(unicode_char).unwrap_or('_').to_string()
    } else {
        format!("{fallback}{}", unicode_char - last)
    }
}

pub(crate) fn type_variable_index_to_string_greek(index: u32) -> String {
    type_variable_index_to_string(index, 0x3B1, 0x3C9, "T")
}

pub(crate) fn type_variable_index_to_string_latin(index: u32) -> String {
    type_variable_index_to_string(index, 'A' as u32, 'Y' as u32, "Z")
}

pub(crate) fn type_variable_subscript(index: u32) -> String {
    let mut result = String::new();
    if index == 0 {
        return "₀".to_string();
    } else {
        let mut index = index;
        while index > 0 {
            let digit = index % 10;
            result.insert(0, char::from_u32(0x2080 + digit).unwrap());
            index /= 10;
        }
    }
    result
}

pub(crate) fn write_with_separator(
    iter: impl IntoIterator<Item = impl std::fmt::Display>,
    separator: &str,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    let mut iter = iter.into_iter();
    if let Some(element) = iter.next() {
        write!(f, "{element}")?;
    }
    for element in iter {
        write!(f, "{separator}{element}")?;
    }
    Ok(())
}

pub(crate) fn write_with_separator_and_format_fn<T>(
    iter: impl IntoIterator<Item = T>,
    separator: &str,
    format_fn: impl Fn(T, &mut fmt::Formatter) -> fmt::Result,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    let mut iter = iter.into_iter();
    if let Some(element) = iter.next() {
        format_fn(element, f)?;
    }
    for element in iter {
        write!(f, "{separator}")?;
        format_fn(element, f)?;
    }
    Ok(())
}
