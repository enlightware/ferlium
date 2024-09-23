use std::fmt;

/// A wrapper to fmt::Display types that depend on third-party data
pub struct FormatWith<'a, T: ?Sized + 'a, D: ?Sized + 'a> {
    pub value: &'a T,
    pub data: &'a D,
}

impl<'a, T, D> FormatWith<'a, T, D> {
    pub fn new(value: &'a T, data: &'a D) -> Self {
        Self { value, data }
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
        write!(f, "{}", element)?;
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
