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

pub(crate) fn write_with_separator(
    iter: impl IntoIterator<Item = impl std::fmt::Display>,
    separator: &str,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    let mut iter = iter.into_iter();
    if let Some(e) = iter.next() {
        write!(f, "{}", e)?;
    }
    for e in iter {
        write!(f, "{separator}{e}")?;
    }
    Ok(())
}

pub(crate) fn newline_indices_of_non_empty_lines(text: &str) -> Vec<usize> {
    let mut last_char = '\n';
    text.char_indices()
        .filter_map(|(i, c)| {
            let prev_last_char = last_char;
            last_char = c;
            if c == '\n' && prev_last_char != '\n' {
                Some(i)
            } else {
                None
            }
        })
        .collect()
}
