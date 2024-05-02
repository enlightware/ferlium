use std::cmp;

/// Alias to keep code shorter
pub(crate) type B<T> = Box<T>;

/// Small vector having one element inline
pub type SVec1<T> = smallvec::SmallVec<[T; 1]>;
/// Small vector having two elements inline
pub type SVec2<T> = smallvec::SmallVec<[T; 2]>;

/// A struct that holds an optional first item of an iterator.
pub struct First<T>(pub Option<T>);

impl<T> FromIterator<T> for First<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        First(iter.into_iter().next())
    }
}

/// Compare two collections of items using a custom comparison function.
/// The comparison proceeds element by element, and if all elements are equal,
/// the shorter collection is considered less than the longer one.
pub fn compare_by<T, F>(left: &[T], right: &[T], compare: F) -> cmp::Ordering
where
    T: cmp::Ord,
    F: Fn(&T, &T) -> cmp::Ordering,
{
    let l = cmp::min(left.len(), right.len());
    let lhs = &left[..l];
    let rhs = &right[..l];

    for i in 0..l {
        match compare(&lhs[i], &rhs[i]) {
            cmp::Ordering::Equal => (),
            non_eq => return non_eq,
        }
    }

    left.len().cmp(&right.len())
}

/// Concatenate a collection of items into a string, separating them with a separator.
pub fn iterable_to_string(
    iter: impl IntoIterator<Item = impl std::fmt::Display>,
    sep: &str,
) -> String {
    iter.into_iter()
        .map(|x| x.to_string())
        .collect::<Vec<_>>()
        .join(sep)
}
