use std::hash::Hash;
use std::{cmp, collections::HashMap};

/// Alias to keep code shorter
pub(crate) type B<T> = Box<T>;

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
    separator: &str,
) -> String {
    iter.into_iter()
        .map(|x| x.to_string())
        .collect::<Vec<_>>()
        .join(separator)
}

/// In a Hashmap, find a key that has a value equal to the given value.
pub fn find_key_for_value_property<'a, K, V, P, F>(
    map: &'a HashMap<K, V>,
    value: &P,
    compare: F,
) -> Option<&'a K>
where
    K: Eq + Hash,
    F: Fn(&V, &P) -> bool,
{
    for (key, val) in map {
        if compare(val, value) {
            return Some(key);
        }
    }
    None
}

/// Returns a vector containing the elements of this that are not in that
/// O(this.len() * that.len())
#[allow(dead_code)]
pub fn vec_difference<T: Clone + PartialEq>(this: &[T], that: &[T]) -> Vec<T> {
    this.iter()
        .filter(|&x| !that.contains(x))
        .cloned()
        .collect()
}
