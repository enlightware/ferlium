// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::hash::Hash;
use std::{cmp, collections::HashMap};

/// Box alias to keep code shorter
pub(crate) type B<T> = Box<T>;

/// Box a value, keeping code shorter
pub(crate) fn b<T>(t: T) -> B<T> {
    Box::new(t)
}

/// Small vector having two elements inline
pub type SVec2<T> = smallvec::SmallVec<[T; 2]>;

// A trait that knows how to turn either an owned T or a &T into a T
pub trait IntoOwned<T> {
    fn into_owned(self) -> T;
}

// Moving an owned T is just identity
impl<T> IntoOwned<T> for T {
    fn into_owned(self) -> T {
        self
    }
}

// Cloning a &T if we only have a reference
impl<T: Clone> IntoOwned<T> for &T {
    fn into_owned(self) -> T {
        self.clone()
    }
}

/// Anything that can turn itself into a `SVec<T>`,
/// moving owned Ts and cloning borrowed ones.
pub trait IntoSVec2<T> {
    fn into_svec2(self) -> SVec2<T>;
}

impl<T, I> IntoSVec2<T> for I
where
    I: IntoIterator,
    I::Item: IntoOwned<T>,
{
    fn into_svec2(self) -> SVec2<T> {
        self.into_iter().map(IntoOwned::into_owned).collect()
    }
}

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

/// Sort v and return it.
pub fn sorted<T: Ord>(mut v: Vec<T>) -> Vec<T> {
    v.sort();
    v
}

/// A helper trait to convert an index to a value for use in `continuous_hashmap_to_vec`.
pub trait FromIndex: std::cmp::Eq + std::hash::Hash {
    fn from_index(index: usize) -> Self;
}

/// Consumes a HashMap with continuous indices starting at 0 and returns a Vec with the values in order.
/// If the indices are not continuous, an error is returned.
pub fn continuous_hashmap_to_vec<K: FromIndex, T>(
    mut map: HashMap<K, T>,
) -> Result<Vec<T>, &'static str> {
    let len = map.len();

    // Check if all keys from 0 to len-1 are present
    for i in 0..len {
        if !map.contains_key(&K::from_index(i)) {
            return Err("HashMap does not contain continuous indices starting at 0");
        }
    }

    // Collect values in order
    let mut vec: Vec<T> = Vec::with_capacity(map.len());
    for i in 0..len {
        vec.push(map.remove(&K::from_index(i)).unwrap());
    }

    Ok(vec)
}
