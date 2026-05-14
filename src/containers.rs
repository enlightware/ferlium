// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::cmp;
use std::hash::{Hash, Hasher};
use std::iter::FusedIterator;

use crate::FxHashMap;

/// Box alias to keep code shorter
pub(crate) type B<T> = Box<T>;

/// Box a value, keeping code shorter
pub(crate) fn b<T>(t: T) -> B<T> {
    Box::new(t)
}

/// Small vector having two elements inline
pub type SVec2<T> = smallvec::SmallVec<[T; 2]>;

/// Small vector having four elements inline
pub type SVec4<T> = smallvec::SmallVec<[T; 4]>;

/// Dense set of non-negative integer indices.
#[derive(Debug, Clone, Default)]
pub(crate) enum DenseBitSet {
    #[default]
    Empty,
    Inline(u64),
    Heap(Box<[u64]>),
}

impl DenseBitSet {
    pub const fn empty() -> Self {
        Self::Empty
    }

    pub fn with_capacity(bits: usize) -> Self {
        if bits <= u64::BITS as usize {
            Self::Inline(0)
        } else {
            Self::Heap(zeroed_words(bits.div_ceil(u64::BITS as usize)))
        }
    }

    pub fn insert(&mut self, index: usize) {
        let word = index / u64::BITS as usize;
        let bit = 1u64 << (index % u64::BITS as usize);
        match self {
            Self::Empty if word == 0 => *self = Self::Inline(bit),
            Self::Empty => {
                let mut words = zeroed_words(word + 1);
                words[word] = bit;
                *self = Self::Heap(words);
            }
            Self::Inline(bits) if word == 0 => *bits |= bit,
            Self::Inline(bits) => {
                let low = *bits;
                let mut words = zeroed_words(word + 1);
                words[0] = low;
                words[word] |= bit;
                *self = Self::Heap(words);
            }
            Self::Heap(words) if word < words.len() => words[word] |= bit,
            Self::Heap(words) => {
                let old = std::mem::take(words);
                let mut new_words = zeroed_words(word + 1);
                new_words[..old.len()].copy_from_slice(&old);
                new_words[word] |= bit;
                *words = new_words;
            }
        }
    }

    pub fn remove(&mut self, index: usize) {
        let word = index / u64::BITS as usize;
        let bit = 1u64 << (index % u64::BITS as usize);
        match self {
            Self::Empty => {}
            Self::Inline(bits) if word == 0 => *bits &= !bit,
            Self::Inline(_) => {}
            Self::Heap(words) => {
                if let Some(word) = words.get_mut(word) {
                    *word &= !bit;
                }
            }
        }
    }

    pub fn contains(&self, index: usize) -> bool {
        let word = index / u64::BITS as usize;
        let bit = 1u64 << (index % u64::BITS as usize);
        match self {
            Self::Empty => false,
            Self::Inline(bits) => word == 0 && (*bits & bit) != 0,
            Self::Heap(words) => words.get(word).is_some_and(|word| (*word & bit) != 0),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.nonzero_word_len() == 0
    }

    pub fn len(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Inline(bits) => bits.count_ones() as usize,
            Self::Heap(words) => words.iter().map(|word| word.count_ones() as usize).sum(),
        }
    }

    pub fn union_with(&mut self, other: &Self) {
        match (&mut *self, other) {
            (_, Self::Empty) => {}
            (Self::Empty, _) => *self = other.clone(),
            (Self::Inline(a), Self::Inline(b)) => *a |= *b,
            (Self::Heap(a), Self::Inline(b)) => a[0] |= *b,
            (Self::Inline(a), Self::Heap(b)) => {
                let low = *a;
                let mut words = zeroed_words(b.len());
                words.copy_from_slice(b);
                words[0] |= low;
                *self = Self::Heap(words);
            }
            (Self::Heap(a), Self::Heap(b)) => {
                if a.len() < b.len() {
                    let old = std::mem::take(a);
                    let mut words = zeroed_words(b.len());
                    words[..old.len()].copy_from_slice(&old);
                    *a = words;
                }
                for (left, right) in a.iter_mut().zip(b.iter()) {
                    *left |= *right;
                }
            }
        }
    }

    pub fn intersects(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Empty, _) | (_, Self::Empty) => false,
            (Self::Inline(a), Self::Inline(b)) => (*a & *b) != 0,
            (Self::Inline(a), Self::Heap(b)) | (Self::Heap(b), Self::Inline(a)) => (*a & b[0]) != 0,
            (Self::Heap(a), Self::Heap(b)) => a
                .iter()
                .zip(b.iter())
                .any(|(left, right)| (left & right) != 0),
        }
    }

    pub fn iter_ones(&self) -> DenseBitSetOnes<'_> {
        match self {
            Self::Empty => DenseBitSetOnes::Inline { current: 0 },
            Self::Inline(bits) => DenseBitSetOnes::Inline { current: *bits },
            Self::Heap(words) => DenseBitSetOnes::Heap {
                words,
                word_idx: 0,
                current: words.first().copied().unwrap_or(0),
            },
        }
    }

    fn nonzero_word_len(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Inline(bits) => usize::from(*bits != 0),
            Self::Heap(words) => words
                .iter()
                .rposition(|word| *word != 0)
                .map_or(0, |index| index + 1),
        }
    }

    fn word_at(&self, index: usize) -> u64 {
        match self {
            Self::Empty => 0,
            Self::Inline(bits) => {
                if index == 0 {
                    *bits
                } else {
                    0
                }
            }
            Self::Heap(words) => words.get(index).copied().unwrap_or(0),
        }
    }
}

impl PartialEq for DenseBitSet {
    fn eq(&self, other: &Self) -> bool {
        let len = self.nonzero_word_len();
        if len != other.nonzero_word_len() {
            return false;
        }
        (0..len).all(|index| self.word_at(index) == other.word_at(index))
    }
}

impl Eq for DenseBitSet {}

impl Hash for DenseBitSet {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let len = self.nonzero_word_len();
        len.hash(state);
        for index in 0..len {
            self.word_at(index).hash(state);
        }
    }
}

pub(crate) enum DenseBitSetOnes<'a> {
    Inline {
        current: u64,
    },
    Heap {
        words: &'a [u64],
        word_idx: usize,
        current: u64,
    },
}

impl Iterator for DenseBitSetOnes<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            DenseBitSetOnes::Inline { current } => {
                if *current == 0 {
                    None
                } else {
                    let bit = current.trailing_zeros() as usize;
                    *current &= *current - 1;
                    Some(bit)
                }
            }
            DenseBitSetOnes::Heap {
                words,
                word_idx,
                current,
            } => loop {
                if *current != 0 {
                    let bit = current.trailing_zeros() as usize;
                    *current &= *current - 1;
                    return Some(*word_idx * u64::BITS as usize + bit);
                }
                *word_idx += 1;
                if *word_idx >= words.len() {
                    return None;
                }
                *current = words[*word_idx];
            },
        }
    }
}

impl FusedIterator for DenseBitSetOnes<'_> {}

fn zeroed_words(len: usize) -> Box<[u64]> {
    let words = Box::<[u64]>::new_zeroed_slice(len);
    // SAFETY: all-zero bytes are a valid initialized `u64`.
    unsafe { words.assume_init() }
}

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
    map: &'a FxHashMap<K, V>,
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
    mut map: FxHashMap<K, T>,
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

#[cfg(test)]
mod tests {
    use std::collections::hash_map::DefaultHasher;

    use super::*;

    fn hash(value: &DenseBitSet) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn dense_bit_set_empty_capacity_is_logically_empty() {
        let empty = DenseBitSet::empty();
        let inline = DenseBitSet::with_capacity(64);
        let heap = DenseBitSet::with_capacity(65);
        assert_eq!(empty, inline);
        assert_eq!(empty, heap);
        assert_eq!(hash(&empty), hash(&inline));
        assert_eq!(hash(&empty), hash(&heap));
        assert!(heap.is_empty());
    }

    #[test]
    fn dense_bit_set_insert_contains_and_remove() {
        let mut set = DenseBitSet::empty();
        set.insert(3);
        set.insert(64);
        set.insert(130);
        assert!(set.contains(3));
        assert!(set.contains(64));
        assert!(set.contains(130));
        assert_eq!(set.len(), 3);

        set.remove(64);
        assert!(set.contains(3));
        assert!(!set.contains(64));
        assert!(set.contains(130));
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn dense_bit_set_union_intersection_and_iteration() {
        let mut left = DenseBitSet::empty();
        left.insert(1);
        left.insert(70);

        let mut right = DenseBitSet::empty();
        right.insert(70);
        right.insert(130);

        assert!(left.intersects(&right));
        left.union_with(&right);
        assert_eq!(left.iter_ones().collect::<Vec<_>>(), vec![1, 70, 130]);
    }

    #[test]
    fn dense_bit_set_heap_zero_after_remove_equals_empty() {
        let mut set = DenseBitSet::with_capacity(130);
        set.insert(129);
        set.remove(129);
        assert_eq!(set, DenseBitSet::empty());
        assert_eq!(hash(&set), hash(&DenseBitSet::empty()));
    }
}
