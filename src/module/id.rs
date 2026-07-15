// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::FxHashMap;
use std::hash::Hash;
use std::mem::swap;

#[doc(hidden)]
pub use nonmax::NonMaxU32 as IdRepr;

/// An ID that can be used as an index into a collection
pub trait Id: Copy {
    fn from_index(index: usize) -> Self;
    fn as_index(self) -> usize;
}

// Small helper macro to declare compact newtype ID wrappers with common derives and helpers.
#[macro_export]
macro_rules! define_id_type {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        #[repr(transparent)]
        pub struct $name($crate::module::id::IdRepr);

        impl $name {
            /// Creates an ID from its compact integer representation.
            ///
            /// Panics if `index` is `u32::MAX`, which is reserved as the niche for `Option<Self>`.
            #[inline]
            pub const fn new(index: u32) -> Self {
                match $crate::module::id::IdRepr::new(index) {
                    Some(index) => Self(index),
                    None => panic!(concat!(
                        stringify!($name),
                        " cannot represent u32::MAX"
                    )),
                }
            }

            /// Returns the compact integer representation of this ID.
            #[inline]
            pub const fn as_u32(self) -> u32 {
                self.0.get()
            }
        }

        impl $crate::module::id::Id for $name {
            #[inline]
            fn from_index(index: usize) -> Self {
                let index = match <u32 as std::convert::TryFrom<usize>>::try_from(index) {
                    Ok(index) => index,
                    Err(_) => panic!(concat!(
                        stringify!($name),
                        " index does not fit in u32"
                    )),
                };
                Self::new(index)
            }

            #[inline]
            fn as_index(self) -> usize {
                self.as_u32() as usize
            }
        }

        impl Default for $name {
            #[inline]
            fn default() -> Self {
                Self::new(0)
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(&self.as_u32(), f)
            }
        }

        impl std::hash::Hash for $name {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                std::hash::Hash::hash(&self.as_u32(), state);
            }
        }

        impl From<$name> for usize {
            fn from(id: $name) -> Self {
                id.as_u32() as usize
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::{DefaultHasher, Hash, Hasher};
    use std::mem::size_of;

    define_id_type!(TestId);

    #[cfg(feature = "serde")]
    fn assert_serde<T: serde::Serialize + for<'de> serde::Deserialize<'de>>() {}

    #[test]
    #[cfg(feature = "serde")]
    fn defined_id_types_derive_serde_when_feature_is_enabled() {
        assert_serde::<TestId>();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn defined_id_types_preserve_the_u32_wire_representation() {
        use serde_test::{Token, assert_de_tokens_error, assert_tokens};

        let id = TestId::new(42);
        assert_tokens(
            &id,
            &[Token::NewtypeStruct { name: "TestId" }, Token::U32(42)],
        );
        assert_de_tokens_error::<TestId>(
            &[
                Token::NewtypeStruct { name: "TestId" },
                Token::U32(u32::MAX),
            ],
            "out of range integral type conversion attempted",
        );
    }

    #[test]
    fn defined_id_types_round_trip_indices() {
        let id = TestId::from_index((u32::MAX - 1) as usize);
        assert_eq!(id.as_u32(), u32::MAX - 1);
        assert_eq!(id.as_index(), (u32::MAX - 1) as usize);
        assert_eq!(TestId::default(), TestId::new(0));
    }

    #[test]
    fn defined_id_types_have_a_compact_optional_representation() {
        assert_eq!(size_of::<TestId>(), size_of::<u32>());
        assert_eq!(size_of::<Option<TestId>>(), size_of::<u32>());
    }

    #[test]
    fn defined_id_types_preserve_u32_hashing() {
        fn hash(value: impl Hash) -> u64 {
            let mut hasher = DefaultHasher::new();
            value.hash(&mut hasher);
            hasher.finish()
        }

        assert_eq!(hash(TestId::new(42)), hash(42_u32));
    }

    #[test]
    #[should_panic(expected = "TestId cannot represent u32::MAX")]
    fn defined_id_types_reject_the_reserved_value() {
        TestId::new(u32::MAX);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    #[should_panic(expected = "TestId index does not fit in u32")]
    fn defined_id_types_reject_indices_larger_than_u32() {
        TestId::from_index(u32::MAX as usize + 1);
    }
}

/// A helper struct for collections indexed by an ID type, providing both vector storage and name-to-ID mapping.
#[derive(Debug, Clone)]
pub struct NamedIndexed<N: Clone + Eq + Hash, I: Id, T> {
    data: Vec<(T, Option<N>)>,
    name_to_id: FxHashMap<N, I>,
}
impl<N: Clone + Eq + Hash, I: Id, T> NamedIndexed<N, I, T> {
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            name_to_id: FxHashMap::default(),
        }
    }

    /// Insert a new entry with a name, returning its assigned ID.
    /// If the name already exists, it is re-associated with the new ID,
    /// but the old entry remains in the data vector (and can be accessed by its ID).
    pub fn insert(&mut self, name: N, value: T) -> I {
        let id = I::from_index(self.data.len());
        self.data.push((value, Some(name.clone())));
        self.name_to_id.insert(name, id);
        id
    }

    /// Insert a new entry without a name, returning its assigned ID.
    pub fn insert_anonymous(&mut self, value: T) -> I {
        let id = I::from_index(self.data.len());
        self.data.push((value, None));
        id
    }

    /// Replace the value associated with a name, returning the ID and the old value if it existed.
    pub fn replace(&mut self, name: N, mut value: T) -> (I, Option<T>) {
        let cur_index = self.name_to_id.get(&name).copied();
        match cur_index {
            Some(id) => {
                let old_data = &mut self.data[id.as_index()];
                swap(&mut old_data.0, &mut value);
                (id, Some(value))
            }
            None => (self.insert(name, value), None),
        }
    }

    /// Keep the len first data and drop the rest.
    pub fn truncate(&mut self, len: usize) {
        self.name_to_id.retain(|_k, v| v.as_index() < len);
        self.data.truncate(len);
    }

    /// Get the next ID that would be assigned to a new entry.
    pub fn next_id(&self) -> I {
        I::from_index(self.data.len())
    }

    pub fn get(&self, id: I) -> Option<&T> {
        self.data.get(id.as_index()).map(|(data, _)| data)
    }

    pub fn get_mut(&mut self, id: I) -> Option<&mut T> {
        self.data.get_mut(id.as_index()).map(|(data, _)| data)
    }

    pub fn get_by_name(&self, name: &N) -> Option<(I, &T)> {
        self.name_to_id
            .get(name)
            .and_then(|&id| self.get(id).map(|data| (id, data)))
    }

    pub fn get_mut_by_name(&mut self, name: &N) -> Option<(I, &mut T)> {
        let id = *self.name_to_id.get(name)?;
        self.get_mut(id).map(|data| (id, data))
    }

    pub fn get_name(&self, id: I) -> Option<&N> {
        self.data
            .get(id.as_index())
            .and_then(|(_, name)| name.as_ref())
    }

    pub fn iter(&self) -> impl Iterator<Item = &(T, Option<N>)> {
        self.data.iter()
    }

    pub fn enumerate(&self) -> impl Iterator<Item = (I, &T, Option<&N>)> {
        self.data
            .iter()
            .enumerate()
            .map(|(index, (data, name))| (I::from_index(index), data, name.as_ref()))
    }

    pub fn iter_ids(&self) -> impl Iterator<Item = I> {
        (0..self.data.len()).map(I::from_index)
    }

    pub fn enumerates(&self) -> impl Iterator<Item = (I, &T, &Option<N>)> {
        self.data
            .iter()
            .enumerate()
            .map(|(index, (data, name))| (I::from_index(index), data, name))
    }

    pub fn iter_names(&self) -> impl Iterator<Item = &N> {
        self.name_to_id.keys()
    }

    /// Get a value by name, returning only the value (without the ID).
    pub fn get_value_by_name(&self, name: &N) -> Option<&T> {
        self.get_by_name(name).map(|(_, v)| v)
    }

    /// Get the ID of an entry by its name.
    pub fn get_id_by_name(&self, name: &N) -> Option<I> {
        self.name_to_id.get(name).copied()
    }

    /// Iterate over all named entries, yielding `(&name, &value)` pairs.
    pub fn iter_named(&self) -> impl Iterator<Item = (&N, &T)> {
        self.data
            .iter()
            .filter_map(|(data, name_opt)| name_opt.as_ref().map(|name| (name, data)))
    }

    /// Find the name of an entry by a predicate on its value.
    pub fn find_name_by_value(&self, pred: impl Fn(&T) -> bool) -> Option<&N> {
        self.data.iter().find_map(
            |(data, name_opt)| {
                if pred(data) { name_opt.as_ref() } else { None }
            },
        )
    }
}
impl<N: Clone + Eq + Hash, I: Id, T> Default for NamedIndexed<N, I, T> {
    fn default() -> Self {
        Self::new()
    }
}
