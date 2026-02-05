// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::collections::HashMap;
use std::hash::Hash;

/// An ID that can be used as an index into a collection
pub trait Id: Copy {
    fn from_index(index: usize) -> Self;
    fn as_index(self) -> usize;
}

// Small helper macro to declare newtype ID wrappers over u32 with common derives and helpers
#[macro_export]
macro_rules! define_id_type {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name(pub u32);
        impl $crate::module::id::Id for $name {
            #[inline]
            fn from_index(index: usize) -> Self {
                Self(index as u32)
            }
            #[inline]
            fn as_index(self) -> usize {
                self.0 as usize
            }
        }
        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.0)
            }
        }
    };
}

/// A helper struct for collections indexed by an ID type, providing both vector storage and name-to-ID mapping.
#[derive(Debug, Clone)]
pub struct NamedIndexed<N: Clone + Eq + Hash, I: Id, T> {
    data: Vec<(T, Option<N>)>,
    name_to_id: HashMap<N, I>,
}
impl<N: Clone + Eq + Hash, I: Id, T> NamedIndexed<N, I, T> {
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            name_to_id: HashMap::new(),
        }
    }

    pub fn insert(&mut self, name: N, value: T) -> I {
        let id = I::from_index(self.data.len());
        self.data.push((value, Some(name.clone())));
        self.name_to_id.insert(name, id);
        id
    }

    pub fn insert_anonymous(&mut self, value: T) -> I {
        let id = I::from_index(self.data.len());
        self.data.push((value, None));
        id
    }

    pub fn get(&self, id: I) -> Option<&T> {
        self.data.get(id.as_index()).map(|(data, _)| data)
    }

    pub fn get_by_name(&self, name: N) -> Option<(I, &T)> {
        self.name_to_id
            .get(&name)
            .and_then(|&id| self.get(id).map(|data| (id, data)))
    }

    pub fn get_name(&self, id: I) -> Option<&N> {
        self.data
            .get(id.as_index())
            .and_then(|(_, name)| name.as_ref())
    }

    pub fn name_iter(&self) -> impl Iterator<Item = &N> {
        self.name_to_id.keys()
    }

    pub fn data_iter(&self) -> impl Iterator<Item = &(T, Option<N>)> {
        self.data.iter()
    }
}
impl<N: Clone + Eq + Hash, I: Id, T> Default for NamedIndexed<N, I, T> {
    fn default() -> Self {
        Self::new()
    }
}
