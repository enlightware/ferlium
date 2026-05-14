// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

//! Compact bitmap of named variables (type, mutability, or effect vars).
//!
//! Used to cache the set of free variables of an interned `TypeKind`, so that
//! substitution can short-circuit when a substitution's domain does not
//! intersect a type's free variables.
//!
//! The representation is biased for the observed distribution: most variable
//! names fit in one inline `u64`, with a boxed-slice fallback for higher names.

use std::iter::FusedIterator;
use std::marker::PhantomData;

use crate::{
    containers::{DenseBitSet, DenseBitSetOnes},
    types::{effects::EffectVar, mutability::MutVar, r#type::TypeVar},
};

/// A trait for variable identifiers represented by a small `u32` name.
pub trait NamedVar: Copy {
    fn name(self) -> u32;
    fn from_name(name: u32) -> Self;
}

impl NamedVar for TypeVar {
    fn name(self) -> u32 {
        TypeVar::name(&self)
    }
    fn from_name(name: u32) -> Self {
        TypeVar::new(name)
    }
}

impl NamedVar for MutVar {
    fn name(self) -> u32 {
        MutVar::name(&self)
    }
    fn from_name(name: u32) -> Self {
        MutVar::new(name)
    }
}

impl NamedVar for EffectVar {
    fn name(self) -> u32 {
        EffectVar::name(&self)
    }
    fn from_name(name: u32) -> Self {
        EffectVar::new(name)
    }
}

/// A compact set of `NamedVar`s identified by their `name()` index.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct KindVarSet<V: NamedVar> {
    bits: DenseBitSet,
    _phantom: PhantomData<fn() -> V>,
}

impl<V: NamedVar> Default for KindVarSet<V> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<V: NamedVar> KindVarSet<V> {
    pub const fn empty() -> Self {
        Self {
            bits: DenseBitSet::empty(),
            _phantom: PhantomData,
        }
    }

    pub fn singleton(var: V) -> Self {
        let mut set = Self::empty();
        set.insert(var);
        set
    }

    pub fn from_iterator<I: IntoIterator<Item = V>>(vars: I) -> Self {
        let mut set = Self::empty();
        for var in vars {
            set.insert(var);
        }
        set
    }

    pub fn is_empty(&self) -> bool {
        self.bits.is_empty()
    }

    pub fn insert(&mut self, var: V) {
        self.bits.insert(var.name() as usize);
    }

    /// Mutate `self` to be the union of itself and `other`.
    pub fn union_with(&mut self, other: &Self) {
        self.bits.union_with(&other.bits);
    }

    /// Returns true if `self` and `other` share at least one variable.
    pub fn intersects(&self, other: &Self) -> bool {
        self.bits.intersects(&other.bits)
    }

    /// Iterate over the variables present in the set, in ascending name order.
    pub fn iter(&self) -> KindVarSetIter<'_, V> {
        KindVarSetIter {
            inner: self.bits.iter_ones(),
            _phantom: PhantomData,
        }
    }

    /// Number of variables present in the set.
    pub fn len(&self) -> usize {
        self.bits.len()
    }

    /// Returns true if `self` contains the given variable.
    pub fn contains(&self, var: V) -> bool {
        self.bits.contains(var.name() as usize)
    }
}

/// Ascending-name iterator over a `KindVarSet<V>`'s elements.
pub struct KindVarSetIter<'a, V: NamedVar> {
    inner: DenseBitSetOnes<'a>,
    _phantom: PhantomData<fn() -> V>,
}

impl<V: NamedVar> Iterator for KindVarSetIter<'_, V> {
    type Item = V;

    fn next(&mut self) -> Option<V> {
        self.inner.next().map(|name| V::from_name(name as u32))
    }
}

impl<V: NamedVar> FusedIterator for KindVarSetIter<'_, V> {}

#[cfg(test)]
mod tests {
    use super::*;

    fn ty(name: u32) -> TypeVar {
        TypeVar::new(name)
    }

    #[test]
    fn empty_is_empty() {
        let s = KindVarSet::<TypeVar>::empty();
        assert!(s.is_empty());
        assert!(!s.contains(ty(0)));
    }

    #[test]
    fn insert_compact() {
        let mut s = KindVarSet::<TypeVar>::empty();
        s.insert(ty(3));
        s.insert(ty(63));
        assert!(s.contains(ty(3)));
        assert!(s.contains(ty(63)));
        assert!(!s.contains(ty(64)));
        assert!(!s.is_empty());
    }

    #[test]
    fn insert_promotes_to_many() {
        let mut s = KindVarSet::<TypeVar>::singleton(ty(5));
        s.insert(ty(80));
        assert!(s.contains(ty(5)));
        assert!(s.contains(ty(80)));
        assert!(!s.contains(ty(64)));
    }

    #[test]
    fn intersects_compact_compact() {
        let a = KindVarSet::<TypeVar>::from_iterator([ty(1), ty(5)]);
        let b = KindVarSet::<TypeVar>::from_iterator([ty(5), ty(7)]);
        let c = KindVarSet::<TypeVar>::from_iterator([ty(0), ty(2)]);
        assert!(a.intersects(&b));
        assert!(b.intersects(&a));
        assert!(!a.intersects(&c));
    }

    #[test]
    fn intersects_with_many() {
        let a = KindVarSet::<TypeVar>::from_iterator([ty(1), ty(80)]);
        let b = KindVarSet::<TypeVar>::singleton(ty(80));
        assert!(a.intersects(&b));
        let c = KindVarSet::<TypeVar>::singleton(ty(81));
        assert!(!a.intersects(&c));
    }

    #[test]
    fn union_normalises() {
        let mut a = KindVarSet::<TypeVar>::singleton(ty(1));
        let b = KindVarSet::<TypeVar>::singleton(ty(80));
        a.union_with(&b);
        assert!(a.contains(ty(1)));
        assert!(a.contains(ty(80)));
    }

    #[test]
    fn union_with_empty_noop() {
        let mut a = KindVarSet::<TypeVar>::singleton(ty(1));
        let before = a.clone();
        a.union_with(&KindVarSet::empty());
        assert_eq!(a, before);
    }

    #[test]
    fn empty_into_nonempty() {
        let mut a = KindVarSet::<TypeVar>::empty();
        let b = KindVarSet::<TypeVar>::singleton(ty(1));
        a.union_with(&b);
        assert!(a.contains(ty(1)));
    }
}
