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
//! The representation is biased for the observed distribution: ~10% of types
//! have no free variables at all, and the names of free variables are almost
//! always small (max name 76 across the std + test workloads, with 96% of
//! occurrences fitting in `Compact(u64)`). The `Many` variant is the cold
//! insurance path for higher names.

use std::iter::FusedIterator;
use std::marker::PhantomData;

use crate::types::{effects::EffectVar, mutability::MutVar, r#type::TypeVar};

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
///
/// Invariants:
/// - `Compact(0)` is normalised to `Empty`.
/// - `Many(words)` is only used when at least one bit with name >= 64 is set;
///   it is never used when `Compact` would suffice. Trailing zero words are
///   trimmed so equal sets always have equal `Many` payloads.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct KindVarSet<V: NamedVar> {
    repr: Repr,
    _phantom: PhantomData<fn() -> V>,
}

impl<V: NamedVar> Default for KindVarSet<V> {
    fn default() -> Self {
        Self::empty()
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
enum Repr {
    #[default]
    Empty,
    Compact(u64),
    Many(Box<[u64]>),
}

impl<V: NamedVar> KindVarSet<V> {
    pub const fn empty() -> Self {
        Self {
            repr: Repr::Empty,
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
        matches!(self.repr, Repr::Empty)
    }

    pub fn insert(&mut self, var: V) {
        let name = var.name();
        if name < 64 {
            let bit = 1u64 << name;
            match &mut self.repr {
                Repr::Empty => self.repr = Repr::Compact(bit),
                Repr::Compact(bits) => *bits |= bit,
                Repr::Many(words) => words[0] |= bit,
            }
            return;
        }
        // name >= 64: must use Many.
        let word = name as usize / 64;
        let bit = 1u64 << (name % 64);
        let needed_len = word + 1;
        match &mut self.repr {
            Repr::Empty => {
                self.repr = Repr::Many(boxed_slice_with(needed_len, |i| {
                    if i == word { bit } else { 0 }
                }));
            }
            Repr::Compact(low) => {
                let low = *low;
                self.repr = Repr::Many(boxed_slice_with(needed_len, |i| match i {
                    0 if word == 0 => low | bit,
                    0 => low,
                    i if i == word => bit,
                    _ => 0,
                }));
            }
            Repr::Many(words) => {
                if words.len() < needed_len {
                    let old = std::mem::take(words);
                    *words = boxed_slice_with(needed_len, |i| {
                        let prev = old.get(i).copied().unwrap_or(0);
                        if i == word { prev | bit } else { prev }
                    });
                } else {
                    words[word] |= bit;
                }
            }
        }
    }

    /// Mutate `self` to be the union of itself and `other`.
    pub fn union_with(&mut self, other: &Self) {
        match (&mut self.repr, &other.repr) {
            (_, Repr::Empty) => {}
            (Repr::Empty, _) => *self = other.clone(),
            (Repr::Compact(a), Repr::Compact(b)) => {
                *a |= *b;
            }
            (Repr::Many(a), Repr::Compact(b)) => {
                a[0] |= *b;
            }
            (Repr::Compact(a), Repr::Many(b)) => {
                let low = *a;
                self.repr = Repr::Many(boxed_slice_with(b.len(), |i| {
                    if i == 0 { low | b[0] } else { b[i] }
                }));
            }
            (Repr::Many(a), Repr::Many(b)) => {
                let len = a.len().max(b.len());
                if a.len() == len {
                    for (i, word) in b.iter().enumerate() {
                        a[i] |= *word;
                    }
                } else {
                    let old = std::mem::take(a);
                    *a = boxed_slice_with(len, |i| {
                        let av = old.get(i).copied().unwrap_or(0);
                        let bv = b.get(i).copied().unwrap_or(0);
                        av | bv
                    });
                }
            }
        }
    }

    /// Returns true if `self` and `other` share at least one variable.
    pub fn intersects(&self, other: &Self) -> bool {
        match (&self.repr, &other.repr) {
            (Repr::Empty, _) | (_, Repr::Empty) => false,
            (Repr::Compact(a), Repr::Compact(b)) => (*a & *b) != 0,
            (Repr::Compact(a), Repr::Many(b)) | (Repr::Many(b), Repr::Compact(a)) => {
                (*a & b[0]) != 0
            }
            (Repr::Many(a), Repr::Many(b)) => a.iter().zip(b.iter()).any(|(x, y)| (x & y) != 0),
        }
    }

    /// Iterate over the variables present in the set, in ascending name order.
    pub fn iter(&self) -> KindVarSetIter<'_, V> {
        let words: &[u64] = match &self.repr {
            Repr::Empty => &[],
            Repr::Compact(bits) => std::slice::from_ref(bits),
            Repr::Many(words) => words,
        };
        KindVarSetIter {
            words,
            word_idx: 0,
            current: words.first().copied().unwrap_or(0),
            _phantom: PhantomData,
        }
    }

    /// Number of variables present in the set.
    pub fn len(&self) -> usize {
        match &self.repr {
            Repr::Empty => 0,
            Repr::Compact(bits) => bits.count_ones() as usize,
            Repr::Many(words) => words.iter().map(|w| w.count_ones() as usize).sum(),
        }
    }

    /// Returns true if `self` contains the given variable.
    pub fn contains(&self, var: V) -> bool {
        let name = var.name();
        let word = name as usize / 64;
        let bit = 1u64 << (name % 64);
        match &self.repr {
            Repr::Empty => false,
            Repr::Compact(bits) => word == 0 && (*bits & bit) != 0,
            Repr::Many(words) => words.get(word).is_some_and(|w| (w & bit) != 0),
        }
    }
}

/// Allocate a `Box<[u64]>` of exactly `len` words, filled by `f(i)`.
fn boxed_slice_with(len: usize, mut f: impl FnMut(usize) -> u64) -> Box<[u64]> {
    (0..len).map(&mut f).collect()
}

/// Ascending-name iterator over a `KindVarSet<V>`'s elements.
pub struct KindVarSetIter<'a, V: NamedVar> {
    words: &'a [u64],
    word_idx: usize,
    /// Bits of the current word still to be yielded; cleared as we go.
    current: u64,
    _phantom: PhantomData<fn() -> V>,
}

impl<V: NamedVar> Iterator for KindVarSetIter<'_, V> {
    type Item = V;

    fn next(&mut self) -> Option<V> {
        loop {
            if self.current != 0 {
                let bit = self.current.trailing_zeros();
                self.current &= self.current - 1;
                let name = (self.word_idx as u32) * 64 + bit;
                return Some(V::from_name(name));
            }
            self.word_idx += 1;
            if self.word_idx >= self.words.len() {
                return None;
            }
            self.current = self.words[self.word_idx];
        }
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
