// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::ops::{Deref, DerefMut};

use ena::unify::{EqUnifyValue, InPlace, InPlaceUnificationTable, Snapshot, UnifyKey, UnifyValue};

use super::effect_solver::EffectClass;
use crate::types::{
    effects::EffectVarKey,
    mutability::{MutVal, MutVarKey},
    r#type::{TyVarKey, Type},
    type_scheme::PubTypeConstraint,
};

impl UnifyKey for TyVarKey {
    type Value = Option<Type>;

    fn index(&self) -> u32 {
        self.name()
    }

    fn from_index(u: u32) -> Self {
        Self::new(u)
    }

    fn tag() -> &'static str {
        "TyVarKey"
    }
}

impl EqUnifyValue for Type {}

impl UnifyKey for MutVarKey {
    type Value = Option<MutVal>;

    fn index(&self) -> u32 {
        self.name()
    }

    fn from_index(u: u32) -> Self {
        Self::new(u)
    }

    fn tag() -> &'static str {
        "MutVarKey"
    }
}

impl EqUnifyValue for MutVal {}

impl UnifyKey for EffectVarKey {
    type Value = EffectClass;

    fn index(&self) -> u32 {
        self.name()
    }

    fn from_index(u: u32) -> Self {
        Self::new(u)
    }

    fn tag() -> &'static str {
        "EffectVarKey"
    }
}

/// A cache invalidation token. Never reuse a value, including after rollback.
/// Keep a wide counter because speculative mutations are not bounded by the
/// number of variables; checked increment also prevents wrapping in release.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) struct Revision(u64);

impl Revision {
    pub fn advance(&mut self) {
        self.0 = self.0.checked_add(1).expect("inference revision exhausted");
    }
}

/// Equality revisions exclude reads (including path compression) and allocation.
/// Rollback advances the revision: a cache from a speculative branch must never
/// match a later branch, even if both performed the same number of bindings.
#[derive(Debug)]
pub(super) struct RevisionedTable<K: UnifyKey> {
    table: InPlaceUnificationTable<K>,
    revision: Revision,
}

impl<K: UnifyKey> Default for RevisionedTable<K> {
    fn default() -> Self {
        Self::from(InPlaceUnificationTable::default())
    }
}

impl<K: UnifyKey> From<InPlaceUnificationTable<K>> for RevisionedTable<K> {
    fn from(table: InPlaceUnificationTable<K>) -> Self {
        Self {
            table,
            revision: Revision::default(),
        }
    }
}

impl<K: UnifyKey> RevisionedTable<K> {
    pub fn revision(&self) -> Revision {
        self.revision
    }
    pub fn len(&self) -> usize {
        self.table.len()
    }
    pub fn new_key(&mut self, value: K::Value) -> K {
        self.table.new_key(value)
    }
    pub fn find(&mut self, key: impl Into<K>) -> K {
        self.table.find(key)
    }
    pub fn probe_value(&mut self, key: impl Into<K>) -> K::Value {
        self.table.probe_value(key)
    }
    pub fn snapshot(&mut self) -> Snapshot<InPlace<K>> {
        self.table.snapshot()
    }
    pub fn rollback_to(&mut self, snapshot: Snapshot<InPlace<K>>) {
        self.table.rollback_to(snapshot);
        self.revision.advance();
    }
    pub fn unify_var_var(
        &mut self,
        a: impl Into<K>,
        b: impl Into<K>,
    ) -> Result<(), <K::Value as UnifyValue>::Error> {
        self.table.unify_var_var(a, b)?;
        self.revision.advance();
        Ok(())
    }
    pub fn unify_var_value(
        &mut self,
        key: impl Into<K>,
        value: K::Value,
    ) -> Result<(), <K::Value as UnifyValue>::Error> {
        self.table.unify_var_value(key, value)?;
        self.revision.advance();
        Ok(())
    }
}

/// Any mutable access invalidates readers, including replacement with another
/// vector of the same length. Read-only access and cloning the contents do not.
#[derive(Debug, Default)]
pub(super) struct RevisionedConstraints {
    constraints: Vec<PubTypeConstraint>,
    revision: Revision,
}

impl RevisionedConstraints {
    pub fn revision(&self) -> Revision {
        self.revision
    }
}

impl Deref for RevisionedConstraints {
    type Target = Vec<PubTypeConstraint>;
    fn deref(&self) -> &Self::Target {
        &self.constraints
    }
}

impl DerefMut for RevisionedConstraints {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.revision.advance();
        &mut self.constraints
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic(expected = "inference revision exhausted")]
    fn revision_exhaustion_cannot_reuse_a_cache_stamp() {
        Revision(u64::MAX).advance();
    }

    #[test]
    fn equality_revisions_distinguish_speculative_branches() {
        let mut table = RevisionedTable::<MutVarKey>::default();
        let a = table.new_key(None);
        let b = table.new_key(None);
        let initial = table.revision();
        let snapshot = table.snapshot();
        table.find(a);
        table.probe_value(b);
        assert_eq!(table.revision(), initial);
        table.unify_var_var(a, b).unwrap();
        let merged = table.revision();
        assert_ne!(merged, initial);
        table.unify_var_value(a, Some(MutVal::constant())).unwrap();
        let bound = table.revision();
        assert_ne!(bound, merged);
        table.rollback_to(snapshot);
        assert_ne!(table.revision(), bound);
        assert_eq!(table.probe_value(b), None);
        table.unify_var_value(b, Some(MutVal::mutable())).unwrap();
        assert_ne!(table.revision(), bound);
        assert_eq!(table.probe_value(a), None);
    }
}
