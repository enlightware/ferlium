// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Inference-local obligation identities and uses of individual givens. Locations
//! are diagnostic data only. Deduplication joins origins before discarding an
//! obligation, and solver snapshots include this provenance.

use std::rc::Rc;

use crate::{FxHashSet, module::LocalFunctionId, types::type_scheme::ConstraintOrigin};

/// Stable index in the inference context's supplied-evidence list.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct GivenId(pub usize);

#[derive(Clone, Debug, Default)]
pub(super) struct EvidenceUses {
    enabled: bool,
    // Probes usually only read provenance. Share it with snapshots until a
    // real update; lexical ownership and enablement remain local to each copy.
    data: Rc<EvidenceData>,
    active_owner: Option<LocalFunctionId>,
}

#[derive(Clone, Debug, Default)]
struct EvidenceData {
    groups: Vec<OriginGroup>,
    used: Vec<(usize, GivenId)>,
}

#[derive(Clone, Debug)]
struct OriginGroup {
    parent: usize,
    // None is an explicit unowned contributor, preserved by union like any owner.
    // A root's set is always nonempty; no separate conservative flag is needed.
    owners: FxHashSet<Option<LocalFunctionId>>,
}

impl EvidenceUses {
    pub(super) fn enable(&mut self) {
        self.enabled = true;
    }

    pub(super) fn active_owner(&self) -> Option<LocalFunctionId> {
        self.active_owner
    }

    pub(super) fn replace_active_owner(
        &mut self,
        owner: Option<LocalFunctionId>,
    ) -> Option<LocalFunctionId> {
        std::mem::replace(&mut self.active_owner, owner)
    }

    pub fn fresh_origin(&mut self) -> ConstraintOrigin {
        if !self.enabled {
            return ConstraintOrigin::default();
        }
        let data = Rc::make_mut(&mut self.data);
        let index = data.groups.len();
        data.groups.push(OriginGroup {
            parent: index,
            owners: FxHashSet::from_iter([None]),
        });
        ConstraintOrigin::new(index)
    }

    fn ensure_origin(&mut self, origin: ConstraintOrigin) -> usize {
        origin
            .index()
            .unwrap_or_else(|| self.fresh_origin().index().unwrap())
    }

    fn root(&self, mut index: usize) -> usize {
        while self.data.groups[index].parent != index {
            index = self.data.groups[index].parent;
        }
        index
    }

    pub fn register(&mut self, origin: ConstraintOrigin, owner: LocalFunctionId) {
        if !self.enabled {
            return;
        }
        let index = self.ensure_origin(origin);
        // Ownership is assigned once, before this obligation is solved or merged.
        debug_assert_eq!(self.root(index), index);
        debug_assert_eq!(self.data.groups[index].owners.len(), 1);
        let group = &mut Rc::make_mut(&mut self.data).groups[index];
        let was_unowned = group.owners.remove(&None);
        debug_assert!(was_unowned);
        group.owners.insert(Some(owner));
    }

    pub fn merge(&mut self, kept: ConstraintOrigin, removed: ConstraintOrigin) {
        if !self.enabled {
            return;
        }
        let left = self.ensure_origin(kept);
        let right = self.ensure_origin(removed);
        let mut left = self.root(left);
        let mut right = self.root(right);
        if left == right {
            return;
        }
        if self.data.groups[left].owners.len() < self.data.groups[right].owners.len() {
            std::mem::swap(&mut left, &mut right);
        }
        let data = Rc::make_mut(&mut self.data);
        data.groups[right].parent = left;
        let owners = std::mem::take(&mut data.groups[right].owners);
        data.groups[left].owners.extend(owners);
    }

    pub fn record(&mut self, origin: ConstraintOrigin, given: GivenId) {
        if !self.enabled {
            return;
        }
        let index = self.ensure_origin(origin);
        Rc::make_mut(&mut self.data).used.push((index, given));
    }

    pub fn used_by(&self, owner: LocalFunctionId, given: GivenId) -> bool {
        self.data.used.iter().any(|(index, used_given)| {
            if *used_given != given {
                return false;
            }
            let group = &self.data.groups[self.root(*index)];
            let owners = &group.owners;
            // An obligation introduced outside a registered function scope must
            // never make a supplied dictionary disappear from the ABI.
            owners.contains(&None) || owners.contains(&Some(owner))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{module::id::Id, types::type_inference::unify::UnifiedTypeInference};

    #[test]
    fn evidence_snapshots_share_data_across_no_ops_and_owner_changes() {
        let mut uses = EvidenceUses::default();
        let disabled = uses.clone();
        let owner = LocalFunctionId::from_index(0);
        let missing = ConstraintOrigin::default();
        assert_eq!(uses.fresh_origin(), missing);
        uses.register(missing, owner);
        uses.merge(missing, missing);
        uses.record(missing, GivenId(0));
        uses.enable();
        uses.replace_active_owner(Some(owner));
        assert!(Rc::ptr_eq(&uses.data, &disabled.data));
        assert!(!disabled.enabled);
        assert_eq!(disabled.active_owner(), None);

        let origin = uses.fresh_origin();
        let unowned = uses.clone();
        uses.register(origin, owner);
        uses.record(origin, GivenId(0));
        assert!(!Rc::ptr_eq(&uses.data, &unowned.data));
        assert!(unowned.data.groups[0].owners.contains(&None));
        let snapshot = uses.clone();
        uses.merge(origin, origin);
        uses.enable();
        uses.replace_active_owner(None);
        assert!(uses.used_by(owner, GivenId(0)));
        assert!(Rc::ptr_eq(&uses.data, &snapshot.data));
        assert_eq!(snapshot.active_owner(), Some(owner));
    }

    #[test]
    fn nested_solver_snapshots_restore_evidence_merges_and_unowned_uses() {
        let mut inference = UnifiedTypeInference::default();
        let owner = LocalFunctionId::from_index;
        inference.evidence_uses.enable();
        let a = inference.evidence_uses.fresh_origin();
        let b = inference.evidence_uses.fresh_origin();
        inference.evidence_uses.register(a, owner(0));
        inference.evidence_uses.register(b, owner(1));
        inference.evidence_uses.record(a, GivenId(0));
        inference.evidence_uses.replace_active_owner(Some(owner(0)));
        let outer = inference.snapshot();

        inference.evidence_uses.merge(a, b);
        assert!(inference.given_used_by(owner(1), GivenId(0)));
        let c = inference.evidence_uses.fresh_origin();
        inference.evidence_uses.register(c, owner(2));
        inference.evidence_uses.record(c, GivenId(1));
        inference.evidence_uses.replace_active_owner(Some(owner(1)));
        let inner = inference.snapshot();

        inference.evidence_uses.merge(a, c);
        assert!(inference.given_used_by(owner(0), GivenId(1)));
        let unowned = inference.evidence_uses.fresh_origin();
        inference.evidence_uses.merge(a, unowned);
        assert!(inference.given_used_by(owner(3), GivenId(0)));
        assert!(inference.given_used_by(owner(3), GivenId(1)));
        inference.evidence_uses.replace_active_owner(None);
        inference.rollback_to(inner);

        assert_eq!(inference.evidence_uses.active_owner(), Some(owner(1)));
        assert!(inference.given_used_by(owner(1), GivenId(0)));
        assert!(inference.given_used_by(owner(2), GivenId(1)));
        assert!(!inference.given_used_by(owner(0), GivenId(1)));
        assert!(!inference.given_used_by(owner(3), GivenId(0)));
        inference.rollback_to(outer);

        assert_eq!(inference.evidence_uses.active_owner(), Some(owner(0)));
        assert!(inference.given_used_by(owner(0), GivenId(0)));
        assert!(!inference.given_used_by(owner(1), GivenId(0)));
        assert!(!inference.given_used_by(owner(2), GivenId(1)));
        assert_eq!(inference.evidence_uses.fresh_origin(), c);
    }

    #[test]
    fn deduplicated_evidence_retains_transitive_owners() {
        let mut uses = EvidenceUses::default();
        uses.enable();
        let origins = (0..3)
            .map(|index| {
                let origin = uses.fresh_origin();
                uses.register(origin, LocalFunctionId::from_index(index));
                origin
            })
            .collect::<Vec<_>>();
        uses.merge(origins[0], origins[1]);
        uses.record(origins[0], GivenId(0));
        uses.merge(origins[1], origins[2]);
        for index in 0..3 {
            assert!(uses.used_by(LocalFunctionId::from_index(index), GivenId(0)));
            assert!(!uses.used_by(LocalFunctionId::from_index(index), GivenId(1)));
        }
        assert!(!uses.used_by(LocalFunctionId::from_index(3), GivenId(0)));
    }

    #[test]
    fn obligations_at_the_same_location_keep_owners_separate() {
        use crate::{
            Location,
            module::{LocalTraitId, ModuleId, TraitId},
            types::type_inference::{constraints::TypeConstraint, expr::TypeInference},
            types::{r#type::Type, type_scheme::PubTypeConstraint},
        };
        let mut inference = TypeInference::default();
        let constraint = PubTypeConstraint::new_have_trait(
            TraitId::new(ModuleId::new(0), LocalTraitId::new(0)),
            vec![Type::unit()],
            vec![],
            vec![],
            Location::new_synthesized(),
        );
        let given = inference.add_given_constraint(constraint.clone());
        for index in 0..2 {
            let start = inference.constraint_scope_start();
            inference.add_pub_constraint(constraint.clone());
            inference.own_constraints_since(start, LocalFunctionId::from_index(index));
        }
        let TypeConstraint::Pub(first) = &inference.ty_constraints[0] else {
            panic!("public obligation");
        };
        inference.evidence_uses.record(first.origin(), given);
        assert!(
            inference
                .evidence_uses
                .used_by(LocalFunctionId::from_index(0), given)
        );
        assert!(
            !inference
                .evidence_uses
                .used_by(LocalFunctionId::from_index(1), given)
        );
    }

    #[test]
    fn unowned_evidence_remains_conservative_when_merged_with_known_use() {
        let mut uses = EvidenceUses::default();
        uses.enable();
        let a = uses.fresh_origin();
        let b = uses.fresh_origin();
        uses.register(a, LocalFunctionId::from_index(0));
        uses.record(a, GivenId(0));
        uses.merge(a, b);
        assert!(uses.used_by(LocalFunctionId::from_index(1), GivenId(0)));
    }

    #[test]
    fn owner_scope_restores_outer_owner_after_early_return() {
        fn nested(inference: &mut UnifiedTypeInference) -> Result<(), ()> {
            let scope = inference.constraint_owner_scope(LocalFunctionId::from_index(1));
            assert_eq!(
                scope.evidence_uses.active_owner(),
                Some(LocalFunctionId::from_index(1))
            );
            Err(())
        }
        let mut inference = UnifiedTypeInference::default();
        {
            let mut scope = inference.constraint_owner_scope(LocalFunctionId::from_index(0));
            assert!(nested(&mut scope).is_err());
            assert_eq!(
                scope.evidence_uses.active_owner(),
                Some(LocalFunctionId::from_index(0))
            );
        }
        assert_eq!(inference.evidence_uses.active_owner(), None);
    }

    #[test]
    fn rejected_solver_probe_does_not_retain_evidence_use() {
        let mut inference = UnifiedTypeInference::default();
        let owner = LocalFunctionId::from_index(0);
        inference.evidence_uses.enable();
        let origin = inference.evidence_uses.fresh_origin();
        inference.evidence_uses.register(origin, owner);
        let snapshot = inference.snapshot();
        inference.evidence_uses.record(origin, GivenId(0));
        assert!(inference.given_used_by(owner, GivenId(0)));
        inference.rollback_to(snapshot);
        assert!(!inference.given_used_by(owner, GivenId(0)));
    }
}
