// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Inference-local obligation identities and uses of individual givens. Locations
//! are diagnostic data only. Deduplication joins origins before discarding an
//! obligation, and solver snapshots include this provenance.

use crate::{FxHashSet, module::LocalFunctionId, types::type_scheme::ConstraintOrigin};

/// Stable index in the inference context's supplied-evidence list.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct GivenId(pub usize);

#[derive(Clone, Debug, Default)]
pub(super) struct EvidenceUses {
    enabled: bool,
    groups: Vec<OriginGroup>,
    used: Vec<(usize, GivenId)>,
    active_owner: Option<LocalFunctionId>,
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
        let index = self.groups.len();
        self.groups.push(OriginGroup {
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
        while self.groups[index].parent != index {
            index = self.groups[index].parent;
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
        debug_assert_eq!(self.groups[index].owners.len(), 1);
        let was_unowned = self.groups[index].owners.remove(&None);
        debug_assert!(was_unowned);
        self.groups[index].owners.insert(Some(owner));
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
        if self.groups[left].owners.len() < self.groups[right].owners.len() {
            std::mem::swap(&mut left, &mut right);
        }
        self.groups[right].parent = left;
        let owners = std::mem::take(&mut self.groups[right].owners);
        self.groups[left].owners.extend(owners);
    }

    pub fn record(&mut self, origin: ConstraintOrigin, given: GivenId) {
        if !self.enabled {
            return;
        }
        let index = self.ensure_origin(origin);
        self.used.push((index, given));
    }

    pub fn used_by(&self, owner: LocalFunctionId, given: GivenId) -> bool {
        self.used.iter().any(|(index, used_given)| {
            if *used_given != given {
                return false;
            }
            let group = &self.groups[self.root(*index)];
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
