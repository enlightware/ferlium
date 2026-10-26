// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Saturation and checked selection of ordinary subtype bounds.

use std::{collections::hash_map::Entry, mem};

use super::{
    ground_bounds::{BoundOperation, ground_bound, symbolic_bound},
    type_bounds::TypeBound,
    unify::{SubOrSameType, UnifiedTypeInference},
};
use crate::{
    FxHashMap, FxHashSet,
    compiler::error::InternalCompilationError,
    internal_compilation_error,
    parser::location::Location,
    types::{
        effects::EffType,
        mutability::MutType,
        r#type::{Type, TypeKind, TypeVar, store_types},
        type_like::TypeLike,
    },
};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum SelectionPhase {
    /// Propagation may still reveal structural or trait-produced contributors.
    Inference,
    /// Reconcile structure, but preserve pending trait-output dependencies.
    Preparation,
    /// Eligible defaults have settled; conservatively close residual bounds.
    Publication,
}

#[derive(Debug, Default)]
pub(super) struct SelectionStats {
    normalizations: usize,
    performed_bounds_normalizations: usize,
    skipped_bounds_normalizations: usize,
    pub(super) performed_constraint_normalizations: usize,
    pub(super) skipped_constraint_normalizations: usize,
    scc_passes: usize,
    structural_comparisons: usize,
    products: usize,
    selections: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        compiler::error::CompilationErrorImpl,
        std::{logic::bool_type, math::int_type},
    };

    #[test]
    fn publication_budget_exhaustion_returns_an_internal_error() {
        for final_publication in [false, true] {
            let mut inference = UnifiedTypeInference::default();
            inference
                .solve_publication_bounds_with_limit(final_publication, 1)
                .unwrap();
            let error = inference
                .solve_publication_bounds_with_limit(final_publication, 0)
                .unwrap_err();
            assert!(matches!(
                error.into_inner(),
                CompilationErrorImpl::Internal { error, .. }
                    if error == "type-bound publication failed to converge after 0 rounds"
            ));

            let mut inference = UnifiedTypeInference::new_with_ty_vars(1);
            let span = Location::new_synthesized();
            inference.bounds.insert(TypeBound {
                lower: int_type(),
                lower_span: span,
                upper: Type::variable_id(0),
                upper_span: span,
            });
            // Selecting the lower bound makes progress, but must not renew
            // the budget: another round is needed to establish convergence.
            let error = inference
                .solve_publication_bounds_with_limit(final_publication, 1)
                .unwrap_err();
            assert!(matches!(
                error.into_inner(),
                CompilationErrorImpl::Internal { error, .. }
                    if error == "type-bound publication failed to converge after 1 rounds"
            ));
            inference
                .solve_publication_bounds(final_publication)
                .unwrap();
            assert_eq!(inference.normalize_type(Type::variable_id(0)), int_type());
        }
    }

    #[test]
    fn component_publication_keeps_disjoint_shapes_and_effect_rows_independent() {
        const COMPONENTS: u32 = 32;
        let mut inference = UnifiedTypeInference::new_with_ty_vars(2 * COMPONENTS + 5);
        let span = Location::new_synthesized();
        let edge = |lower, upper| TypeBound {
            lower,
            lower_span: span,
            upper,
            upper_span: span,
        };
        let variable = Type::variable_id;
        let bottom = Type::nullary_function_by_val(Type::never());
        let result = |index| {
            if index % 2 == 0 {
                int_type()
            } else {
                bool_type()
            }
        };
        let mut relations = Vec::new();
        for index in (0..COMPONENTS).rev() {
            relations.push(edge(variable(2 * index), variable(2 * index + 1)));
            relations.push(edge(bottom, variable(2 * index)));
        }
        for index in 0..COMPONENTS {
            relations.push(edge(
                Type::nullary_function_by_val(result(index)),
                variable(2 * index + 1),
            ));
            relations.push(edge(Type::never(), variable(2 * index)));
        }
        let empty = 2 * COMPONENTS;
        let recursive = empty + 2;
        let singleton = empty + 4;
        relations.extend([
            edge(variable(empty), variable(empty + 1)),
            edge(variable(recursive), variable(recursive + 1)),
            edge(
                Type::nullary_function_by_val(variable(recursive)),
                variable(recursive + 1),
            ),
            edge(bottom, variable(singleton)),
            edge(bottom, Type::nullary_function_by_val(int_type())),
        ]);
        assert!(inference.publish_component_shapes(&relations).unwrap());
        let mut effects = FxHashSet::default();
        for index in 0..COMPONENTS {
            for var in [2 * index, 2 * index + 1] {
                let ty = inference.normalize_type(variable(var));
                let data = ty.data();
                let function = data.as_function().unwrap();
                assert_eq!(function.ret, result(index));
                assert!(effects.insert(function.effects.to_single_variable().unwrap()));
            }
        }
        for var in empty..=singleton {
            assert_eq!(inference.normalize_type(variable(var)), variable(var));
        }
    }

    #[test]
    fn component_publication_preserves_component_and_contributor_diagnostic_order() {
        use crate::compiler::error::CompilationErrorImpl;
        let mut inference = UnifiedTypeInference::new_with_ty_vars(4);
        let location =
            |offset| Location::new(offset, offset + 1, Location::new_synthesized().source_id);
        let edge = |lower, upper, offset| TypeBound {
            lower,
            lower_span: location(offset),
            upper,
            upper_span: location(offset),
        };
        let int = Type::nullary_function_by_val(int_type());
        let boolean = Type::nullary_function_by_val(bool_type());
        let variable = Type::variable_id;
        // Component 2 appears first, but component 0 must still publish first.
        // Its contributors retain input order, even with spans in reverse order.
        let relations = [
            edge(variable(2), variable(3), 0),
            edge(variable(0), variable(1), 1),
            edge(boolean, variable(2), 2),
            edge(int, variable(1), 50),
            edge(int, variable(3), 40),
            edge(boolean, variable(0), 5),
        ];
        let error = inference.publish_component_shapes(&relations).unwrap_err();
        let CompilationErrorImpl::TypeMismatch {
            current_ty,
            current_span,
            expected_ty,
            expected_span,
            ..
        } = error.into_inner()
        else {
            panic!("expected callable mismatch");
        };
        assert_eq!((current_ty, current_span), (boolean, location(5)));
        assert_eq!((expected_ty, expected_span), (int, location(50)));
    }

    #[test]
    fn immutable_bound_comparisons_survive_rebuilds_and_rollback() {
        let mut inference = UnifiedTypeInference::new_with_ty_vars(2);
        let span = Location::new_synthesized();
        let lower = Type::nullary_function_by_val(Type::never());
        let upper = Type::nullary_function_by_val(int_type());
        let a = Type::variable_id(0);
        let b = Type::variable_id(1);
        for (lower, upper) in [(lower, a), (a, upper), (b, a)] {
            inference.unify_sub_type(lower, span, upper, span).unwrap();
        }
        let snapshot = inference.snapshot();
        inference.propagate_type_bounds().unwrap();
        assert!(inference.checked_bounds.contains(&(lower, upper)));
        let comparisons = inference.selection_stats.structural_comparisons;
        inference.unify_same_type(b, span, lower, span).unwrap();
        inference.propagate_type_bounds().unwrap();
        assert_eq!(
            inference.selection_stats.structural_comparisons,
            comparisons
        );
        inference.rollback_to(snapshot);
        inference.propagate_type_bounds().unwrap();
        assert_eq!(
            inference.selection_stats.structural_comparisons,
            comparisons
        );
        inference
            .unify_same_type(b, span, Type::nullary_function_by_val(bool_type()), span)
            .unwrap();
        assert!(inference.propagate_type_bounds().is_err());
        assert_eq!(inference.checked_bounds.len(), 1);
    }

    #[test]
    fn symbolic_effect_comparisons_are_not_cached() {
        use crate::types::{effects::PrimitiveEffect, r#type::FnType};
        let mut inference = UnifiedTypeInference::default();
        let span = Location::new_synthesized();
        let effect = EffType::single_variable(inference.fresh_effect_var());
        let lower = Type::function_type(FnType::new(vec![], int_type(), effect.clone()));
        let upper = Type::nullary_function_by_val(int_type());
        inference.bounds.insert(TypeBound {
            lower,
            lower_span: span,
            upper,
            upper_span: span,
        });
        let snapshot = inference.snapshot();
        inference.propagate_type_bounds().unwrap();
        assert!(inference.checked_bounds.is_empty());
        inference.rollback_to(snapshot);
        inference
            .unify_same_effect(
                effect,
                span,
                EffType::single_primitive(PrimitiveEffect::Write),
                span,
            )
            .unwrap();
        assert!(inference.propagate_type_bounds().is_err());
    }

    #[test]
    fn discharged_bounds_are_restored_by_speculative_rollback() {
        let span = Location::new_synthesized();
        let var = Type::variable_id(0);
        let mut inference = UnifiedTypeInference::new_with_ty_vars(1);
        inference
            .unify_sub_type(var, span, int_type(), span)
            .unwrap();
        let snapshot = inference.snapshot();
        inference
            .unify_same_type(var, span, Type::never(), span)
            .unwrap();
        inference.propagate_type_bounds().unwrap();
        assert_eq!(inference.bounds.relations().count(), 0);
        inference.rollback_to(snapshot);
        inference
            .unify_same_type(var, span, bool_type(), span)
            .unwrap();
        assert!(inference.propagate_type_bounds().is_err());
    }

    #[test]
    fn selected_bounds_hold_for_every_remaining_model_instantiation() {
        let domain = [
            (Type::never(), 0_u8),
            (int_type(), 1),
            (bool_type(), 2),
            (Type::nullary_function_by_val(Type::never()), 4),
            (Type::nullary_function_by_val(int_type()), 12),
        ];
        let terms: Vec<_> = [Type::variable_id(0), Type::variable_id(1)]
            .into_iter()
            .chain(domain.iter().map(|(ty, _)| *ty))
            .collect();
        let edges: Vec<_> = terms
            .iter()
            .flat_map(|a| terms.iter().map(move |b| (*a, *b)))
            .collect();
        let span = Location::new_synthesized();
        for (i, first) in edges.iter().enumerate() {
            for second in &edges[i..] {
                let mut accepted = None;
                for inputs in [[*first, *second], [*second, *first]] {
                    let mut inference = UnifiedTypeInference::new_with_ty_vars(2);
                    let result = inputs
                        .iter()
                        .try_for_each(|(a, b)| inference.unify_sub_type(*a, span, *b, span))
                        .and_then(|()| inference.publish_type_bounds());
                    if let Some(previous) = accepted {
                        assert_eq!(previous, result.is_ok(), "{inputs:?}");
                    }
                    accepted = Some(result.is_ok());
                    if result.is_err() {
                        continue;
                    }
                    inference
                        .minimize_unobservable_effects(FxHashSet::default())
                        .unwrap();
                    inference.finalize_effect_dependencies().unwrap();
                    for x in 0..domain.len() {
                        for y in 0..domain.len() {
                            let assignment = [x, y];
                            let mut value = |ty| {
                                let ty = inference.substitute_in_type(ty);
                                if let Some(var) = ty.data().as_variable() {
                                    domain[assignment[var.name() as usize]].1
                                } else {
                                    domain
                                        .iter()
                                        .find(|(t, _)| *t == ty)
                                        .expect("model is closed")
                                        .1
                                }
                            };
                            for (a, b) in inputs {
                                let (a, b) = (value(a), value(b));
                                assert_eq!(a & b, a, "{inputs:?}, assignment {assignment:?}");
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn selection_waits_for_late_equalities_and_rolls_back_bounds() {
        let span = Location::new_synthesized();
        let result = Type::variable_id(0);
        let joined = Type::variable_id(1);
        for order in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            let mut inference = UnifiedTypeInference::new_with_ty_vars(2);
            let snapshot = inference.snapshot();
            for step in order {
                match step {
                    0 => inference
                        .unify_sub_type(Type::nullary_function_by_val(result), span, joined, span)
                        .unwrap(),
                    1 => inference
                        .unify_sub_type(
                            Type::nullary_function_by_val(int_type()),
                            span,
                            joined,
                            span,
                        )
                        .unwrap(),
                    _ => inference
                        .unify_same_type(result, span, Type::never(), span)
                        .unwrap(),
                }
            }
            inference.publish_type_bounds().unwrap();
            assert_eq!(
                inference.substitute_in_type(joined),
                Type::nullary_function_by_val(int_type())
            );
            inference.rollback_to(snapshot);
            assert_eq!(inference.substitute_in_type(result), result);
            assert_eq!(inference.substitute_in_type(joined), joined);
            assert_eq!(inference.bounds.relations().count(), 0);
            assert!(inference.bottom_sources.is_empty());
        }
    }

    #[test]
    fn dependent_recursive_selection_uses_equation_validation() {
        let span = Location::new_synthesized();
        let a = Type::variable_id(0);
        let b = Type::variable_id(1);
        for reversed in [false, true] {
            let mut inference = UnifiedTypeInference::new_with_ty_vars(2);
            let mut inputs = [(a, Type::tuple([b])), (b, Type::tuple([a]))];
            if reversed {
                inputs.reverse();
            }
            for (lower, upper) in inputs {
                inference.unify_sub_type(lower, span, upper, span).unwrap();
            }
            assert!(inference.publish_type_bounds().is_err());
            assert_eq!(inference.ty_unification_table.len(), 2);
        }
    }

    #[test_log::test]
    fn selection_batches_long_chains_and_dense_components() {
        let span = Location::new_synthesized();
        for (count, dense) in [(1024, false), (64, true)] {
            for reverse in [false, true] {
                let mut inference = UnifiedTypeInference::new_with_ty_vars(count);
                let mut edges = Vec::new();
                for i in 0..count - 1 {
                    for j in i + 1..if dense { count } else { i + 2 } {
                        edges.push((Type::variable_id(i), Type::variable_id(j)));
                    }
                }
                if reverse {
                    edges.reverse();
                }
                for (a, b) in edges {
                    inference.unify_sub_type(a, span, b, span).unwrap();
                }
                inference
                    .unify_sub_type(int_type(), span, Type::variable_id(0), span)
                    .unwrap();
                assert!(
                    inference
                        .select_lower_bounds(false, SelectionPhase::Inference)
                        .unwrap()
                );
                for i in 0..count {
                    assert_eq!(
                        inference.substitute_in_type(Type::variable_id(i)),
                        int_type()
                    );
                }
                // The first root is forced immediately by its maximal lower bound.
                assert_eq!(inference.selection_stats.selections, count as usize - 1);
                assert!(inference.selection_stats.normalizations <= 2);
                assert!(
                    !inference
                        .select_lower_bounds(false, SelectionPhase::Inference)
                        .unwrap()
                );
                inference.log_bounds_stats();
            }
        }
    }

    #[test]
    fn selection_waits_for_unconstrained_predecessors() {
        let span = Location::new_synthesized();
        let mut inference = UnifiedTypeInference::new_with_ty_vars(3);
        for (a, b) in [
            (Type::variable_id(0), Type::variable_id(1)),
            (Type::variable_id(1), Type::variable_id(2)),
            (
                Type::nullary_function_by_val(Type::never()),
                Type::variable_id(1),
            ),
        ] {
            inference.unify_sub_type(a, span, b, span).unwrap();
        }
        assert!(
            !inference
                .select_lower_bounds(false, SelectionPhase::Inference)
                .unwrap()
        );
        assert_eq!(
            inference.substitute_in_type(Type::variable_id(2)),
            Type::variable_id(2)
        );
    }

    #[test]
    fn selection_without_contributors_still_saturates_bounds() {
        let span = Location::new_synthesized();
        for phase in [
            SelectionPhase::Inference,
            SelectionPhase::Preparation,
            SelectionPhase::Publication,
        ] {
            let mut inference = UnifiedTypeInference::new_with_ty_vars(2);
            let a = Type::variable_id(0);
            let b = Type::variable_id(1);
            for (lower, upper) in [(a, b), (b, a)] {
                inference.unify_sub_type(lower, span, upper, span).unwrap();
            }
            // Neither variable has a concrete contributor, but the cycle must
            // still collapse before selection reports that it made no choice.
            assert!(!inference.select_lower_bounds(false, phase).unwrap());
            assert_eq!(inference.normalize_type(a), inference.normalize_type(b));
            assert_eq!(inference.selection_stats.selections, 0);

            // A structural pair also has no variable to select. Its queued
            // check must not disappear behind the empty-contributor return.
            inference.bounds.insert(TypeBound {
                lower: Type::nullary_function_by_val(int_type()),
                lower_span: span,
                upper: Type::nullary_function_by_val(bool_type()),
                upper_span: span,
            });
            assert!(inference.select_lower_bounds(false, phase).is_err());
        }
    }

    #[test]
    fn bottom_generalization_requires_known_read_only_access() {
        use crate::types::r#type::{FnArgType, FnType};
        let inner = Type::function_type(FnType::new_mut_resolved(
            [(Type::never(), false)],
            Type::unit(),
            Default::default(),
        ));
        for access in [
            MutType::constant(),
            MutType::mutable(),
            MutType::variable_id(0),
        ] {
            let mut inference = UnifiedTypeInference::default();
            let outer = Type::function_type(FnType::new(
                vec![FnArgType::new(inner, access)],
                Type::unit(),
                Default::default(),
            ));
            let generalized = inference.generalize_bottom_leaves(outer);
            if access == MutType::constant() {
                assert_eq!(generalized.inner_ty_vars().len(), 1);
            } else {
                assert_eq!(generalized, outer);
            }
        }
    }

    #[test]
    fn unsuccessful_reduction_rolls_back_all_effect_meets() {
        use crate::types::r#type::FnType;
        let mut inference = UnifiedTypeInference::new_with_ty_vars(1);
        let first = EffType::single_variable(inference.fresh_effect_var());
        let second = EffType::single_variable(inference.fresh_effect_var());
        let function = |ret, effects| Type::function_type(FnType::new(vec![], ret, effects));
        let span = Location::new_synthesized();
        let bounds: Vec<_> = [
            function(int_type(), first),
            function(int_type(), second),
            function(Type::variable_id(0), Default::default()),
        ]
        .into_iter()
        .map(|upper| TypeBound {
            lower: Type::variable_id(0),
            lower_span: span,
            upper,
            upper_span: span,
        })
        .collect();
        let before = inference.effects.var_count();
        assert!(
            inference
                .reduce_bounds(&bounds, BoundOperation::Meet)
                .unwrap()
                .is_none()
        );
        assert_eq!(inference.effects.var_count(), before);
    }

    #[test]
    fn pending_trait_outputs_block_prepublication_selection() {
        use crate::{
            module::{LocalTraitId, ModuleId, TraitId},
            types::type_scheme::PubTypeConstraint,
        };
        let mut inference = UnifiedTypeInference::new_with_ty_vars(3);
        let input = Type::variable_id(0);
        let output = Type::variable_id(1);
        let nested = Type::variable_id(2);
        let span = Location::new_synthesized();
        inference
            .unify_sub_type(
                Type::nullary_function_by_val(Type::never()),
                span,
                output,
                span,
            )
            .unwrap();
        inference
            .remaining_ty_constraints
            .push(PubTypeConstraint::new_have_trait(
                TraitId::new(ModuleId::new(0), LocalTraitId::new(0)),
                vec![input],
                vec![output],
                vec![],
                span,
            ));
        inference
            .unify_sub_type(Type::nullary_function_by_val(output), span, nested, span)
            .unwrap();
        assert!(
            !inference
                .select_lower_bounds(false, SelectionPhase::Inference)
                .unwrap()
        );
        assert_eq!(inference.substitute_in_type(output), output);
        assert_eq!(inference.substitute_in_type(nested), nested);
        // A later implementation determines the exact output, which is wider
        // than the current lower contributor. Saturation must still accept it.
        let actual = Type::nullary_function_by_val(int_type());
        inference
            .unify_same_type(output, span, actual, span)
            .unwrap();
        inference.propagate_type_bounds().unwrap();
        assert_eq!(inference.substitute_in_type(output), actual);
    }
}

impl UnifiedTypeInference {
    fn ordered_bounds(&self) -> Vec<TypeBound> {
        let mut relations: Vec<_> = self.bounds.relations().copied().collect();
        relations.extend(self.bottom_sources.iter().map(|(&upper, &span)| TypeBound {
            lower: Type::never(),
            lower_span: span,
            upper,
            upper_span: span,
        }));
        relations.sort_by_key(|bound| {
            (
                bound.lower_span.start(),
                bound.lower_span.end(),
                bound.upper_span.start(),
                bound.upper_span.end(),
            )
        });
        relations
    }
    pub(crate) fn set_publication_inputs(&mut self, inputs: impl IntoIterator<Item = Type>) {
        self.publication_inputs = inputs.into_iter().collect();
    }

    fn input_variables(&mut self) -> FxHashSet<TypeVar> {
        self.publication_inputs
            .clone()
            .into_iter()
            .flat_map(|ty| self.normalize_type(ty).inner_ty_vars())
            .collect()
    }

    /// Rebuild only after representatives or nested terms change. Structural
    /// decomposition adds semantic seeds, so normalization cannot lose them.
    pub(super) fn propagate_type_bounds(&mut self) -> Result<bool, InternalCompilationError> {
        let mut progress = false;
        loop {
            for (ty, span) in mem::take(&mut self.bottom_sources) {
                let ty = self.normalize_type(ty);
                if ty.data().as_variable().is_some() {
                    self.bottom_sources.entry(ty).or_insert(span);
                }
            }
            let mut bounds = mem::take(&mut self.bounds);
            let revision = (
                self.ty_unification_table.revision(),
                self.mut_unification_table.revision(),
            );
            match bounds.normalize_if_changed(revision, |ty| self.normalize_type(ty)) {
                Some(changed) => {
                    self.selection_stats.performed_bounds_normalizations += 1;
                    self.selection_stats.normalizations += usize::from(changed);
                    progress |= changed;
                }
                None => self.selection_stats.skipped_bounds_normalizations += 1,
            }
            self.bounds = bounds;
            self.selection_stats.scc_passes += 1;
            let equalities = self.bounds.equalities();
            if !equalities.is_empty() {
                for (left, right) in equalities {
                    self.ty_unification_table
                        .unify_var_var(left, right)
                        .expect("normalized variable cycle");
                }
                progress = true;
                continue;
            }
            let work = self.bounds.take_structural();
            if work.is_empty() {
                return Ok(progress);
            }
            progress = true;
            for bound in &work {
                let pair = (bound.lower, bound.upper);
                if self.checked_bounds.contains(&pair) {
                    continue;
                }
                self.selection_stats.structural_comparisons += 1;
                self.unify_sub_type(bound.lower, bound.lower_span, bound.upper, bound.upper_span)?;
                if bound.lower.is_constant() && bound.upper.is_constant() {
                    self.checked_bounds.insert(pair);
                }
            }
            self.bounds.discharge_checked(&work);
        }
    }

    fn pending_output_variables(&mut self, structural_outputs: bool) -> FxHashSet<TypeVar> {
        use crate::types::type_scheme::PubTypeConstraint::*;
        self.normalize_remaining_constraints();
        let mut outputs = FxHashSet::default();
        for constraint in self.remaining_ty_constraints.iter() {
            match constraint {
                HaveTrait {
                    input_tys,
                    output_tys,
                    ..
                } if !output_tys.is_empty() => {
                    let inputs: FxHashSet<_> =
                        input_tys.iter().flat_map(|ty| ty.inner_ty_vars()).collect();
                    outputs.extend(
                        output_tys
                            .iter()
                            .flat_map(|ty| ty.inner_ty_vars())
                            .filter(|var| !inputs.contains(var)),
                    );
                }
                TupleAtIndexIs { element_ty, .. } if structural_outputs => {
                    outputs.extend(element_ty.inner_ty_vars())
                }
                ProjectionSubscriptIs { subscript_ty, .. } if structural_outputs => {
                    outputs.extend(subscript_ty.ret.inner_ty_vars())
                }
                TypeHasVariant { payload_ty, .. } if structural_outputs => {
                    outputs.extend(payload_ty.inner_ty_vars())
                }
                _ => {}
            }
        }
        outputs
    }

    /// Pending outputs can constrain variables nested anywhere in a bound,
    /// including an upper constructor that cannot be decomposed yet. Preserve
    /// the whole connected component until its producer has been resolved.
    pub(super) fn pending_bound_variables(
        &mut self,
        structural_outputs: bool,
    ) -> FxHashSet<TypeVar> {
        self.pending_dependency_variables(structural_outputs, false)
    }

    pub(super) fn pending_default_variables(&mut self) -> FxHashSet<TypeVar> {
        self.pending_dependency_variables(false, true)
    }

    fn pending_dependency_variables(
        &mut self,
        structural_outputs: bool,
        defaulting: bool,
    ) -> FxHashSet<TypeVar> {
        let mut blocked = self.pending_output_variables(structural_outputs);
        if blocked.is_empty() {
            return blocked;
        }
        let mut neighbors = FxHashMap::<TypeVar, Vec<TypeVar>>::default();
        for bound in self.bounds.relations() {
            let vars: Vec<_> = bound
                .lower
                .inner_ty_vars()
                .into_iter()
                .chain(bound.upper.inner_ty_vars())
                .collect();
            if let Some(first) = vars.first() {
                for var in &vars[1..] {
                    neighbors.entry(*first).or_default().push(*var);
                    neighbors.entry(*var).or_default().push(*first);
                }
            }
        }
        // A pending aggregate can still determine its projected members. The
        // reverse edge is needed only for defaults: reconciling an aggregate's
        // existing shape may preserve unknown members, but defaulting its shape
        // would close a constructor before those members are known.
        use crate::types::type_scheme::PubTypeConstraint::*;
        for constraint in self.remaining_ty_constraints.iter() {
            let (subject, output) = match constraint {
                TupleAtIndexIs {
                    tuple_ty,
                    element_ty,
                    ..
                } => (*tuple_ty, *element_ty),
                ProjectionSubscriptIs { subscript_ty, .. } => {
                    (subscript_ty.receiver_ty(), subscript_ty.ret)
                }
                TypeHasVariant {
                    variant_ty,
                    payload_ty,
                    ..
                } => (*variant_ty, *payload_ty),
                _ => continue,
            };
            for input in subject.inner_ty_vars() {
                for output in output.inner_ty_vars() {
                    neighbors.entry(input).or_default().push(output);
                    if defaulting {
                        neighbors.entry(output).or_default().push(input);
                    }
                }
            }
        }
        let mut queue: Vec<_> = blocked.iter().copied().collect();
        while let Some(var) = queue.pop() {
            for next in neighbors.get(&var).into_iter().flatten() {
                if blocked.insert(*next) {
                    queue.push(*next);
                }
            }
        }
        blocked
    }

    /// Select only after all currently available structural consequences have
    /// been propagated. Symbolic predecessors remain dependencies, not bottom.
    pub(super) fn select_lower_bounds(
        &mut self,
        bottom: bool,
        phase: SelectionPhase,
    ) -> Result<bool, InternalCompilationError> {
        self.propagate_type_bounds()?;
        let relations = self.ordered_bounds();
        let mut contributors = FxHashMap::<TypeVar, Vec<TypeBound>>::default();
        let mut dependents = FxHashMap::<TypeVar, Vec<TypeVar>>::default();
        let mut structural_dependents = FxHashSet::default();
        for bound in relations {
            if bound.lower.data().as_variable().is_some()
                && bound.upper.data().as_variable().is_none()
            {
                structural_dependents.extend(bound.upper.inner_ty_vars());
            }
            if let Some(root) = bound.upper.data().as_variable().copied() {
                if let Some(predecessor) = bound.lower.data().as_variable().copied() {
                    dependents.entry(predecessor).or_default().push(root);
                } else {
                    contributors.entry(root).or_default().push(bound);
                }
            }
        }
        // Saturation above is still required even when no root can be selected:
        // it checks structural pairs and collapses variable cycles. Once it has
        // finished, an empty contributor map needs no dependency or input scan.
        if contributors.is_empty() {
            return Ok(false);
        }
        let mut roots: Vec<_> = contributors.keys().copied().collect();
        roots.sort_by_key(|var| var.name());
        let mut choices = Vec::new();
        let inputs = self.input_variables();
        let publishing = phase != SelectionPhase::Inference;
        let pending_outputs = if phase == SelectionPhase::Publication {
            FxHashSet::default()
        } else {
            self.pending_bound_variables(phase == SelectionPhase::Inference)
        };
        for root in roots {
            if pending_outputs.contains(&root)
                || (!publishing && structural_dependents.contains(&root))
            {
                continue;
            }
            let lowers = &contributors[&root];
            if lowers.iter().any(|b| {
                b.lower.contains_any_type_var(root)
                    || b.lower
                        .inner_ty_vars()
                        .iter()
                        .any(|var| pending_outputs.contains(var))
            }) {
                continue;
            }
            if (!bottom || inputs.contains(&root))
                && lowers.iter().all(|b| b.lower == Type::never())
            {
                continue;
            }
            if let Some(candidate) = self.reduce_bounds(lowers, BoundOperation::Join)? {
                choices.push((root, candidate, lowers[0]));
            }
        }
        // Concrete contributors already propagate through every variable edge.
        // Select a closed group together, but never guess the value of an
        // unconstrained predecessor. Removing one blocked predecessor removes
        // its dependent choices transitively, in linear graph time.
        let mut eligible: FxHashSet<_> = choices.iter().map(|(root, _, _)| *root).collect();
        let mut blocked: Vec<_> = dependents
            .keys()
            .filter(|root| !eligible.contains(root))
            .copied()
            .collect();
        while let Some(root) = blocked.pop() {
            for dependent in dependents.get(&root).into_iter().flatten() {
                if eligible.remove(dependent) {
                    blocked.push(*dependent);
                }
            }
        }
        choices.retain(|(root, _, _)| eligible.contains(root));
        let progress = !choices.is_empty();
        self.selection_stats.selections += choices.len();
        // Choices are computed from the same saturated graph, then validated
        // together. Processing order cannot change their contributors.
        for (root, mut candidate, source) in choices {
            if inputs.contains(&root) {
                candidate = self.generalize_bottom_leaves(candidate);
                candidate = self
                    .effects
                    .generalize_effectful_callable_type(candidate, true);
            }
            self.unify_same_type(
                Type::variable(root),
                source.upper_span,
                candidate,
                source.lower_span,
            )?;
        }
        self.propagate_type_bounds()?;
        Ok(progress)
    }

    /// At publication a parameter bounded below by a diverging callback can
    /// retain a universally quantified result. Memoize the finite signed graph;
    /// no unfolding or recursive single-contributor shape guess is involved.
    fn generalize_bottom_leaves(&mut self, ty: Type) -> Type {
        // Production callers normalize mutability before selection. Unknown
        // access is still invariant here; mutability is never generalized.
        let mut indices = FxHashMap::default();
        let mut states = vec![(ty, true)];
        indices.insert((ty, true), Type::new_local(0));
        let mut kinds = Vec::new();
        let mut cursor = 0;
        while cursor < states.len() {
            let (ty, positive) = states[cursor];
            let mut kind = ty.data().clone();
            let mut request = |ty: Type, positive: bool| {
                *indices.entry((ty, positive)).or_insert_with(|| {
                    let index = Type::new_local(states.len() as u32);
                    states.push((ty, positive));
                    index
                })
            };
            match &mut kind {
                TypeKind::Never if positive => kind = TypeKind::Variable(self.fresh_type_var()),
                TypeKind::Function(function) => {
                    for arg in &mut function.args {
                        if arg.mut_ty == MutType::constant() {
                            arg.ty = request(arg.ty, !positive);
                        }
                    }
                    function.ret = request(function.ret, positive);
                }
                // Nominal parameters and writable capabilities retain storage identity.
                TypeKind::Named(_) | TypeKind::Subscript(_) => {}
                _ => kind.for_each_inner_type_mut(|ty| *ty = request(*ty, positive)),
            }
            kinds.push(kind);
            cursor += 1;
        }
        store_types(&kinds)[0]
    }

    fn fresh_callable_effects(&mut self, ty: Type) -> Type {
        let mut indices = FxHashMap::from_iter([(ty, Type::new_local(0))]);
        let mut states = vec![ty];
        let mut kinds = Vec::new();
        let mut cursor = 0;
        while cursor < states.len() {
            let mut kind = states[cursor].data().clone();
            if !matches!(kind, TypeKind::Named(_)) {
                kind.for_each_inner_type_mut(|child| {
                    *child = *indices.entry(*child).or_insert_with(|| {
                        let index = Type::new_local(states.len() as u32);
                        states.push(*child);
                        index
                    });
                });
                match &mut kind {
                    TypeKind::Function(function) => {
                        function.effects = EffType::single_variable(self.fresh_effect_var())
                    }
                    TypeKind::Subscript(subscript) => {
                        for member in [&mut subscript.ref_member, &mut subscript.mut_member]
                            .into_iter()
                            .flatten()
                        {
                            member.effects = EffType::single_variable(self.fresh_effect_var());
                        }
                    }
                    _ => {}
                }
            }
            kinds.push(kind);
            cursor += 1;
        }
        store_types(&kinds)[0]
    }

    /// Equality publication concerns type structure, not independently tracked
    /// effect rows. When a component has a known common lower shape, give its
    /// roots separate effect rows and let the retained edges relate those rows.
    fn publish_component_shapes(
        &mut self,
        relations: &[TypeBound],
    ) -> Result<bool, InternalCompilationError> {
        let mut neighbors: FxHashMap<TypeVar, Vec<TypeVar>> = FxHashMap::default();
        for bound in relations {
            if let (Some(left), Some(right)) = (
                bound.lower.data().as_variable().copied(),
                bound.upper.data().as_variable().copied(),
            ) {
                neighbors.entry(left).or_default().push(right);
                neighbors.entry(right).or_default().push(left);
            }
        }
        let mut roots: Vec<_> = neighbors.keys().copied().collect();
        roots.sort_by_key(|var| var.name());
        let mut component_indices = FxHashMap::default();
        let mut components = Vec::new();
        for root in roots {
            if component_indices.contains_key(&root) {
                continue;
            }
            let index = components.len();
            component_indices.insert(root, index);
            let mut component = vec![root];
            let mut cursor = 0;
            while cursor < component.len() {
                for next in &neighbors[&component[cursor]] {
                    if let Entry::Vacant(entry) = component_indices.entry(*next) {
                        entry.insert(index);
                        component.push(*next);
                    }
                }
                cursor += 1;
            }
            components.push(component);
        }
        if components.is_empty() {
            return Ok(false);
        }
        let inputs = self.input_variables();
        // Partition once instead of rescanning all relations for each component.
        // Preserve relation order within each group: products and diagnostics
        // use the first contributor. Component/BFS order is unchanged as well.
        let mut lowers = vec![Vec::new(); components.len()];
        let never = Type::never();
        for bound in relations {
            if bound.lower == never || bound.lower.data().as_variable().is_some() {
                continue;
            }
            if let Some(upper) = bound.upper.data().as_variable()
                && let Some(&index) = component_indices.get(upper)
            {
                lowers[index].push(*bound);
            }
        }
        let mut progress = false;
        for (component, lower) in components.into_iter().zip(lowers) {
            if lower
                .iter()
                .any(|b| b.lower.contains_any_ty_vars(&component))
            {
                continue;
            }
            let Some(mut shape) = self.reduce_bounds(&lower, BoundOperation::Join)? else {
                continue;
            };
            if component.iter().any(|v| inputs.contains(v)) {
                shape = self.generalize_bottom_leaves(shape);
            }
            for var in component {
                let ty = self.fresh_callable_effects(shape);
                self.unify_same_type(
                    Type::variable(var),
                    lower[0].upper_span,
                    ty,
                    lower[0].lower_span,
                )?;
            }
            progress = true;
        }
        Ok(progress)
    }

    fn reduce_bounds(
        &mut self,
        bounds: &[TypeBound],
        operation: BoundOperation,
    ) -> Result<Option<Type>, InternalCompilationError> {
        if bounds.len() < 2
            || bounds.iter().all(|bound| match operation {
                BoundOperation::Join => bound.lower.is_constant(),
                BoundOperation::Meet => bound.upper.is_constant(),
            })
        {
            return self.reduce_bounds_inner(bounds, operation);
        }
        let snapshot = self.effects.snapshot();
        let result = self.reduce_bounds_inner(bounds, operation);
        if !matches!(result, Ok(Some(_))) {
            self.effects.rollback_to(snapshot);
        }
        result
    }

    fn reduce_bounds_inner(
        &mut self,
        bounds: &[TypeBound],
        operation: BoundOperation,
    ) -> Result<Option<Type>, InternalCompilationError> {
        let endpoint = |b: &TypeBound| match operation {
            BoundOperation::Join => b.lower,
            BoundOperation::Meet => b.upper,
        };
        let Some(first) = bounds.first() else {
            return Ok(None);
        };
        let mut candidate = endpoint(first);
        for bound in &bounds[1..] {
            let other = endpoint(bound);
            self.selection_stats.products += 1;
            let result = if candidate.is_constant() && other.is_constant() {
                ground_bound(candidate, other, operation)
            } else {
                let mut effect_meet = |left: &EffType, right: &EffType| {
                    let result = EffType::single_variable(self.fresh_effect_var());
                    let span = Location::new_synthesized();
                    self.add_effect_dep(&result, span, left, span)
                        .expect("fresh effect lower bound");
                    self.add_effect_dep(&result, span, right, span)
                        .expect("fresh effect lower bound");
                    result
                };
                symbolic_bound(candidate, other, operation, Some(&mut effect_meet))
            };
            match result {
                Ok(Some(ty)) => candidate = ty,
                Err(_) => return Ok(None),
                Ok(None) => {
                    if let (TypeKind::Named(current), TypeKind::Named(expected)) =
                        (&*other.data(), &*candidate.data())
                    {
                        if current.def != expected.def {
                            return Err(internal_compilation_error!(NamedTypeMismatch {
                                current_decl: current.def,
                                current_span: bound.lower_span,
                                expected_decl: expected.def,
                                expected_span: first.lower_span,
                            }));
                        }
                    }
                    return Err(internal_compilation_error!(TypeMismatch {
                        current_ty: other,
                        current_span: bound.lower_span,
                        expected_ty: candidate,
                        expected_span: first.lower_span,
                        sub_or_same: SubOrSameType::SubType,
                    }));
                }
            }
        }
        Ok(Some(candidate))
    }

    pub(super) fn log_bounds_stats(&self) {
        log::trace!(
            "type bounds: {} variables, {} retained relations, {:?}",
            self.ty_unification_table.len(),
            self.bounds.relations().count(),
            self.selection_stats
        );
    }

    /// Reconcile structure before defaulting without fixing pending outputs.
    pub(crate) fn prepare_type_bounds(&mut self) -> Result<(), InternalCompilationError> {
        self.solve_publication_bounds(false)
    }

    /// No subtype constraints are exported in schemes. Residual variable edges
    /// are strengthened simultaneously to equality, then all original seeds
    /// are checked again under that substitution. Call only after eligible
    /// defaults have reached a fixed point.
    pub(crate) fn publish_type_bounds(&mut self) -> Result<(), InternalCompilationError> {
        self.solve_publication_bounds(true)
    }

    fn solve_publication_bounds(
        &mut self,
        final_publication: bool,
    ) -> Result<(), InternalCompilationError> {
        let iteration_limit =
            100 + 16 * (self.ty_unification_table.len() + self.bounds.relations().count());
        self.solve_publication_bounds_with_limit(final_publication, iteration_limit)
    }

    fn solve_publication_bounds_with_limit(
        &mut self,
        final_publication: bool,
        iteration_limit: usize,
    ) -> Result<(), InternalCompilationError> {
        let mut iterations = 0;
        loop {
            // This is a robustness budget, not a proof of convergence. Keep it
            // active in release builds, including compilers hosted in Wasm.
            if iterations == iteration_limit {
                return Err(internal_compilation_error!(Internal {
                    span: self
                        .bounds
                        .relations()
                        .next()
                        .map_or(Location::new_synthesized(), |bound| bound.lower_span),
                    error: format!(
                        "type-bound publication failed to converge after {iteration_limit} rounds"
                    ),
                }));
            }
            iterations += 1;
            self.propagate_type_bounds()?;
            let phase = if final_publication {
                SelectionPhase::Publication
            } else {
                SelectionPhase::Preparation
            };
            if self.select_lower_bounds(false, phase)? {
                continue;
            }
            let blocked = if final_publication {
                FxHashSet::default()
            } else {
                // Structural constraints describe the shape currently being
                // reconciled; they are not outputs awaiting an implementation.
                self.pending_bound_variables(false)
            };
            let relations: Vec<_> = self
                .ordered_bounds()
                .into_iter()
                .filter(|bound| {
                    !bound
                        .lower
                        .inner_ty_vars()
                        .iter()
                        .chain(bound.upper.inner_ty_vars().iter())
                        .any(|var| blocked.contains(var))
                })
                .collect();
            if self.publish_component_shapes(&relations)? {
                continue;
            }
            let mut merged = false;
            for bound in &relations {
                let left = bound.lower.data().as_variable().copied();
                let right = bound.upper.data().as_variable().copied();
                if let (Some(left), Some(right)) = (left, right) {
                    self.ty_unification_table
                        .unify_var_var(left, right)
                        .expect("normalized residual variables");
                    merged = true;
                }
            }
            if merged {
                continue;
            }
            // When a symbolic product is still undecidable at publication,
            // retain expressible relationships by strengthening its contributor
            // group together. This is deliberately not used by propagation.
            // Index once: scanning every relation for every root was quadratic
            // and repeatedly interned the same Type::variable inside filters.
            let mut lowers = FxHashMap::<TypeVar, Vec<TypeBound>>::default();
            let mut uppers = FxHashMap::<TypeVar, Vec<TypeBound>>::default();
            for bound in &relations {
                if let Some(root) = bound.upper.data().as_variable().copied() {
                    if bound.lower != Type::never() {
                        lowers.entry(root).or_default().push(*bound);
                    }
                }
                if let Some(root) = bound.lower.data().as_variable().copied() {
                    uppers.entry(root).or_default().push(*bound);
                }
            }
            let mut lower_roots: Vec<_> = lowers.keys().copied().collect();
            lower_roots.sort_by_key(|v| v.name());
            let mut strengthened = false;
            for root in lower_roots {
                let lower = &lowers[&root];
                if lower
                    .iter()
                    .any(|bound| bound.lower.contains_any_type_var(root))
                {
                    if let Some(candidate) = self.reduce_bounds(lower, BoundOperation::Join)? {
                        self.unify_same_type(
                            Type::variable(root),
                            lower[0].upper_span,
                            candidate,
                            lower[0].lower_span,
                        )?;
                        strengthened = true;
                    }
                    continue;
                }
                if lower.len() < 2 {
                    continue;
                }
                for bound in &lower[1..] {
                    let shape = self.fresh_callable_effects(lower[0].lower);
                    self.unify_same_type_with_sub_effects(
                        bound.lower,
                        bound.lower_span,
                        shape,
                        lower[0].lower_span,
                    )?;
                }
                strengthened |= lower
                    .iter()
                    .any(|b| self.normalize_type(b.lower) != b.lower);
            }
            if strengthened {
                continue;
            }
            let mut roots: Vec<_> = uppers.keys().copied().collect();
            roots.sort_by_key(|v| v.name());
            let mut progress = false;
            for root in roots {
                let upper = &uppers[&root];
                if let Some(candidate) = self.reduce_bounds(upper, BoundOperation::Meet)? {
                    self.unify_same_type(
                        Type::variable(root),
                        upper[0].lower_span,
                        candidate,
                        upper[0].upper_span,
                    )?;
                    progress = true;
                } else if upper.len() > 1 {
                    // Unknown leaves can prevent a shape-stable product. At
                    // publication, strengthen this entire group to equal type
                    // structure, then retry; no subtype bound escapes a scheme.
                    for bound in &upper[1..] {
                        let shape = self.fresh_callable_effects(upper[0].upper);
                        self.unify_same_type_with_sub_effects(
                            bound.upper,
                            bound.upper_span,
                            shape,
                            upper[0].upper_span,
                        )?;
                    }
                    let normalized: Vec<_> = upper
                        .iter()
                        .map(|bound| TypeBound {
                            upper: self.normalize_type(bound.upper),
                            ..*bound
                        })
                        .collect();
                    if let Some(candidate) =
                        self.reduce_bounds(&normalized, BoundOperation::Meet)?
                    {
                        self.unify_same_type(
                            Type::variable(root),
                            upper[0].lower_span,
                            candidate,
                            upper[0].upper_span,
                        )?;
                        progress = true;
                    }
                }
            }
            if !progress {
                break;
            }
        }
        self.propagate_type_bounds()?;
        self.normalize_remaining_constraints();
        if !final_publication {
            return Ok(());
        }
        // Never <: a is valid for every instantiation. All other residual
        // structural bounds must be discharged before a scheme can escape.
        let remaining: Vec<_> = self.bounds.relations().copied().collect();
        for bound in remaining {
            if bound.lower == Type::never() {
                continue;
            }
            if bound.lower.data().is_variable() || bound.upper.data().is_variable() {
                return Err(internal_compilation_error!(TypeMismatch {
                    current_ty: bound.lower,
                    current_span: bound.lower_span,
                    expected_ty: bound.upper,
                    expected_span: bound.upper_span,
                    sub_or_same: SubOrSameType::SubType,
                }));
            }
        }
        self.validate_type_coverage()
    }
}
