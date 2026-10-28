// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{borrow::Borrow, mem};

use ena::unify::{InPlace, InPlaceUnificationTable, NoError, Snapshot, UnifyValue};
use ustr::Ustr;

use super::{constraints::EffectConstraint, tables::Revision};
use crate::{
    FxHashMap, FxHashSet,
    compiler::error::InternalCompilationError,
    internal_compilation_error,
    module::TraitId,
    parser::location::Location,
    types::{
        effects::{EffType, Effect, EffectVar, EffectVarKey},
        r#type::{FnType, SubscriptMemberType, SubscriptType, Type, TypeKind},
    },
};

/// Diagnostic origin for internal effect dependency constraints.
#[derive(Debug, Clone)]
pub(crate) enum EffectConstraintOrigin {
    Inference,
    TraitMethodImpl {
        trait_id: TraitId,
        method_name: Ustr,
        impl_span: Location,
    },
}

impl EffectConstraintOrigin {
    fn is_trait_method_impl(&self) -> bool {
        matches!(self, Self::TraitMethodImpl { .. })
    }
}

/// An effect inclusion `lower ⊆ upper`, as stated.
#[derive(Debug, Clone)]
struct EffectInclusion {
    lower: EffType,
    lower_span: Location,
    upper: EffType,
    upper_span: Location,
    origin: EffectConstraintOrigin,
}

/// The constraint that brought an atom into a least solution, or a ceiling.
#[derive(Debug, Clone)]
struct BoundSource {
    span: Location,
    origin: EffectConstraintOrigin,
}

#[derive(Debug, Clone)]
struct Ceiling {
    row: EffType,
    source: BoundSource,
}

/// What the solver knows about a class of equal effect variables.
///
/// Atoms are primitive effects and rigid variables: declared effect variables, which stand for
/// any row and are never solved. All bounds are kept exactly, as rows of atoms: `lower` is the
/// least solution, `ceiling` the intersection of the rows the class must fit in, and
/// `successors` the masked inclusions `self ⊆ (mask, var)`; `predecessors` mirrors them for
/// replay. A class equal to a row with several variables is an alias of that row: its own bounds
/// were replayed on the row.
#[derive(Debug, Clone, Default)]
pub struct EffectClass {
    rigid: bool,
    /// The smallest variable of the class, which names it.
    smallest: Option<EffectVar>,
    lower: EffType,
    lower_sources: Vec<(Effect, BoundSource)>,
    ceiling: Option<Ceiling>,
    successors: Vec<(EffectVar, EffType)>,
    predecessors: Vec<(EffectVar, EffType)>,
    alias: Option<EffType>,
}

impl EffectClass {
    fn with_lower(effect: Effect, source: BoundSource) -> Self {
        Self {
            lower: EffType::single(effect),
            lower_sources: vec![(effect, source)],
            ..Self::default()
        }
    }

    fn lower_source(&self, effect: Effect) -> BoundSource {
        self.lower_sources
            .iter()
            .find(|(atom, _)| *atom == effect)
            .map(|(_, source)| source.clone())
            .expect("every atom of a least solution has a source")
    }
}

/// Classes merge by joining their bounds; the solver checks the result.
impl UnifyValue for EffectClass {
    type Error = NoError;

    fn unify_values(a: &Self, b: &Self) -> Result<Self, Self::Error> {
        let mut lower_sources = a.lower_sources.clone();
        for (effect, source) in &b.lower_sources {
            if !a.lower.contains(*effect) {
                lower_sources.push((*effect, source.clone()));
            }
        }
        let ceiling = match (&a.ceiling, &b.ceiling) {
            (None, ceiling) | (ceiling, None) => ceiling.clone(),
            (Some(a), Some(b)) => {
                let row = a.row.intersection(&b.row);
                let source = if row == a.row { &a.source } else { &b.source };
                Some(Ceiling {
                    row,
                    source: source.clone(),
                })
            }
        };
        let mut successors = a.successors.clone();
        extend_edges(&mut successors, &b.successors);
        let mut predecessors = a.predecessors.clone();
        extend_edges(&mut predecessors, &b.predecessors);
        let smallest = match (a.smallest, b.smallest) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (smallest, None) | (None, smallest) => smallest,
        };
        Ok(Self {
            rigid: a.rigid || b.rigid,
            smallest,
            lower: a.lower.union(&b.lower),
            lower_sources,
            ceiling,
            successors,
            predecessors,
            alias: a.alias.clone().or_else(|| b.alias.clone()),
        })
    }
}

fn extend_edges(edges: &mut Vec<(EffectVar, EffType)>, new: &[(EffectVar, EffType)]) {
    for edge in new {
        if !edges.contains(edge) {
            edges.push(edge.clone());
        }
    }
}

pub(crate) struct EffectSolverSnapshot {
    table: Snapshot<InPlace<EffectVarKey>>,
    deferred_inclusions: Vec<EffectInclusion>,
    publishing: bool,
}

/// Solver state for inferred effect variables and effect relations.
///
/// Every inclusion is split per solvable variable into lower bounds, ceilings and masked
/// inclusions over atoms (primitive effects and rigid variables), all kept exactly, so the least
/// solution and its checks do not depend on the order in which constraints arrive. Inclusions
/// into rows with several solvable variables are disjunctions: they are deferred, and
/// materialized conservatively when dependencies are expanded. Equalities unify rows.
///
/// Readers see the solution through substitution. While constraints are added, a variable maps
/// to its least atoms and itself, or to its row once its bounds determine it. Once effect
/// dependencies are finalized, a variable bounded by a ceiling maps to the largest row its
/// ceilings allow, and the other variables are merged along their inclusions, each mapping to
/// its least atoms and its group's representative: the group's rigid variable if its least
/// solution holds exactly one, otherwise its smallest variable.
#[derive(Default, Debug)]
pub(crate) struct EffectSolver {
    table: InPlaceUnificationTable<EffectVarKey>,
    constraints: Vec<EffectConstraint>,
    deferred_inclusions: Vec<EffectInclusion>,
    publishing: bool,
    publication: Option<PublicationView>,
    substitution_revision: Revision,
    /// The declared names of rigid variables, for diagnostics.
    rigid_names: FxHashMap<EffectVar, Ustr>,
}

/// The substitution of class roots once effect dependencies are finalized.
#[derive(Debug)]
struct PublicationView {
    roots: FxHashMap<EffectVar, EffType>,
    representatives: FxHashMap<EffectVar, EffectVar>,
}

impl EffectSolver {
    // Changes to existing classes or the substitution view invalidate both caches.
    // Fresh independent roots only require rebuilding the publication view.
    // The revision is monotonic across rollback; it is not solver progress.
    fn invalidate_publication(&mut self) {
        self.substitution_revision.advance();
        self.publication = None;
    }

    pub(super) fn substitution_revision(&self) -> Revision {
        self.substitution_revision
    }

    pub(crate) fn fresh_var(&mut self) -> EffectVar {
        // The publication view needs an entry for the new root, but allocating
        // an independent variable cannot change substitution of existing terms.
        self.publication = None;
        let var = self.table.new_key(EffectClass::default());
        self.table.union_value(
            var,
            EffectClass {
                smallest: Some(var),
                ..EffectClass::default()
            },
        );
        var
    }

    /// A declared effect variable: an atom, which stands for any row and is never solved.
    pub(crate) fn fresh_rigid_var(&mut self, name: Option<Ustr>) -> EffectVar {
        self.publication = None;
        let var = self.table.new_key(EffectClass {
            rigid: true,
            ..EffectClass::default()
        });
        if let Some(name) = name {
            self.rigid_names.insert(var, name);
        }
        var
    }

    fn ensure_var(&mut self, var: EffectVar) {
        while self.table.len() <= var.name() as usize {
            self.fresh_var();
        }
    }

    pub(crate) fn fresh_var_ty(&mut self) -> EffType {
        EffType::single_variable(self.fresh_var())
    }

    pub(crate) fn snapshot(&mut self) -> EffectSolverSnapshot {
        EffectSolverSnapshot {
            table: self.table.snapshot(),
            deferred_inclusions: self.deferred_inclusions.clone(),
            publishing: self.publishing,
        }
    }

    pub(crate) fn rollback_to(&mut self, snapshot: EffectSolverSnapshot) {
        self.table.rollback_to(snapshot.table);
        self.deferred_inclusions = snapshot.deferred_inclusions;
        self.publishing = snapshot.publishing;
        self.invalidate_publication();
    }

    pub(super) fn add_same_constraint(
        &mut self,
        current: &EffType,
        current_span: Location,
        expected: &EffType,
        expected_span: Location,
    ) {
        if current == expected {
            return;
        }
        self.constraints.push(EffectConstraint::SameEffect {
            current: current.clone(),
            current_span,
            expected: expected.clone(),
            expected_span,
        });
    }

    pub(super) fn drain_constraints(&mut self) -> Vec<EffectConstraint> {
        mem::take(&mut self.constraints)
    }

    /// Return a row containing all of `deps`: a fresh variable bounded below by them, unless
    /// the union is already a row of primitives or a lone variable.
    pub(super) fn make_dependent_effect<T: Borrow<EffType> + Clone>(
        &mut self,
        deps: impl AsRef<[T]>,
    ) -> EffType {
        let deps = deps.as_ref();

        if deps.is_empty() {
            return EffType::empty();
        } else if deps.len() == 1 {
            return deps[0].borrow().clone();
        }

        let mut effects = deps[0].borrow().clone();
        for effect in &deps[1..] {
            effects.extend(effect.borrow());
        }

        if !effects.has_variables() || effects.to_single_variable().is_some() {
            return effects;
        }

        let effect_var = self.fresh_var_ty();
        let span = Location::new_synthesized();
        self.add_effect_inclusion(
            effects,
            span,
            effect_var.clone(),
            span,
            EffectConstraintOrigin::Inference,
        )
        .expect("a fresh variable accepts any lower bound");
        effect_var
    }

    /// Make the two effects equal and return the resulting row.
    pub(super) fn unify_effects(
        &mut self,
        eff1: &EffType,
        eff2: &EffType,
        span: Location,
    ) -> Result<EffType, InternalCompilationError> {
        match (eff1.to_single_variable(), eff2.to_single_variable()) {
            (None, None) => Ok(eff1.union(eff2)),
            (var1, _) => {
                self.unify_same_effect(eff1.clone(), span, eff2.clone(), span)?;
                Ok(if var1.is_some() && eff2.to_single_variable().is_none() {
                    eff2.clone()
                } else {
                    eff1.clone()
                })
            }
        }
    }

    /// Give the top-level effects of a first-class callable-like type a fresh variable, bounded
    /// below by them if the type receives values (`widen`), above otherwise.
    ///
    /// Binding a type variable to a callable at a join point must not make the joined values
    /// share one effect variable: each relates to the fresh variable by inclusion.
    pub(crate) fn generalize_effectful_callable_type(&mut self, ty: Type, widen: bool) -> Type {
        use TypeKind::*;
        let ty_data = ty.data();
        match &*ty_data {
            Function(fn_ty) => {
                let fn_ty = fn_ty.clone();
                drop(ty_data);
                let effects = self.generalize_effect_type(&fn_ty.effects, widen);
                Type::function_type(FnType::new(fn_ty.args.clone(), fn_ty.ret, effects))
            }
            Subscript(subscript) => {
                let subscript = subscript.clone();
                drop(ty_data);
                let ref_member = subscript
                    .ref_member
                    .as_ref()
                    .map(|member| self.generalize_subscript_member(member, widen));
                let mut_member = subscript
                    .mut_member
                    .as_ref()
                    .map(|member| self.generalize_subscript_member(member, widen));
                Type::subscript_type(SubscriptType::new(
                    subscript.args.clone(),
                    subscript.ret,
                    ref_member,
                    mut_member,
                ))
            }
            _ => {
                drop(ty_data);
                ty
            }
        }
    }

    fn generalize_subscript_member(
        &mut self,
        member: &SubscriptMemberType,
        widen: bool,
    ) -> SubscriptMemberType {
        let effects = self.generalize_effect_type(&member.effects, widen);
        SubscriptMemberType::new(effects, member.result_convention)
    }

    fn generalize_effect_type(&mut self, effects: &EffType, widen: bool) -> EffType {
        let fresh = self.fresh_var_ty();
        let span = Location::new_synthesized();
        let (lower, upper) = if widen {
            (effects.clone(), fresh.clone())
        } else {
            (fresh.clone(), effects.clone())
        };
        self.add_effect_inclusion(lower, span, upper, span, EffectConstraintOrigin::Inference)
            .expect("a fresh variable accepts any bound");
        fresh
    }

    /// Make current and target the same effect type.
    ///
    /// Equality unifies rows where that is exact, so that equal rows become the same row: two
    /// lone variables are merged, and a lone variable is aliased to the other row. Other
    /// equalities, such as `(read, a) = (read, b)`, which does not imply `a = b`, are kept as two
    /// inclusions.
    pub(crate) fn unify_same_effect(
        &mut self,
        current: EffType,
        current_span: Location,
        target: EffType,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.ensure_effect_vars(&current);
        self.ensure_effect_vars(&target);
        log::trace!("effect equality: {current} = {target}");
        let current_row = self.resolve(&current);
        let target_row = self.resolve(&target);
        let (current_atoms, current_vars) = self.split_atoms(&current_row);
        let (target_atoms, target_vars) = self.split_atoms(&target_row);
        match (current_vars.as_slice(), target_vars.as_slice()) {
            ([current_var], [target_var]) if current_var != target_var => {
                if current_atoms.is_empty() && target_atoms.is_empty() {
                    return self.union_vars(*current_var, *target_var, current_span);
                } else if current_atoms.is_empty() {
                    return self.alias_var(*current_var, target_row, target_span);
                } else if target_atoms.is_empty() {
                    return self.alias_var(*target_var, current_row, current_span);
                }
            }
            ([var], [_, _, ..]) if current_atoms.is_empty() => {
                return self.alias_var(*var, target_row, target_span);
            }
            ([_, _, ..], [var]) if target_atoms.is_empty() => {
                return self.alias_var(*var, current_row, current_span);
            }
            _ => {}
        }
        self.add_effect_inclusion(
            current.clone(),
            current_span,
            target.clone(),
            target_span,
            EffectConstraintOrigin::Inference,
        )?;
        self.add_effect_inclusion(
            target,
            target_span,
            current,
            current_span,
            EffectConstraintOrigin::Inference,
        )
    }

    pub(crate) fn add_effect_dep(
        &mut self,
        current: &EffType,
        current_span: Location,
        target: &EffType,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.add_effect_dep_with_origin(
            current,
            current_span,
            target,
            target_span,
            EffectConstraintOrigin::Inference,
        )
    }

    pub(crate) fn add_effect_dep_with_origin(
        &mut self,
        current: &EffType,
        current_span: Location,
        target: &EffType,
        target_span: Location,
        origin: EffectConstraintOrigin,
    ) -> Result<(), InternalCompilationError> {
        self.add_effect_inclusion(
            current.clone(),
            current_span,
            target.clone(),
            target_span,
            origin,
        )
    }

    /// Materialize the deferred inclusions that do not hold yet.
    pub(super) fn expand_pending_dependencies(&mut self) -> Result<(), InternalCompilationError> {
        for inclusion in mem::take(&mut self.deferred_inclusions) {
            self.materialize_inclusion(inclusion)?;
        }
        Ok(())
    }

    /// Materialize the deferred inclusions and switch readers to the publication view.
    pub(super) fn finalize(&mut self) -> Result<(), InternalCompilationError> {
        self.expand_pending_dependencies()?;
        self.publishing = true;
        self.invalidate_publication();
        self.validate_publication()
    }

    /// Check that every retained constraint holds once each variable is replaced by its
    /// published row, for all values of the remaining variables: the publication approximates
    /// the exact solution and must stay sound.
    fn validate_publication(&mut self) -> Result<(), InternalCompilationError> {
        let mut visited = FxHashSet::default();
        for index in 0..self.table.len() {
            let root = self.table.find(EffectVar::new(index as u32));
            if !visited.insert(root) {
                continue;
            }
            let class = self.class(root);
            if class.rigid || class.alias.is_some() {
                continue;
            }
            let row = self.substitute_var(root);
            let lower_span = class
                .lower_sources
                .first()
                .map_or_else(Location::new_synthesized, |(_, source)| source.span);
            let missing = class.lower.difference(&row);
            if !missing.is_empty() {
                return Err(invalid_effect_dependency(
                    missing,
                    lower_span,
                    row,
                    Location::new_synthesized(),
                    EffectConstraintOrigin::Inference,
                ));
            }
            if let Some(ceiling) = &class.ceiling {
                let excess = row.difference(&ceiling.row);
                if !excess.is_empty() {
                    return Err(invalid_effect_dependency(
                        excess,
                        lower_span,
                        ceiling.row.clone(),
                        ceiling.source.span,
                        ceiling.source.origin.clone(),
                    ));
                }
            }
            for (target, mask) in class.successors {
                let upper = mask.union(&self.substitute_var(target));
                let excess = row.difference(&upper);
                if !excess.is_empty() {
                    return Err(invalid_effect_dependency(
                        excess,
                        lower_span,
                        upper,
                        Location::new_synthesized(),
                        EffectConstraintOrigin::Inference,
                    ));
                }
            }
        }
        Ok(())
    }

    /// The number of variables, which is the name of the next fresh one.
    pub(super) fn var_count(&self) -> u32 {
        self.table.len() as u32
    }

    /// Fix every solvable variable outside the classes of `observable` at its least solution,
    /// which is unobservable for them.
    pub(super) fn minimize_except(
        &mut self,
        observable: &FxHashSet<EffectVar>,
    ) -> Result<(), InternalCompilationError> {
        self.expand_pending_dependencies()?;
        let observable_roots = observable
            .iter()
            .map(|var| {
                self.ensure_var(*var);
                self.table.find(*var)
            })
            .collect::<FxHashSet<_>>();
        // A variable's least solution is its least atoms only when everything flowing into it is
        // fixed too; one reached by a variable left solvable keeps that variable in its solution.
        let mut fixed = FxHashSet::default();
        for index in 0..self.table.len() {
            let root = self.table.find(EffectVar::new(index as u32));
            let class = self.class(root);
            if !observable_roots.contains(&root) && !class.rigid && class.alias.is_none() {
                fixed.insert(root);
            }
        }
        loop {
            let reached = fixed
                .iter()
                .copied()
                .filter(|&root| {
                    self.class(root)
                        .predecessors
                        .clone()
                        .into_iter()
                        .any(|(source, _)| !fixed.contains(&self.table.find(source)))
                })
                .collect::<Vec<_>>();
            if reached.is_empty() {
                break;
            }
            for root in reached {
                fixed.remove(&root);
            }
        }
        let mut fixed = fixed.into_iter().collect::<Vec<_>>();
        fixed.sort_by_key(|var| var.name());
        for root in fixed {
            let class = self.class(root);
            let source = BoundSource {
                span: Location::new_synthesized(),
                origin: EffectConstraintOrigin::Inference,
            };
            let ceiling = Ceiling {
                row: class.lower.clone(),
                source,
            };
            self.add_ceiling(root, ceiling, &EffectConstraintOrigin::Inference)?;
        }
        Ok(())
    }

    /// The names of two declared variables that `row` combines, if any.
    pub(super) fn combined_declared_variables(&mut self, row: &EffType) -> Option<(Ustr, Ustr)> {
        let mut declared = Vec::new();
        for var in row.inner_vars() {
            self.ensure_var(var);
            let root = self.table.find(var);
            if self.class(root).rigid && !declared.contains(&var) {
                declared.push(var);
            }
        }
        let [first, second, ..] = declared.as_slice() else {
            return None;
        };
        let name = |var: &EffectVar| {
            self.rigid_names
                .get(var)
                .copied()
                .unwrap_or_else(|| ustr::ustr(&var.to_string()))
        };
        Some((name(first), name(second)))
    }

    pub(super) fn is_finalized(&self) -> bool {
        self.publishing
    }

    pub(super) fn set_finalized(&mut self, finalized: bool) {
        if self.publishing != finalized {
            self.publishing = finalized;
            self.invalidate_publication();
        }
    }

    fn ensure_effect_vars(&mut self, eff: &EffType) {
        for var in eff.inner_vars() {
            self.ensure_var(var);
        }
    }

    fn is_rigid(&mut self, var: EffectVar) -> bool {
        self.ensure_var(var);
        let root = self.table.find(var);
        self.class(root).rigid
    }

    /// Split a resolved row into its atoms and its solvable variables.
    fn split_atoms(&mut self, row: &EffType) -> (EffType, Vec<EffectVar>) {
        let mut atoms = row.primitive_effects();
        let mut vars = Vec::new();
        for var in row.inner_vars() {
            if self.is_rigid(var) {
                atoms.insert(Effect::Variable(var));
            } else {
                vars.push(var);
            }
        }
        (atoms, vars)
    }

    fn class(&mut self, root: EffectVar) -> EffectClass {
        self.table.probe_value(root)
    }

    fn update_class(&mut self, root: EffectVar, delta: EffectClass) {
        self.invalidate_publication();
        self.table.union_value(root, delta);
    }

    /// `eff` with its variables replaced by their class roots, aliases by their rows, and
    /// variables whose bounds meet by their rows.
    fn resolve(&mut self, eff: &EffType) -> EffType {
        let mut resolved = eff.primitive_effects();
        for var in eff.inner_vars() {
            self.ensure_var(var);
            let root = self.table.find(var);
            let class = self.class(root);
            match class.alias {
                Some(alias) => resolved.extend(&self.resolve(&alias)),
                None if class
                    .ceiling
                    .as_ref()
                    .is_some_and(|ceiling| ceiling.row == class.lower) =>
                {
                    resolved.extend(&class.lower)
                }
                None => resolved.insert(Effect::Variable(root)),
            }
        }
        resolved
    }

    fn add_effect_inclusion(
        &mut self,
        lower: EffType,
        lower_span: Location,
        upper: EffType,
        upper_span: Location,
        origin: EffectConstraintOrigin,
    ) -> Result<(), InternalCompilationError> {
        log::trace!("effect inclusion: {lower} ⊆ {upper}");
        let inclusion = EffectInclusion {
            lower,
            lower_span,
            upper,
            upper_span,
            origin,
        };
        if !self.try_add_inclusion(&inclusion)? {
            self.deferred_inclusions.push(inclusion);
        }
        Ok(())
    }

    /// Add `inclusion` as lower bounds, ceilings and masked inclusions; return false if it is
    /// a disjunction that does not hold yet.
    fn try_add_inclusion(
        &mut self,
        inclusion: &EffectInclusion,
    ) -> Result<bool, InternalCompilationError> {
        let lower = self.resolve(&inclusion.lower);
        let upper = self.resolve(&inclusion.upper);
        let (lower_atoms, lower_vars) = self.split_atoms(&lower);
        let (upper_atoms, upper_vars) = self.split_atoms(&upper);
        let extra = lower_atoms.difference(&upper_atoms);
        let lower_vars: Vec<_> = lower_vars
            .into_iter()
            .filter(|var| !upper_vars.contains(var))
            .collect();
        let source = BoundSource {
            span: inclusion.lower_span,
            origin: inclusion.origin.clone(),
        };
        match upper_vars.as_slice() {
            [] => {
                if !extra.is_empty() {
                    return Err(invalid_effect_dependency(
                        lower_atoms,
                        inclusion.lower_span,
                        upper,
                        inclusion.upper_span,
                        inclusion.origin.clone(),
                    ));
                }
                let ceiling = Ceiling {
                    row: upper_atoms,
                    source: BoundSource {
                        span: inclusion.upper_span,
                        origin: inclusion.origin.clone(),
                    },
                };
                for var in lower_vars {
                    self.add_ceiling(var, ceiling.clone(), &inclusion.origin)?;
                }
                Ok(true)
            }
            [upper_var] => {
                self.add_lower(*upper_var, &extra, &source, &inclusion.origin)?;
                for var in lower_vars {
                    self.add_edge(var, *upper_var, &upper_atoms, &inclusion.origin)?;
                }
                Ok(true)
            }
            _ => Ok(self.disjunction_holds(&extra, &lower_vars, &upper_atoms, &upper_vars)),
        }
    }

    /// Whether `extra ⊆ (upper_atoms, upper_vars)` and each of `lower_vars` too already hold.
    fn disjunction_holds(
        &mut self,
        extra: &EffType,
        lower_vars: &[EffectVar],
        upper_atoms: &EffType,
        upper_vars: &[EffectVar],
    ) -> bool {
        let upper_lower = self.lower_union(upper_vars);
        if !extra.difference(&upper_lower).is_empty() {
            return false;
        }
        lower_vars
            .iter()
            .all(|var| self.has_edge_into(*var, upper_atoms, upper_vars))
    }

    fn lower_union(&mut self, vars: &[EffectVar]) -> EffType {
        let mut lower = EffType::empty();
        for var in vars {
            let root = self.table.find(*var);
            lower.extend(&self.class(root).lower);
        }
        lower
    }

    fn has_edge_into(
        &mut self,
        var: EffectVar,
        upper_atoms: &EffType,
        upper_vars: &[EffectVar],
    ) -> bool {
        let root = self.table.find(var);
        let successors = self.class(root).successors;
        successors.into_iter().any(|(target, mask)| {
            let target = self.table.find(target);
            upper_vars.contains(&target) && mask.difference(upper_atoms).is_empty()
        })
    }

    /// Satisfy a disjunction that does not hold by a sufficient Horn system: every missing
    /// atom and every lower variable flows into each upper variable.
    fn materialize_inclusion(
        &mut self,
        inclusion: EffectInclusion,
    ) -> Result<(), InternalCompilationError> {
        if self.try_add_inclusion(&inclusion)? {
            return Ok(());
        }
        let lower = self.resolve(&inclusion.lower);
        let upper = self.resolve(&inclusion.upper);
        let (lower_atoms, lower_vars) = self.split_atoms(&lower);
        let (upper_atoms, upper_vars) = self.split_atoms(&upper);
        let missing = lower_atoms
            .difference(&upper_atoms)
            .difference(&self.lower_union(&upper_vars));
        let source = BoundSource {
            span: inclusion.lower_span,
            origin: inclusion.origin.clone(),
        };
        for var in &upper_vars {
            self.add_lower(*var, &missing, &source, &inclusion.origin)?;
        }
        for var in lower_vars {
            if upper_vars.contains(&var) || self.has_edge_into(var, &upper_atoms, &upper_vars) {
                continue;
            }
            for upper_var in &upper_vars {
                self.add_edge(var, *upper_var, &upper_atoms, &inclusion.origin)?;
            }
        }
        Ok(())
    }

    /// Add `effects ⊆ var` and propagate it along masked inclusions.
    fn add_lower(
        &mut self,
        var: EffectVar,
        effects: &EffType,
        source: &BoundSource,
        origin: &EffectConstraintOrigin,
    ) -> Result<(), InternalCompilationError> {
        let mut work: Vec<_> = effects
            .iter()
            .map(|effect| (var, effect, source.clone()))
            .collect();
        while let Some((var, effect, source)) = work.pop() {
            let root = self.table.find(var);
            let class = self.class(root);
            // An aliased class's bounds were replayed on its row, this one included.
            if class.alias.is_some() || class.lower.contains(effect) {
                continue;
            }
            self.update_class(root, EffectClass::with_lower(effect, source.clone()));
            self.check_ceiling(root, origin)?;
            for (target, mask) in class.successors {
                if !mask.contains(effect) {
                    work.push((target, effect, source.clone()));
                }
            }
        }
        Ok(())
    }

    /// Add `lower ⊆ (mask, upper)`.
    fn add_edge(
        &mut self,
        lower: EffectVar,
        upper: EffectVar,
        mask: &EffType,
        origin: &EffectConstraintOrigin,
    ) -> Result<(), InternalCompilationError> {
        let lower = self.table.find(lower);
        let upper = self.table.find(upper);
        if lower == upper {
            return Ok(());
        }
        let class = self.class(lower);
        if class
            .successors
            .iter()
            .any(|(target, edge_mask)| edge_mask == mask && self.table.find(*target) == upper)
        {
            return Ok(());
        }
        self.update_class(
            lower,
            EffectClass {
                successors: vec![(upper, mask.clone())],
                ..EffectClass::default()
            },
        );
        self.update_class(
            upper,
            EffectClass {
                predecessors: vec![(lower, mask.clone())],
                ..EffectClass::default()
            },
        );
        self.propagate_lower(lower, &class.lower.difference(mask), upper, origin)
    }

    /// Propagate the atoms `effects` of class `from` into `to`, keeping their sources.
    fn propagate_lower(
        &mut self,
        from: EffectVar,
        effects: &EffType,
        to: EffectVar,
        origin: &EffectConstraintOrigin,
    ) -> Result<(), InternalCompilationError> {
        let class = self.class(from);
        for effect in effects.iter() {
            let source = class.lower_source(effect);
            self.add_lower(to, &EffType::single(effect), &source, origin)?;
        }
        Ok(())
    }

    fn add_ceiling(
        &mut self,
        var: EffectVar,
        ceiling: Ceiling,
        origin: &EffectConstraintOrigin,
    ) -> Result<(), InternalCompilationError> {
        let root = self.table.find(var);
        self.update_class(
            root,
            EffectClass {
                ceiling: Some(ceiling),
                ..EffectClass::default()
            },
        );
        self.check_ceiling(root, origin)
    }

    /// Report the atoms of `root`'s least solution that its ceiling excludes.
    fn check_ceiling(
        &mut self,
        root: EffectVar,
        origin: &EffectConstraintOrigin,
    ) -> Result<(), InternalCompilationError> {
        let class = self.class(root);
        let Some(ceiling) = &class.ceiling else {
            return Ok(());
        };
        let excess = class.lower.difference(&ceiling.row);
        let Some(first) = excess.iter().next() else {
            return Ok(());
        };
        let source = class.lower_source(first);
        // An impl method check is the most useful diagnostic, wherever it took part.
        let origin = [origin, &source.origin, &ceiling.source.origin]
            .into_iter()
            .find(|origin| origin.is_trait_method_impl())
            .unwrap_or(origin)
            .clone();
        Err(invalid_effect_dependency(
            excess,
            source.span,
            ceiling.row.clone(),
            ceiling.source.span,
            origin,
        ))
    }

    /// Make two variables equal by merging their classes.
    fn union_vars(
        &mut self,
        a: EffectVar,
        b: EffectVar,
        span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.ensure_var(a);
        self.ensure_var(b);
        let a_root = self.table.find(a);
        let b_root = self.table.find(b);
        if a_root == b_root {
            return Ok(());
        }
        let a_class = self.class(a_root);
        let b_class = self.class(b_root);
        if a_class.alias.is_some() || b_class.alias.is_some() {
            let a_row = EffType::single_variable(a_root);
            let b_row = EffType::single_variable(b_root);
            return self.unify_same_effect(a_row, span, b_row, span);
        }
        if a_class.rigid || b_class.rigid {
            // A rigid variable is an atom: the other one must be exactly that atom.
            let a_row = EffType::single_variable(a_root);
            let b_row = EffType::single_variable(b_root);
            let origin = EffectConstraintOrigin::Inference;
            self.add_effect_inclusion(a_row.clone(), span, b_row.clone(), span, origin.clone())?;
            return self.add_effect_inclusion(b_row, span, a_row, span, origin);
        }
        self.invalidate_publication();
        self.table.union(a_root, b_root);
        let root = self.table.find(a_root);
        let origin = EffectConstraintOrigin::Inference;
        self.check_ceiling(root, &origin)?;
        let class = self.class(root);
        for (target, mask) in class.successors {
            let effects = class.lower.difference(&mask);
            self.propagate_lower(root, &effects, target, &origin)?;
        }
        Ok(())
    }

    /// Make the variable `var` equal to `row`, by replaying its bounds on the row.
    fn alias_var(
        &mut self,
        var: EffectVar,
        row: EffType,
        span: Location,
    ) -> Result<(), InternalCompilationError> {
        let root = self.table.find(var);
        let var_row = EffType::single_variable(root);
        if let Some(other) = row.to_single_variable() {
            return self.union_vars(root, other, span);
        }
        if self.class(root).rigid {
            let origin = EffectConstraintOrigin::Inference;
            self.add_effect_inclusion(var_row.clone(), span, row.clone(), span, origin.clone())?;
            return self.add_effect_inclusion(row, span, var_row, span, origin);
        }
        if row.contains(Effect::Variable(root)) {
            // `var = (rest, var)` only bounds `var` below.
            let mut rest = row.primitive_effects();
            for other in row.inner_vars() {
                if other != root {
                    rest.insert(Effect::Variable(other));
                }
            }
            return self.add_effect_inclusion(
                rest,
                span,
                var_row,
                span,
                EffectConstraintOrigin::Inference,
            );
        }
        let class = self.class(root);
        log::trace!("effect alias: {root} := {row}");
        self.update_class(
            root,
            EffectClass {
                alias: Some(row.clone()),
                ..EffectClass::default()
            },
        );
        for effect in class.lower.iter() {
            let source = class.lower_source(effect);
            self.add_effect_inclusion(
                EffType::single(effect),
                source.span,
                row.clone(),
                span,
                source.origin,
            )?;
        }
        if let Some(ceiling) = class.ceiling {
            self.add_effect_inclusion(
                row.clone(),
                span,
                ceiling.row,
                ceiling.source.span,
                ceiling.source.origin,
            )?;
        }
        for (target, mask) in class.successors {
            let mut upper = mask;
            upper.insert(Effect::Variable(target));
            self.add_effect_inclusion(
                row.clone(),
                span,
                upper,
                span,
                EffectConstraintOrigin::Inference,
            )?;
        }
        for (source, mask) in class.predecessors {
            let upper = mask.union(&row);
            self.add_effect_inclusion(
                EffType::single_variable(source),
                span,
                upper,
                span,
                EffectConstraintOrigin::Inference,
            )?;
        }
        Ok(())
    }

    /// The row `var` stands for in the current view.
    pub(super) fn substitute_var(&mut self, var: EffectVar) -> EffType {
        self.ensure_var(var);
        let root = self.table.find(var);
        let class = self.class(root);
        if let Some(alias) = class.alias {
            let mut row = alias.primitive_effects();
            for var in alias.inner_vars() {
                row.extend(&self.substitute_var(var));
            }
            return row;
        }
        if class.rigid {
            return EffType::single_variable(root);
        }
        if self.publishing {
            return self.publication_view().roots[&root].clone();
        }
        let representative = class.smallest.unwrap_or(root);
        match class.ceiling {
            Some(ceiling) if ceiling.row == class.lower => class.lower,
            _ => class.lower.union(&EffType::single_variable(representative)),
        }
    }

    pub(super) fn effect_var_affects_substitution(&mut self, var: EffectVar) -> bool {
        self.substitute_var(var) != EffType::single_variable(var)
    }

    /// The variable standing for `var` in the current view.
    pub(super) fn effect_var_root(&mut self, var: EffectVar) -> EffectVar {
        self.ensure_var(var);
        let root = self.table.find(var);
        if self.publishing {
            if let Some(representative) = self.publication_view().representatives.get(&root) {
                return *representative;
            }
        }
        self.class(root).smallest.unwrap_or(root)
    }

    fn publication_view(&mut self) -> &PublicationView {
        if self.publication.is_none() {
            self.publication = Some(self.compute_publication_view());
        }
        self.publication.as_ref().unwrap()
    }

    fn compute_publication_view(&mut self) -> PublicationView {
        // Solvable classes, with their smallest variable.
        let mut visited = FxHashSet::default();
        let mut classes = FxHashMap::default();
        let mut smallest = FxHashMap::default();
        let mut order = Vec::new();
        for index in 0..self.table.len() {
            let var = EffectVar::new(index as u32);
            let root = self.table.find(var);
            if !visited.insert(root) {
                continue;
            }
            let class = self.class(root);
            if class.alias.is_none() && !class.rigid {
                classes.insert(root, class);
                smallest.insert(root, var);
                order.push(root);
            }
        }
        let successors: FxHashMap<EffectVar, Vec<(EffectVar, EffType)>> = order
            .iter()
            .map(|root| {
                let edges = classes[root]
                    .successors
                    .iter()
                    .map(|(target, mask)| (self.table.find(*target), mask.clone()))
                    .filter(|(target, _)| target != root && classes.contains_key(target))
                    .collect();
                (*root, edges)
            })
            .collect();

        // Greatest solution of the ceilings, derived backwards through masked inclusions.
        let mut ceilings: FxHashMap<EffectVar, EffType> = order
            .iter()
            .filter_map(|root| Some((*root, classes[root].ceiling.as_ref()?.row.clone())))
            .collect();
        let mut changed = true;
        while changed {
            changed = false;
            for root in &order {
                for (target, mask) in &successors[root] {
                    let Some(target_ceiling) = ceilings.get(target) else {
                        continue;
                    };
                    let derived = mask.union(target_ceiling);
                    let narrowed = match ceilings.get(root) {
                        Some(ceiling) => ceiling.intersection(&derived),
                        None => derived,
                    };
                    if ceilings.get(root) != Some(&narrowed) {
                        ceilings.insert(*root, narrowed);
                        changed = true;
                    }
                }
            }
        }

        // Least atoms of the unbounded classes, with bounded ones at their ceilings.
        let mut least: FxHashMap<EffectVar, EffType> = order
            .iter()
            .map(|root| (*root, classes[root].lower.clone()))
            .collect();
        changed = true;
        while changed {
            changed = false;
            for root in &order {
                let value = ceilings
                    .get(root)
                    .cloned()
                    .unwrap_or_else(|| least[root].clone());
                for (target, mask) in &successors[root] {
                    if ceilings.contains_key(target) {
                        continue;
                    }
                    let flowing = value.difference(mask);
                    if !flowing.difference(&least[target]).is_empty() {
                        least.get_mut(target).unwrap().extend(&flowing);
                        changed = true;
                    }
                }
            }
        }

        // Unbounded classes related by inclusions merge into their smallest variable.
        let mut groups = InPlaceUnificationTable::<GroupKey>::default();
        let mut group_keys = FxHashMap::default();
        for root in &order {
            if !ceilings.contains_key(root) {
                group_keys.insert(*root, groups.new_key(smallest[root]));
            }
        }
        for root in &order {
            let Some(key) = group_keys.get(root) else {
                continue;
            };
            for (target, _) in &successors[root] {
                if let Some(target_key) = group_keys.get(target) {
                    groups.union(*key, *target_key);
                }
            }
        }

        // A group whose least solution holds declared variables merges into them instead.
        let mut group_rigid: FxHashMap<EffectVar, EffType> = FxHashMap::default();
        for (root, key) in &group_keys {
            let representative = groups.probe_value(*key);
            let rigid = EffType::multiple_variable(&least[root].inner_vars());
            group_rigid
                .entry(representative)
                .or_default()
                .extend(&rigid);
        }
        let mut roots = FxHashMap::default();
        let mut representatives = FxHashMap::default();
        for root in order {
            let row = match ceilings.get(&root) {
                Some(ceiling) => ceiling.clone(),
                None => {
                    let smallest = groups.probe_value(group_keys[&root]);
                    let rigid = &group_rigid[&smallest];
                    match rigid.inner_vars().as_slice() {
                        [] => {
                            representatives.insert(root, smallest);
                            least[&root].union(&EffType::single_variable(smallest))
                        }
                        [declared] => {
                            representatives.insert(root, *declared);
                            least[&root].union(rigid)
                        }
                        _ => least[&root].union(rigid),
                    }
                }
            };
            roots.insert(root, row);
        }
        PublicationView {
            roots,
            representatives,
        }
    }

    pub(super) fn log_debug_constraints(&mut self) {
        if !log::log_enabled!(log::Level::Trace) {
            return;
        }
        log::trace!("Effect classes:");
        for i in 0..self.table.len() {
            let var = EffectVar::new(i as u32);
            let root = self.table.find(var);
            if root != var {
                log::trace!("  {var} = {root}");
                continue;
            }
            let class = self.class(root);
            if let Some(alias) = &class.alias {
                log::trace!("  {var} = {alias}");
                continue;
            }
            let ceiling = class
                .ceiling
                .as_ref()
                .map_or_else(|| "⊤".to_string(), |ceiling| ceiling.row.to_string());
            let successors = class
                .successors
                .iter()
                .map(|(target, mask)| format!("({mask}, {target})"))
                .collect::<Vec<_>>()
                .join(", ");
            log::trace!(
                "  {} ⊆ {var} ⊆ {ceiling}; {var} ⊆ [{successors}]",
                class.lower
            );
        }
        for inclusion in &self.deferred_inclusions {
            log::trace!("  deferred: {} ⊆ {}", inclusion.lower, inclusion.upper);
        }
    }
}

/// A group of effect classes merged for publication, valued by its smallest variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct GroupKey(u32);

impl ena::unify::UnifyKey for GroupKey {
    type Value = EffectVar;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Self(u)
    }

    fn tag() -> &'static str {
        "GroupKey"
    }
}

impl UnifyValue for EffectVar {
    type Error = NoError;

    fn unify_values(a: &Self, b: &Self) -> Result<Self, Self::Error> {
        Ok(*a.min(b))
    }
}

fn invalid_effect_dependency(
    source: EffType,
    source_span: Location,
    target: EffType,
    target_span: Location,
    origin: EffectConstraintOrigin,
) -> InternalCompilationError {
    match origin {
        EffectConstraintOrigin::Inference => internal_compilation_error!(InvalidEffectDependency {
            source,
            source_span,
            target,
            target_span,
        }),
        EffectConstraintOrigin::TraitMethodImpl {
            trait_id,
            method_name,
            impl_span,
        } => internal_compilation_error!(TraitMethodEffectMismatch {
            trait_ref: trait_id,
            method_name,
            expected: target,
            got: source,
            span: impl_span,
        }),
    }
}

#[cfg(test)]
mod tests {
    use ustr::ustr;

    use super::{EffectConstraintOrigin, EffectSolver};
    use crate::{
        compiler::error::CompilationErrorImpl,
        module::{LocalTraitId, ModuleId, TraitId},
        parser::location::Location,
        types::effects::{EffType, Effect, PrimitiveEffect},
    };

    fn fallible() -> EffType {
        EffType::single_primitive(PrimitiveEffect::Fallible)
    }

    fn read() -> EffType {
        EffType::single_primitive(PrimitiveEffect::Read)
    }

    fn write() -> EffType {
        EffType::single_primitive(PrimitiveEffect::Write)
    }

    impl EffectSolver {
        fn substitute(&mut self, eff: &EffType) -> EffType {
            let mut row = EffType::multiple_primitive(&eff.inner_non_vars());
            for var in eff.inner_vars() {
                row.extend(&self.substitute_var(var));
            }
            row
        }
    }

    #[test]
    fn allocation_preserves_existing_substitution_in_both_effect_views() {
        let span = Location::new_synthesized();
        for finalized in [false, true] {
            let mut solver = EffectSolver::default();
            let existing = solver.fresh_var();
            solver
                .add_effect_dep(&EffType::single_variable(existing), span, &read(), span)
                .unwrap();
            if finalized {
                solver.finalize().unwrap();
            }
            let before = solver.substitute_var(existing);
            let revision = solver.substitution_revision();
            let fresh = solver.fresh_var();
            let rigid = solver.fresh_rigid_var(None);
            assert_eq!(solver.substitution_revision(), revision);
            assert_eq!(solver.substitute_var(existing), before);
            // Publication must include the new roots even though its semantic
            // revision did not advance for their allocation.
            assert_eq!(
                solver.substitute_var(fresh),
                EffType::single_variable(fresh)
            );
            assert_eq!(
                solver.substitute_var(rigid),
                EffType::single_variable(rigid)
            );
            solver
                .unify_same_effect(
                    EffType::single_variable(fresh),
                    span,
                    EffType::empty(),
                    span,
                )
                .unwrap();
            assert_ne!(solver.substitution_revision(), revision);
        }
    }

    #[test]
    fn pure_effect_bound_survives_a_dependency_unified_with_its_target() {
        let mut solver = EffectSolver::default();
        let source = solver.fresh_var_ty();
        let target = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        solver.add_effect_dep(&source, span, &target, span).unwrap();
        solver
            .unify_same_effect(source.clone(), span, target, span)
            .unwrap();
        solver
            .add_effect_dep(&source, span, &EffType::empty(), span)
            .unwrap();

        let result = solver
            .add_effect_dep(&fallible(), span, &source, span)
            .and_then(|()| solver.expand_pending_dependencies());
        result.expect_err("a variable bounded by the pure row must reject fallible effects");
    }

    #[test]
    fn row_equality_with_shared_atoms_accepts_every_order() {
        // `(read, a) = (read, b)`, `a ⊆ ()` and `read ⊆ b` hold with `a = ()` and `b = read`.
        let span = Location::new_synthesized();
        for equality_first in [true, false] {
            let mut solver = EffectSolver::default();
            let a = solver.fresh_var_ty();
            let b = solver.fresh_var_ty();
            let equality = |solver: &mut EffectSolver| {
                solver
                    .unify_same_effect(read().union(&a), span, read().union(&b), span)
                    .unwrap();
            };
            if equality_first {
                equality(&mut solver);
            }
            solver
                .add_effect_dep(&a, span, &EffType::empty(), span)
                .unwrap();
            solver.add_effect_dep(&read(), span, &b, span).unwrap();
            if !equality_first {
                equality(&mut solver);
            }
            solver.finalize().unwrap();
        }
    }

    #[test]
    fn accumulated_open_bounds_are_checked_once_one_closes() {
        let mut solver = EffectSolver::default();
        let source = solver.fresh_var_ty();
        let left = solver.fresh_var_ty();
        let right = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        solver.add_effect_dep(&source, span, &left, span).unwrap();
        solver.add_effect_dep(&source, span, &right, span).unwrap();
        solver
            .add_effect_dep(&right, span, &EffType::empty(), span)
            .unwrap();
        solver
            .add_effect_dep(&fallible(), span, &source, span)
            .unwrap_err();
    }

    #[test]
    fn pure_effect_bound_holds_for_the_variable_as_stated() {
        let mut solver = EffectSolver::default();
        let source = solver.fresh_var_ty();
        let dependency = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        // `source` stands for `dependency` when bounded, then gains an effect of its own.
        solver
            .add_effect_dep(&source, span, &dependency, span)
            .unwrap();
        solver
            .add_effect_dep(&source, span, &EffType::empty(), span)
            .unwrap();
        solver
            .unify_same_effect(source, span, fallible(), span)
            .unwrap_err();
    }

    #[test]
    fn pure_effect_bound_that_already_holds_is_kept() {
        let mut solver = EffectSolver::default();
        let source = solver.fresh_var_ty();
        let dependency = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        solver
            .add_effect_dep(&source, span, &dependency, span)
            .unwrap();
        solver
            .unify_same_effect(dependency, span, EffType::empty(), span)
            .unwrap();
        solver
            .add_effect_dep(&source, span, &EffType::empty(), span)
            .unwrap();
        solver
            .unify_same_effect(source, span, fallible(), span)
            .unwrap_err();
    }

    #[test]
    fn deferred_inclusion_is_retried_as_stated() {
        let mut solver = EffectSolver::default();
        let alias = solver.fresh_var();
        let target = solver.fresh_var_ty();
        let other = solver.fresh_var();
        let left = solver.fresh_var();
        let right = solver.fresh_var();
        let span = Location::new_synthesized();

        solver
            .add_effect_dep(&EffType::single_variable(alias), span, &target, span)
            .unwrap();
        solver
            .add_effect_dep(
                &EffType::multiple_variable(&[alias, other]),
                span,
                &EffType::multiple_variable(&[left, right]),
                span,
            )
            .unwrap();
        for var in [left, right] {
            solver
                .add_effect_dep(
                    &EffType::single_variable(var),
                    span,
                    &EffType::empty(),
                    span,
                )
                .unwrap();
        }
        solver
            .unify_same_effect(EffType::single_variable(alias), span, fallible(), span)
            .unwrap();

        solver.expand_pending_dependencies().unwrap_err();
    }

    #[test]
    fn effect_dependency_cycles_propagate() {
        let mut solver = EffectSolver::default();
        let first = solver.fresh_var_ty();
        let second = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        solver.add_effect_dep(&first, span, &second, span).unwrap();
        solver.add_effect_dep(&second, span, &first, span).unwrap();
        solver.add_effect_dep(&write(), span, &first, span).unwrap();

        assert!(
            solver
                .substitute(&second)
                .contains(Effect::Primitive(PrimitiveEffect::Write))
        );
    }

    #[test]
    fn effect_dependency_preserves_trait_method_origin() {
        let mut solver = EffectSolver::default();
        let target = solver.fresh_var_ty();
        let span = Location::new_synthesized();
        let trait_id = TraitId::new(ModuleId::new(0), LocalTraitId::new(0));
        let method_name = ustr("pure");

        solver
            .add_effect_dep_with_origin(
                &read(),
                span,
                &target,
                span,
                EffectConstraintOrigin::TraitMethodImpl {
                    trait_id,
                    method_name,
                    impl_span: span,
                },
            )
            .unwrap();
        let error = solver
            .add_effect_dep(&target, span, &EffType::empty(), span)
            .unwrap_err();
        match &*error {
            CompilationErrorImpl::TraitMethodEffectMismatch {
                trait_ref,
                method_name: got_method_name,
                expected,
                got,
                span: got_span,
            } => {
                assert_eq!(*trait_ref, trait_id);
                assert_eq!(*got_method_name, method_name);
                assert_eq!(*expected, EffType::empty());
                assert_eq!(*got, read());
                assert_eq!(*got_span, span);
            }
            other => panic!("expected TraitMethodEffectMismatch, got {other:?}"),
        }
    }

    #[test]
    fn inclusion_into_pure_effect_bounds_unconstrained_variable() {
        let mut solver = EffectSolver::default();
        let var = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        solver
            .add_effect_dep(&var, span, &EffType::empty(), span)
            .unwrap();
        solver
            .add_effect_dep(&fallible(), span, &var, span)
            .unwrap_err();
    }

    #[test]
    fn inclusion_into_pure_effect_bounds_the_variables_a_variable_stands_for() {
        let mut solver = EffectSolver::default();
        let left = solver.fresh_var_ty();
        let right = solver.fresh_var_ty();
        let union = solver.make_dependent_effect([&left, &right]);
        let span = Location::new_synthesized();

        solver
            .add_effect_dep(&union, span, &EffType::empty(), span)
            .unwrap();
        solver.finalize().unwrap();
        assert_eq!(solver.substitute(&left), EffType::empty());
        assert_eq!(solver.substitute(&right), EffType::empty());
    }

    #[test]
    fn inclusion_into_pure_effect_rejects_concrete_effects_beside_variables() {
        let mut solver = EffectSolver::default();
        let var = solver.fresh_var_ty();
        let span = Location::new_synthesized();
        let lower = fallible().union(&var);

        solver
            .add_effect_dep(&lower, span, &EffType::empty(), span)
            .unwrap_err();
    }

    #[test]
    fn effect_equality_binds_union_to_single_variable() {
        let mut solver = EffectSolver::default();
        let left = solver.fresh_var();
        let right = solver.fresh_var();
        let output = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        solver
            .unify_same_effect(
                EffType::multiple_variable(&[left, right]),
                span,
                output.clone(),
                span,
            )
            .unwrap();
        solver
            .unify_same_effect(EffType::single_variable(left), span, read(), span)
            .unwrap();
        solver
            .unify_same_effect(EffType::single_variable(right), span, write(), span)
            .unwrap();
        solver.finalize().unwrap();

        let output_effects = solver.substitute(&output);
        assert!(output_effects.contains(Effect::Primitive(PrimitiveEffect::Read)));
        assert!(output_effects.contains(Effect::Primitive(PrimitiveEffect::Write)));
    }

    #[test]
    fn effect_equality_defers_multi_variable_unions() {
        let mut solver = EffectSolver::default();
        let left_a = solver.fresh_var();
        let left_b = solver.fresh_var();
        let right_a = solver.fresh_var();
        let right_b = solver.fresh_var();
        let span = Location::new_synthesized();

        solver
            .unify_same_effect(
                EffType::multiple_variable(&[left_a, left_b]),
                span,
                EffType::multiple_variable(&[right_a, right_b]),
                span,
            )
            .unwrap();
        solver
            .unify_same_effect(EffType::single_variable(right_a), span, read(), span)
            .unwrap();
        solver
            .unify_same_effect(EffType::single_variable(right_b), span, write(), span)
            .unwrap();
        solver.finalize().unwrap();

        let left_effects = solver.substitute(&EffType::multiple_variable(&[left_a, left_b]));
        assert!(left_effects.contains(Effect::Primitive(PrimitiveEffect::Read)));
        assert!(left_effects.contains(Effect::Primitive(PrimitiveEffect::Write)));
    }

    #[test]
    fn residual_inclusion_is_materialized_conservatively() {
        let mut solver = EffectSolver::default();
        let left = solver.fresh_var_ty();
        let right = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        solver
            .add_effect_dep(&read(), span, &left.union(&right), span)
            .unwrap();
        solver.finalize().unwrap();

        assert!(
            solver
                .substitute(&left)
                .contains(Effect::Primitive(PrimitiveEffect::Read))
        );
        assert!(
            solver
                .substitute(&right)
                .contains(Effect::Primitive(PrimitiveEffect::Read))
        );
    }

    #[test]
    fn upper_and_lower_bounds_solve_in_any_order() {
        for upper_first in [false, true] {
            let mut solver = EffectSolver::default();
            let var = solver.fresh_var_ty();
            let span = Location::new_synthesized();
            type Constraint<'a> = Box<dyn Fn(&mut EffectSolver) + 'a>;
            let mut constraints: Vec<Constraint<'_>> = vec![
                Box::new(|solver| {
                    solver
                        .unify_same_effect(fallible().union(&var), span, fallible(), span)
                        .unwrap()
                }),
                Box::new(|solver| {
                    solver
                        .add_effect_dep(&fallible(), span, &var, span)
                        .unwrap()
                }),
            ];
            if !upper_first {
                constraints.reverse();
            }
            for constraint in constraints {
                constraint(&mut solver);
            }
            assert_eq!(solver.substitute(&var), fallible());
        }
    }

    #[test]
    fn ceilings_on_one_variable_intersect() {
        let mut solver = EffectSolver::default();
        let var = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        solver
            .add_effect_dep(&var, span, &fallible().union(&write()), span)
            .unwrap();
        solver
            .add_effect_dep(&var, span, &fallible().union(&read()), span)
            .unwrap();
        solver
            .add_effect_dep(&fallible(), span, &var, span)
            .unwrap();
        solver
            .add_effect_dep(&read(), span, &var, span)
            .unwrap_err();
    }

    #[test]
    fn declared_variable_beyond_masked_atoms_must_fit_ceilings() {
        // With `A` declared, `A ⊆ (read, write, v)`, `v ⊆ A` and `v ⊆ fallible` hold only when
        // `A` holds nothing but `read` and `write`; no published row expresses that.
        let mut solver = EffectSolver::default();
        let declared = EffType::single_variable(solver.fresh_rigid_var(None));
        let var = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        solver
            .add_effect_dep(&declared, span, &read().union(&write()).union(&var), span)
            .unwrap();
        solver.add_effect_dep(&var, span, &declared, span).unwrap();
        solver
            .add_effect_dep(&var, span, &fallible(), span)
            .unwrap_err();
    }

    #[test]
    fn masked_inclusion_publishes_an_inclusion() {
        let mut solver = EffectSolver::default();
        let lower = solver.fresh_var_ty();
        let upper = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        solver
            .add_effect_dep(&lower, span, &read().union(&upper), span)
            .unwrap();
        solver.finalize().unwrap();

        let published_lower = solver.substitute(&lower);
        assert_eq!(published_lower.inner_vars().len(), 1);
        assert_eq!(solver.substitute(&upper), published_lower);
    }

    #[test]
    fn declared_variable_absorbs_the_inferred_ones_below_it() {
        let mut solver = EffectSolver::default();
        let declared = solver.fresh_rigid_var(None);
        let callback = solver.fresh_var_ty();
        let body = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        solver
            .add_effect_dep(&EffType::single_variable(declared), span, &body, span)
            .unwrap();
        solver.add_effect_dep(&callback, span, &body, span).unwrap();
        solver.finalize().unwrap();

        assert_eq!(solver.substitute(&body), EffType::single_variable(declared));
        assert_eq!(
            solver.substitute(&callback),
            EffType::single_variable(declared)
        );
    }

    #[test]
    fn inclusion_between_variables_keeps_the_lower_one_minimal() {
        let mut solver = EffectSolver::default();
        let parameter = solver.fresh_var_ty();
        let result = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        solver
            .add_effect_dep(&parameter, span, &result, span)
            .unwrap();
        solver
            .add_effect_dep(&fallible(), span, &result, span)
            .unwrap();
        solver.finalize().unwrap();

        let parameter_row = solver.substitute(&parameter);
        assert!(parameter_row.to_single_variable().is_some());
        assert_eq!(solver.substitute(&result), fallible().union(&parameter_row));
    }
}
