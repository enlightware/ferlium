// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::{iter::repeat, mem};

use crate::{FxHashMap, FxHashSet, Modules, type_scheme::PubTypeConstraint};

use derive_new::new;
use itertools::MultiUnzip;
use ustr::Ustr;

use crate::{
    Location,
    containers::b,
    effects::EffType,
    error::InternalCompilationError,
    function::{Function, ScriptFunction},
    internal_compilation_error,
    ir::{self, Node, NodeArena},
    ir_syn::{get_dictionary, load, static_apply},
    module::{
        self, BlanketTraitImplKey, BlanketTraitImpls, ConcreteTraitImplKey, DefKind, DefTable,
        FunctionCollector, FunctionId, ImportFunctionSlot, ImportFunctionSlotId,
        ImportFunctionTarget, ImportImplSlot, ImportImplSlotId, LocalDecl, LocalDeclId,
        LocalFunctionId, LocalImplId, Module, ModuleEnv, ModuleFunction, ModuleId, TraitImpl,
        TraitImplId, TraitImpls, TraitKey, id::Id,
    },
    mutability::MutType,
    std::{core::REPR_TRAIT, new_module_using_std},
    r#trait::TraitRef,
    r#type::{FnArgType, Type},
    type_inference::UnifiedTypeInference,
    type_like::{TypeLike, instantiate_types},
    value::{Value, build_dictionary_value},
};

#[cfg(debug_assertions)]
use crate::type_visitor::AllVarsCollector;

/// Trait solving is performed by this structure, mutating it by caching intermediate results.
#[derive(Debug, new)]
#[must_use = "call .commit() to store the created functions"]
pub struct TraitSolver<'a> {
    /// Current module implementations.
    pub impls: &'a mut TraitImpls,
    /// Current module functions available by name.
    pub current_functions: FxHashMap<Ustr, LocalFunctionId>,
    /// Current module function import slots.
    pub import_fn_slots: &'a mut Vec<ImportFunctionSlot>,
    /// Current module trait import slots.
    pub import_impl_slots: &'a mut Vec<ImportImplSlot>,
    /// Collector for newly created current module functions.
    pub fn_collector: FunctionCollector,
    /// Other modules available for fetching trait implementations and normal functions (read only).
    pub others: &'a Modules,
    /// Current recursion depth of the trait solver.
    #[new(default)]
    pub recursion_depth: usize,
    /// Current stack of trait implementations being solved, for cycle detection.
    #[new(default)]
    pub solving_stack: FxHashSet<(TraitRef, Vec<Type>)>,
    /// Partially known trait applications currently being improved, for cycle detection.
    #[new(default)]
    active_improvements: FxHashSet<TraitImprovementKey>,
}

const TRAIT_SOLVER_RECURSION_LIMIT: usize = 128;

/// Macro to create a trait solver from a module and a program.
/// This cannot be a function because of lifetime issues, as we must
/// mutably borrow parts of the module's data while not touching the function field.
macro_rules! trait_solver_from_module {
    ($module:expr, $program:expr) => {{
        let current_functions = crate::trait_solver::current_function_map(&$module.def_table);
        let function_count = $module.functions.len();
        TraitSolver::new(
            &mut $module.impls,
            current_functions,
            &mut $module.import_fn_slots,
            &mut $module.import_impl_slots,
            crate::module::FunctionCollector::new(function_count),
            $program,
        )
    }};
}
pub(crate) use trait_solver_from_module;

/// Scratch overlay for running trait-solver queries without mutating a real module.
pub(crate) struct TraitSolverProbe<'a> {
    impls: TraitImpls,
    current_functions: FxHashMap<Ustr, LocalFunctionId>,
    import_fn_slots: Vec<ImportFunctionSlot>,
    import_impl_slots: Vec<ImportImplSlot>,
    fn_collector: FunctionCollector,
    active_improvements: FxHashSet<TraitImprovementKey>,
    others: &'a Modules,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct TraitImprovementKey {
    trait_ref: TraitRef,
    input_tys: Vec<Type>,
    output_tys: Vec<Type>,
}

pub(crate) fn current_function_map(def_table: &DefTable) -> FxHashMap<Ustr, LocalFunctionId> {
    def_table
        .iter()
        .filter_map(|(def_kind, name)| {
            let name = name.as_ref()?;
            let local_id = def_kind.as_function().copied()?;
            Some((*name, local_id))
        })
        .collect()
}

/// Minimal query interface needed by blanket matching.
///
/// This is a trait so the same matching code can run either against the real
/// solver, which may materialize concrete impls, or against `TraitSolverProbe`,
/// which answers the same questions through a scratch overlay.
trait TraitOutputQuery {
    fn solve_output_types_query(
        &mut self,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<Vec<Type>, InternalCompilationError>;

    #[allow(clippy::too_many_arguments)]
    fn improve_trait_application_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        output_tys: &[Type],
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError>;
}

/// Borrowed view over the ambient public trait constraints that may discharge
/// nested blanket-impl requirements.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ConstraintAssumptions<'a> {
    constraints: &'a [PubTypeConstraint],
    skipped_index: Option<usize>,
}

impl<'a> ConstraintAssumptions<'a> {
    pub(crate) fn all(constraints: &'a [PubTypeConstraint]) -> Self {
        Self {
            constraints,
            skipped_index: None,
        }
    }

    pub(crate) fn excluding(constraints: &'a [PubTypeConstraint], skipped_index: usize) -> Self {
        Self {
            constraints,
            skipped_index: Some(skipped_index),
        }
    }

    pub(crate) fn iter(self) -> impl Iterator<Item = &'a PubTypeConstraint> {
        self.constraints
            .iter()
            .enumerate()
            .filter_map(move |(index, constraint)| {
                (self.skipped_index != Some(index)).then_some(constraint)
            })
    }
}

impl<'a> TraitSolverProbe<'a> {
    pub(crate) fn from_module(module: &Module, others: &'a Modules) -> Self {
        Self {
            impls: module.impls.clone(),
            current_functions: current_function_map(&module.def_table),
            import_fn_slots: module.import_fn_slots.clone(),
            import_impl_slots: module.import_impl_slots.clone(),
            fn_collector: FunctionCollector::new(module.functions.len()),
            active_improvements: FxHashSet::default(),
            others,
        }
    }

    fn from_solver(solver: &TraitSolver<'a>) -> Self {
        Self {
            impls: solver.impls.clone(),
            current_functions: solver.current_functions.clone(),
            import_fn_slots: solver.import_fn_slots.clone(),
            import_impl_slots: solver.import_impl_slots.clone(),
            fn_collector: solver.fn_collector.clone(),
            active_improvements: solver.active_improvements.clone(),
            others: solver.others,
        }
    }

    fn with_solver<R>(&mut self, f: impl FnOnce(&mut TraitSolver<'_>) -> R) -> R {
        let initial_count = self.fn_collector.initial_count;
        let fn_collector = mem::replace(
            &mut self.fn_collector,
            FunctionCollector::new(initial_count),
        );
        let mut solver = TraitSolver::new(
            &mut self.impls,
            self.current_functions.clone(),
            &mut self.import_fn_slots,
            &mut self.import_impl_slots,
            fn_collector,
            self.others,
        );
        solver.active_improvements = mem::take(&mut self.active_improvements);
        let result = f(&mut solver);
        self.active_improvements = mem::take(&mut solver.active_improvements);
        self.fn_collector = mem::replace(
            &mut solver.fn_collector,
            FunctionCollector::new(initial_count),
        );
        result
    }

    pub(crate) fn solve_output_types(
        &mut self,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        self.with_solver(|solver| solver.solve_output_types(trait_ref, input_tys, fn_span, arena))
    }
}

impl TraitOutputQuery for TraitSolverProbe<'_> {
    fn solve_output_types_query(
        &mut self,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        self.solve_output_types(trait_ref, input_tys, fn_span, arena)
    }

    fn improve_trait_application_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        output_tys: &[Type],
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        self.with_solver(|solver| {
            solver.improve_trait_application_match(
                ty_inf,
                trait_ref,
                input_tys,
                output_tys,
                assumptions,
                fn_span,
                arena,
            )
        })
    }
}

/// Lightweight visible impl head used while probing whether a partially known
/// trait application already has a unique candidate.
#[derive(Clone)]
enum TraitImprovementCandidate {
    /// A fully concrete impl head.
    Concrete {
        input_tys: Vec<Type>,
        output_tys: Vec<Type>,
    },
    /// A blanket impl head plus the generic information needed to instantiate
    /// and check its impl constraints.
    Blanket {
        input_tys: Vec<Type>,
        output_tys: Vec<Type>,
        ty_var_count: u32,
        constraints: Vec<PubTypeConstraint>,
    },
}

/// A nested trait constraint from a matched blanket impl after its inputs have
/// been fully resolved.
struct ResolvedTraitConstraint {
    /// Original source order of the constraint in the blanket impl.
    index: usize,
    trait_ref: TraitRef,
    input_tys: Vec<Type>,
}

/// Whether a visible impl candidate is compatible with the current partially known trait application.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TraitImprovementMatch {
    /// The candidate is definitely incompatible.
    No,
    /// The candidate might still match later, but some blanket constraints are not resolved enough yet.
    Unknown,
    /// The candidate can already be matched uniquely with the current information.
    Yes,
}

/// Controls how `match_blanket_impl` treats nested trait constraints that are
/// still not fully resolved after reaching a fixed point.
enum BlanketConstraintMode {
    /// Matching is only considered successful if every nested trait constraint
    /// can be resolved immediately.
    RequireAllResolved,
    /// A partially resolved fixed point is reported back as `Unknown` instead
    /// of being treated as a definite mismatch.
    AllowUnknown,
}

/// Result of matching a blanket impl against a requested trait application.
enum BlanketImplMatch {
    /// The blanket impl is definitely incompatible.
    No,
    /// The blanket impl may still match later, but some nested trait
    /// constraints remain unresolved.
    Unknown,
    /// The blanket impl matches, yielding instantiated output types and the
    /// resolved nested trait constraints in source order.
    Yes {
        output_tys: Vec<Type>,
        resolved_constraints: Vec<ResolvedTraitConstraint>,
    },
}

impl<'a> TraitSolver<'a> {
    /// Collect all visible concrete and blanket impl heads for a trait.
    ///
    /// This is used by trait improvement to probe whether a partially known
    /// trait application already has a unique matching impl.
    fn improvement_candidates(&self, trait_ref: &TraitRef) -> Vec<TraitImprovementCandidate> {
        let mut candidates = Vec::new();

        for (key, id) in &self.impls.concrete_key_to_id {
            if &key.trait_ref == trait_ref {
                let imp = &self.impls.data[id.as_index()];
                candidates.push(TraitImprovementCandidate::Concrete {
                    input_tys: key.input_tys.clone(),
                    output_tys: imp.output_tys.clone(),
                });
            }
        }

        if let Some(blankets) = self.impls.blanket_key_to_id.get(trait_ref) {
            for (sub_key, id) in blankets {
                let imp = &self.impls.data[id.as_index()];
                candidates.push(TraitImprovementCandidate::Blanket {
                    input_tys: sub_key.input_tys.clone(),
                    output_tys: imp.output_tys.clone(),
                    ty_var_count: sub_key.ty_var_count,
                    constraints: sub_key.constraints.clone(),
                });
            }
        }

        for (_, entry) in self.others.iter_named() {
            let Some(module) = entry.module() else {
                continue;
            };

            for (key, id) in &module.impls.concrete_key_to_id {
                if &key.trait_ref == trait_ref {
                    let imp = &module.impls.data[id.as_index()];
                    if imp.public {
                        candidates.push(TraitImprovementCandidate::Concrete {
                            input_tys: key.input_tys.clone(),
                            output_tys: imp.output_tys.clone(),
                        });
                    }
                }
            }

            if let Some(blankets) = module.impls.blanket_key_to_id.get(trait_ref) {
                for (sub_key, id) in blankets {
                    let imp = &module.impls.data[id.as_index()];
                    if imp.public {
                        candidates.push(TraitImprovementCandidate::Blanket {
                            input_tys: sub_key.input_tys.clone(),
                            output_tys: imp.output_tys.clone(),
                            ty_var_count: sub_key.ty_var_count,
                            constraints: sub_key.constraints.clone(),
                        });
                    }
                }
            }
        }

        candidates
    }

    /// Check whether a visible impl candidate is compatible with the current
    /// partially known trait application.
    #[allow(clippy::too_many_arguments)]
    fn improvement_candidate_matches<Q: TraitOutputQuery>(
        query: &mut Q,
        ty_inf: &mut UnifiedTypeInference,
        candidate: &TraitImprovementCandidate,
        input_tys: &[Type],
        output_tys: &[Type],
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        match candidate {
            TraitImprovementCandidate::Concrete {
                input_tys: candidate_inputs,
                output_tys: candidate_outputs,
            } => {
                for (candidate_input, input_ty) in candidate_inputs.iter().zip(input_tys.iter()) {
                    if ty_inf
                        .unify_same_type(*candidate_input, fn_span, *input_ty, fn_span)
                        .is_err()
                    {
                        return Ok(TraitImprovementMatch::No);
                    }
                }
                for (candidate_output, output_ty) in candidate_outputs.iter().zip(output_tys.iter())
                {
                    if ty_inf
                        .unify_same_type(*candidate_output, fn_span, *output_ty, fn_span)
                        .is_err()
                    {
                        return Ok(TraitImprovementMatch::No);
                    }
                }
                Ok(TraitImprovementMatch::Yes)
            }
            TraitImprovementCandidate::Blanket {
                input_tys: candidate_inputs,
                output_tys: candidate_outputs,
                ty_var_count,
                constraints,
            } => Ok(
                match Self::match_blanket_impl(
                    query,
                    ty_inf,
                    candidate_inputs,
                    candidate_outputs,
                    *ty_var_count,
                    constraints,
                    input_tys,
                    output_tys,
                    assumptions,
                    fn_span,
                    arena,
                    BlanketConstraintMode::AllowUnknown,
                )? {
                    BlanketImplMatch::No => TraitImprovementMatch::No,
                    BlanketImplMatch::Unknown => TraitImprovementMatch::Unknown,
                    BlanketImplMatch::Yes { .. } => TraitImprovementMatch::Yes,
                },
            ),
        }
    }

    /// Try to improve a deferred trait application from its partially known
    /// inputs and outputs.
    ///
    /// The algorithm probes every visible impl under snapshots of the current
    /// unifier. It only commits the improvement when there is exactly one
    /// matching candidate and no other candidate remains merely `Unknown`.
    #[allow(clippy::too_many_arguments)]
    fn improve_trait_application_match(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        output_tys: &[Type],
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        let key = TraitImprovementKey {
            trait_ref: trait_ref.clone(),
            input_tys: ty_inf.substitute_in_types(input_tys),
            output_tys: ty_inf.substitute_in_types(output_tys),
        };
        if !self.active_improvements.insert(key.clone()) {
            return Ok(TraitImprovementMatch::Unknown);
        }
        let result = self.improve_trait_application_match_actual(
            ty_inf,
            trait_ref,
            input_tys,
            output_tys,
            assumptions,
            fn_span,
            arena,
        );
        self.active_improvements.remove(&key);
        result
    }

    #[allow(clippy::too_many_arguments)]
    fn improve_trait_application_match_actual(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        output_tys: &[Type],
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        let candidates = self.improvement_candidates(trait_ref);
        let mut probe = TraitSolverProbe::from_solver(self);
        let mut unique_candidate: Option<TraitImprovementCandidate> = None;
        let mut found_unknown_candidate = false;
        let mut found_multiple_yes_candidates = false;

        for candidate in candidates {
            let snapshot = ty_inf.snapshot();
            let matched = Self::improvement_candidate_matches(
                &mut probe,
                ty_inf,
                &candidate,
                input_tys,
                output_tys,
                assumptions,
                fn_span,
                arena,
            )?;
            ty_inf.rollback_to(snapshot);
            use TraitImprovementMatch::*;
            match matched {
                No => {}
                Unknown => {
                    found_unknown_candidate = true;
                }
                Yes => {
                    if unique_candidate.is_some() {
                        found_multiple_yes_candidates = true;
                        unique_candidate = None;
                        continue;
                    }
                    unique_candidate = Some(candidate);
                }
            }
        }

        if found_unknown_candidate || found_multiple_yes_candidates {
            return Ok(TraitImprovementMatch::Unknown);
        }
        let Some(candidate) = unique_candidate else {
            return Ok(TraitImprovementMatch::No);
        };

        Self::improvement_candidate_matches(
            self,
            ty_inf,
            &candidate,
            input_tys,
            output_tys,
            assumptions,
            fn_span,
            arena,
        )
    }

    /// Try to improve a deferred trait application from its partially known
    /// inputs and outputs.
    ///
    /// The algorithm probes every visible impl under snapshots of the current
    /// unifier. It only commits the improvement when there is exactly one
    /// matching candidate and no other candidate remains merely `Unknown`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn try_improve_trait_application(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        output_tys: &[Type],
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<bool, InternalCompilationError> {
        Ok(matches!(
            self.improve_trait_application_match(
                ty_inf,
                trait_ref,
                input_tys,
                output_tys,
                assumptions,
                fn_span,
                arena,
            )?,
            TraitImprovementMatch::Yes
        ))
    }

    /// Try to discharge a nested blanket-impl trait constraint from assumptions
    /// already in scope for the outer query.
    fn match_assumption(
        ty_inf: &mut UnifiedTypeInference,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        output_tys: &[Type],
        assumptions: ConstraintAssumptions<'_>,
    ) -> bool {
        assumptions.iter().any(|assumption| {
            let PubTypeConstraint::HaveTrait {
                trait_ref: assumption_trait_ref,
                input_tys: assumption_input_tys,
                output_tys: assumption_output_tys,
                ..
            } = assumption
            else {
                return false;
            };
            if assumption_trait_ref != trait_ref
                || assumption_input_tys.len() != input_tys.len()
                || assumption_output_tys.len() != output_tys.len()
            {
                return false;
            }

            let substituted_assumption = ty_inf.substitute_in_constraint(assumption);
            let Some((ass_trait_ref, ass_input_tys, ass_output_tys, _)) =
                substituted_assumption.as_have_trait()
            else {
                return false;
            };
            if !ass_input_tys.iter().all(Type::is_constant)
                || !ass_output_tys.iter().all(Type::is_constant)
            {
                return false;
            }
            if ass_trait_ref != trait_ref
                || ass_input_tys.len() != input_tys.len()
                || ass_output_tys.len() != output_tys.len()
            {
                return false;
            }
            ass_input_tys == input_tys && ass_output_tys == output_tys
        })
    }

    #[cfg(debug_assertions)]
    fn assert_blanket_impl_is_well_formed(
        imp_input_tys: &[Type],
        imp_constraints: &[PubTypeConstraint],
        imp_ty_var_count: u32,
        input_tys: &[Type],
    ) {
        assert_eq!(imp_input_tys.len(), input_tys.len());
        let mut ty_vars = FxHashSet::default();
        let mut mut_vars = FxHashSet::default();
        let mut eff_vars = FxHashSet::default();
        let mut collector = AllVarsCollector {
            ty_vars: &mut ty_vars,
            mut_vars: &mut mut_vars,
            effect_vars: &mut eff_vars,
        };
        for ty in imp_input_tys {
            ty.visit(&mut collector);
        }
        for constraint in imp_constraints {
            constraint.visit(&mut collector);
        }
        assert!(mut_vars.is_empty());
        assert!(eff_vars.is_empty());
        assert_eq!(ty_vars.len(), imp_ty_var_count as usize);
    }

    /// Match a blanket impl head plus its impl constraints against a requested
    /// trait application.
    ///
    /// This is the shared fixed-point engine used by both normal blanket impl
    /// solving and trait improvement. It instantiates the blanket-local type
    /// variables, unifies the impl head with the requested types, then iterates
    /// the impl constraints until no more progress is possible.
    #[allow(clippy::too_many_arguments)]
    fn match_blanket_impl<Q: TraitOutputQuery>(
        query: &mut Q,
        ty_inf: &mut UnifiedTypeInference,
        imp_input_tys: &[Type],
        imp_output_tys: &[Type],
        imp_ty_var_count: u32,
        imp_constraints: &[PubTypeConstraint],
        input_tys: &[Type],
        output_tys: &[Type],
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
        mode: BlanketConstraintMode,
    ) -> Result<BlanketImplMatch, InternalCompilationError> {
        // First instantiate the blanket-local type variables with fresh
        // inference variables in the caller-provided unifier.
        let inst_subst = (
            ty_inf.fresh_type_var_subst(imp_ty_var_count),
            FxHashMap::default(),
        );
        let imp_input_tys = instantiate_types(imp_input_tys, &inst_subst);
        let imp_output_tys = instantiate_types(imp_output_tys, &inst_subst);
        let mut remaining = instantiate_types(imp_constraints, &inst_subst)
            .into_iter()
            .enumerate()
            .collect::<Vec<_>>();
        let mut resolved_constraints = Vec::new();

        // Then unify the instantiated blanket input and output types against
        // the requested trait application. Propagating output equalities before
        // solving nested constraints lets those constraints observe any output
        // information already available at the use site.
        for (imp_input_ty, input_ty) in imp_input_tys.iter().zip(input_tys.iter()) {
            if ty_inf
                .unify_same_type(*imp_input_ty, fn_span, *input_ty, fn_span)
                .is_err()
            {
                return Ok(BlanketImplMatch::No);
            }
        }
        for (imp_output_ty, output_ty) in imp_output_tys.iter().zip(output_tys.iter()) {
            if ty_inf
                .unify_same_type(*imp_output_ty, fn_span, *output_ty, fn_span)
                .is_err()
            {
                return Ok(BlanketImplMatch::No);
            }
        }

        loop {
            let initial_count = remaining.len();
            let mut still_remaining = Vec::new();

            for (constraint_index, constraint) in remaining {
                // Re-substitute the constraint on every pass because earlier
                // solved constraints may have refined the type variables it uses.
                let (trait_ref, constraint_inputs, constraint_outputs, _span) = ty_inf
                    .substitute_in_constraint(&constraint)
                    .into_have_trait()
                    .expect("Non trait constraint in blanket impl");
                if Self::match_assumption(
                    ty_inf,
                    &trait_ref,
                    &constraint_inputs,
                    &constraint_outputs,
                    assumptions,
                ) {
                    continue;
                }
                if !constraint_inputs.iter().all(Type::is_constant) {
                    let has_structured_non_constant_input = constraint_inputs
                        .iter()
                        .any(|ty| !ty.is_constant() && !ty.data().is_variable());
                    if has_structured_non_constant_input {
                        match query.improve_trait_application_query(
                            ty_inf,
                            &trait_ref,
                            &constraint_inputs,
                            &constraint_outputs,
                            assumptions,
                            fn_span,
                            arena,
                        )? {
                            TraitImprovementMatch::No => return Ok(BlanketImplMatch::No),
                            TraitImprovementMatch::Unknown => {}
                            TraitImprovementMatch::Yes => {}
                        }
                    }
                    still_remaining.push((constraint_index, constraint));
                    continue;
                }
                let solved_outputs = match query.solve_output_types_query(
                    &trait_ref,
                    &constraint_inputs,
                    fn_span,
                    arena,
                ) {
                    Ok(outputs) => outputs,
                    Err(_) => return Ok(BlanketImplMatch::No),
                };
                for (solved_output, constraint_output) in
                    solved_outputs.iter().zip(constraint_outputs.iter())
                {
                    if ty_inf
                        .unify_same_type(*solved_output, fn_span, *constraint_output, fn_span)
                        .is_err()
                    {
                        return Ok(BlanketImplMatch::No);
                    }
                }
                resolved_constraints.push(ResolvedTraitConstraint {
                    index: constraint_index,
                    trait_ref,
                    input_tys: constraint_inputs,
                });
            }

            // Fixed point reached: either all nested constraints are solved or
            // we have to stop according to the caller's mode.
            if still_remaining.is_empty() {
                break;
            }

            if still_remaining.len() == initial_count {
                return Ok(match mode {
                    BlanketConstraintMode::RequireAllResolved => BlanketImplMatch::No,
                    BlanketConstraintMode::AllowUnknown => BlanketImplMatch::Unknown,
                });
            }

            remaining = still_remaining;
        }

        // Finally, unify the instantiated blanket outputs with the requested
        // outputs and return the resolved nested trait constraints in source order.
        for (imp_output_ty, output_ty) in imp_output_tys.iter().zip(output_tys.iter()) {
            if ty_inf
                .unify_same_type(*imp_output_ty, fn_span, *output_ty, fn_span)
                .is_err()
            {
                return Ok(BlanketImplMatch::No);
            }
        }

        resolved_constraints.sort_by_key(|constraint| constraint.index);
        Ok(BlanketImplMatch::Yes {
            output_tys: ty_inf.substitute_in_types(&imp_output_tys),
            resolved_constraints,
        })
    }

    /// Commit the newly created functions to the module.
    /// This must be called after trait solving is done,
    /// otherwise the created functions will be lost.
    pub fn commit(mut self, functions: &mut Vec<ModuleFunction>, def_table: &mut DefTable) {
        for (name, function) in self.fn_collector.new_elements.drain(..) {
            let id = LocalFunctionId::from_index(functions.len());
            def_table.insert(name, DefKind::Function(id));
            functions.push(function);
        }
    }

    /// Add a concrete trait implementation from the given code body, for single-function traits.
    pub fn add_concrete_impl_from_code(
        &mut self,
        code_entry: ir::NodeId,
        locals: Vec<LocalDecl>,
        trait_ref: &TraitRef,
        input_types: impl Into<Vec<Type>>,
        output_types: impl Into<Vec<Type>>,
    ) -> LocalImplId {
        let arg_names = trait_ref.functions[0].1.arg_names.clone();
        let function: Function = b(ScriptFunction::new(code_entry, arg_names));
        self.impls.add_concrete_raw(
            trait_ref.clone(),
            input_types.into(),
            output_types.into(),
            [(function, locals)],
            &mut self.fn_collector,
        )
    }

    /// Add a concrete trait implementation from one code body per trait method.
    pub fn add_concrete_impl_from_code_entries(
        &mut self,
        code_entries: impl Into<Vec<(ir::NodeId, Vec<LocalDecl>)>>,
        trait_ref: &TraitRef,
        input_types: impl Into<Vec<Type>>,
        output_types: impl Into<Vec<Type>>,
    ) -> LocalImplId {
        let functions = trait_ref
            .functions
            .iter()
            .zip(code_entries.into())
            .map(|((_, definition), (code_entry, locals))| {
                let arg_names = definition.arg_names.clone();
                (
                    b(ScriptFunction::new(code_entry, arg_names)) as Function,
                    locals,
                )
            })
            .collect::<Vec<_>>();
        self.impls.add_concrete_raw(
            trait_ref.clone(),
            input_types.into(),
            output_types.into(),
            functions,
            &mut self.fn_collector,
        )
    }

    /// Check if a concrete trait implementation exists, without performing any solving.
    /// This searches in current module first, then in other modules.
    /// Only public implementations from other modules are considered.
    pub fn has_concrete_impl(&self, key: &ConcreteTraitImplKey) -> bool {
        self.impls.concrete_key_to_id.contains_key(key)
            || self.others.iter_named().any(|(_, entry)| {
                entry.module().is_some_and(|module| {
                    let impls = &module.impls;
                    let id = impls.concrete_key_to_id.get(key);
                    if let Some(id) = id {
                        impls.data[id.as_index()].public
                    } else {
                        false
                    }
                })
            })
    }

    /// Get a concrete trait implementation by its key, without performing any solving.
    /// This searches in current module first, then in other modules.
    /// Only public implementations from other modules are considered.
    /// If found in other modules, the import slots are updated.
    pub fn get_concrete_impl(&mut self, key: &ConcreteTraitImplKey) -> Option<TraitImplId> {
        if let Some(id) = self.impls.concrete_key_to_id.get(key) {
            return Some(TraitImplId::Local(*id));
        }
        // Search other modules; separate immutable search from mutable slot update.
        let found = self.others.enumerates().find_map(|(module_id, entry, _)| {
            entry.module().and_then(|module| {
                let impls = &module.impls;
                impls.concrete_key_to_id.get(key).and_then(|id| {
                    let imp = &impls.data[id.as_index()];
                    if imp.public {
                        Some((module_id, TraitKey::Concrete(key.clone())))
                    } else {
                        None
                    }
                })
            })
        });
        found.map(|(module_id, trait_key)| {
            TraitImplId::Import(self.import_impl_dictionary(module_id, trait_key))
        })
    }

    /// Get the blanket trait implementations for the given trait reference, without performing any solving.
    /// This searches in other modules first, then in the current module.
    fn get_blanket_impls<'s: 'b, 'b>(
        &'s self,
        trait_ref: &'b TraitRef,
    ) -> impl Iterator<Item = (Option<ModuleId>, &'b BlanketTraitImpls)> + use<'b> {
        self.impls
            .blanket_key_to_id
            .get(trait_ref)
            .map(|blankets| (None, blankets))
            .into_iter()
            .chain(self.others.enumerates().flat_map(|(module_id, entry, _)| {
                entry.module().and_then(|module| {
                    module
                        .impls
                        .blanket_key_to_id
                        .get(trait_ref)
                        .map(|imp| (Some(module_id), imp))
                })
            }))
    }

    /// Print all known implementations for the given trait reference.
    fn log_debug_impls(&self, trait_ref: &TraitRef) {
        log::debug!("In current module:");
        let fake_current = new_module_using_std(self.others.next_id());
        let env = ModuleEnv::new(&fake_current, self.others);
        self.impls.log_debug_impls_headers(trait_ref, env);
        for (module_path, entry) in self.others.iter_named() {
            if let Some(module) = &entry.module {
                let impls = &module.impls;
                if impls.blanket_key_to_id.contains_key(trait_ref) {
                    log::debug!("In module {}:", module_path);
                    impls.log_debug_impls_headers(trait_ref, env);
                }
            }
        }
    }

    /// Get a concrete trait implementation for the given trait reference and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If matching blanket implementation is found, a derivation is attempted, if available.
    /// Otherwise an error is returned.
    /// This is the trait solver's core function.
    pub fn solve_impl(
        &mut self,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImplId, InternalCompilationError> {
        // Sanity checks
        assert!(
            input_tys.iter().all(Type::is_constant),
            "Getting trait implementation for non-constant input types"
        );

        // Cycle detection
        let key = (trait_ref.clone(), input_tys.to_vec());
        if self.solving_stack.contains(&key) {
            return Err(internal_compilation_error!(TraitSolverCycleDetected {
                trait_ref: trait_ref.clone(),
                input_tys: input_tys.to_vec(),
                fn_span,
            }));
        }

        // Recursion limit check
        if self.recursion_depth > TRAIT_SOLVER_RECURSION_LIMIT {
            return Err(internal_compilation_error!(
                TraitSolverRecursionLimitExceeded {
                    trait_ref: trait_ref.clone(),
                    input_tys: input_tys.to_vec(),
                    fn_span,
                }
            ));
        }

        self.recursion_depth += 1;
        self.solving_stack.insert(key.clone());

        let result = self.solve_impl_actual(trait_ref, input_tys, fn_span, arena);

        self.solving_stack.remove(&key);
        self.recursion_depth -= 1;
        result
    }

    fn solve_impl_actual(
        &mut self,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImplId, InternalCompilationError> {
        // Special case for `Repr` trait.
        if trait_ref == &*REPR_TRAIT {
            let input_ty = input_tys[0];
            let ty_data = input_ty.data();
            let output_ty = if ty_data.is_named() {
                let named = ty_data.as_named().unwrap().clone();
                named.instantiated_shape()
            } else {
                input_ty
            };

            // Only search in current module, create a new implementation if not found.
            let key = ConcreteTraitImplKey::new(trait_ref.clone(), input_tys.to_vec());
            let local_id = if let Some(id) = self.impls.concrete_key_to_id.get(&key) {
                *id
            } else {
                let imp = TraitImpl {
                    output_tys: vec![output_ty],
                    methods: vec![],
                    dictionary_value: Value::empty_tuple(),
                    dictionary_ty: Type::tuple([]),
                    public: false,
                    source_span: None,
                };
                self.impls.add_concrete_struct(key, imp)
            };
            return Ok(TraitImplId::Local(local_id));
        }

        // If a concrete implementation is found, return it.
        let key = ConcreteTraitImplKey::new(trait_ref.clone(), input_tys.to_vec());
        if let Some(imp) = self.get_concrete_impl(&key) {
            return Ok(imp);
        }

        // No concrete implementation found, search for a matching blanket implementation.
        // We first clone all blanket implementations to avoid borrowing issues.
        let blankets = self
            .get_blanket_impls(trait_ref)
            .map(|(module_id, blankets)| (module_id, blankets.clone()))
            .collect::<Vec<_>>();
        // Then we iterate over all blanket implementations, trying to unify their input types
        for (imp_module_id, blanket_impls) in blankets {
            'impl_loop: for (sub_key, impl_id) in blanket_impls.iter() {
                let imp_input_tys = &sub_key.input_tys;
                let imp_ty_var_count = sub_key.ty_var_count;
                let imp_constraints = &sub_key.constraints;
                let imp_output_tys = if let Some(module_id) = imp_module_id {
                    self.others
                        .get(module_id)
                        .unwrap()
                        .module
                        .as_ref()
                        .unwrap()
                        .impls
                        .data[impl_id.as_index()]
                    .output_tys
                    .clone()
                } else {
                    self.impls.data[impl_id.as_index()].output_tys.clone()
                };

                // Sanity checks
                #[cfg(debug_assertions)]
                Self::assert_blanket_impl_is_well_formed(
                    imp_input_tys,
                    imp_constraints,
                    imp_ty_var_count,
                    input_tys,
                );

                // Match the blanket implementation and resolve the blanket constraints to a
                // fixed point before materializing the concrete implementation.
                let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(imp_ty_var_count);
                let blanket_match = Self::match_blanket_impl(
                    self,
                    &mut ty_inf,
                    imp_input_tys,
                    &imp_output_tys,
                    imp_ty_var_count,
                    imp_constraints,
                    input_tys,
                    &[],
                    ConstraintAssumptions::all(&[]),
                    fn_span,
                    arena,
                    BlanketConstraintMode::RequireAllResolved,
                )?;
                let BlanketImplMatch::Yes {
                    output_tys,
                    resolved_constraints,
                } = blanket_match
                else {
                    continue 'impl_loop;
                };

                let mut constraint_dict_ids = Vec::with_capacity(resolved_constraints.len());
                for resolved_constraint in resolved_constraints {
                    // Marker traits have no runtime dictionary entries.
                    if resolved_constraint.trait_ref.functions.is_empty() {
                        continue;
                    }
                    let dict_id = match self.solve_impl(
                        &resolved_constraint.trait_ref,
                        &resolved_constraint.input_tys,
                        fn_span,
                        arena,
                    ) {
                        Ok(functions) => functions,
                        Err(_) => continue 'impl_loop,
                    };
                    constraint_dict_ids.push(dict_id);
                }

                // Succeeded? First get the blanket implementation data and compute the output types.
                let impls = if let Some(module_id) = imp_module_id {
                    &self
                        .others
                        .get(module_id)
                        .unwrap()
                        .module
                        .as_ref()
                        .unwrap()
                        .impls
                } else {
                    #[allow(clippy::needless_borrow)] // clippy has a bug here as of Rust 1.90
                    &self.impls
                };
                let imp = &impls.data[impl_id.as_index()];

                // Then collect constraint dictionary info for building thunk nodes later.
                // Each thunk gets its own arena, so we store (NodeKind, Type) pairs to re-create them.
                let constraint_dict_infos = constraint_dict_ids
                    .into_iter()
                    .map(|dict_id| {
                        let ty = self.get_impl_data_by_id(dict_id).dictionary_ty;
                        (get_dictionary(dict_id), ty)
                    })
                    .collect::<Vec<_>>();

                // Then, for every function in the blanket implementation, if needed create a thunk function
                // importing it and closing over the constraint dictionaries.
                let trait_key =
                    TraitKey::Blanket(BlanketTraitImplKey::new(trait_ref.clone(), sub_key.clone()));
                let definitions = trait_ref.instantiate_for_tys(input_tys, &output_tys);
                let gen_functions = imp.methods.clone(); // clone to avoid borrowing issues
                let (methods, tys): (Vec<_>, Vec<_>) = gen_functions
                    .iter()
                    .zip(definitions)
                    .enumerate()
                    .map(|(method_index, (fn_id, def))| {
                        // Build the concrete function type and hash its signature.
                        let fn_ty = Type::function_type(def.ty_scheme.ty.clone());

                        // Is the generic function from another module, or do we need to pass constraint dictionaries?
                        let id = if constraint_dict_infos.is_empty() && imp_module_id.is_none() {
                            // No, so we can just use the generic function as is.
                            *fn_id
                        } else {
                            // Yes, get the function id for doing the call to the generic function.
                            let function_id = match imp_module_id {
                                Some(module_id) => {
                                    let slot_id = self.import_impl_method(
                                        module_id,
                                        trait_key.clone(),
                                        method_index as u32,
                                    );
                                    FunctionId::Import(slot_id)
                                }
                                None => FunctionId::Local(*fn_id),
                            };

                            // Build the locals
                            let locals = def.gen_locals_no_bounds(
                                repeat(Location::new_synthesized()),
                                Location::new_synthesized(),
                            );

                            // Allocate constraint dictionary nodes into the module arena.
                            let constraint_dict_nodes: Vec<_> = constraint_dict_infos
                                .iter()
                                .map(|(kind, ty)| {
                                    arena.alloc(Node::new(
                                        kind.clone(),
                                        *ty,
                                        EffType::empty(),
                                        Location::new_synthesized(),
                                    ))
                                })
                                .collect();

                            // Build the arguments for the call: first the constraint dictionaries, then the original arguments.
                            let arguments: Vec<_> = constraint_dict_nodes
                                .iter()
                                .copied()
                                .chain(def.ty_scheme.ty.args.iter().enumerate().map(
                                    |(arg_i, arg_ty)| {
                                        let id = LocalDeclId::from_index(arg_i);
                                        arena.alloc(Node::new(
                                            load(arg_i, id),
                                            arg_ty.ty,
                                            EffType::empty(),
                                            fn_span,
                                        ))
                                    },
                                ))
                                .collect();

                            // Build the function type with added constraint dictionary arguments.
                            let mut ext_fn_ty = def.ty_scheme.ty.clone();
                            ext_fn_ty.args.splice(
                                0..0,
                                constraint_dict_infos
                                    .iter()
                                    .map(|(_, ty)| FnArgType::new(*ty, MutType::constant())),
                            );

                            // Build the application node.
                            let apply = static_apply(function_id, ext_fn_ty, arguments, fn_span);
                            let apply_id = arena.alloc(Node::new(
                                apply,
                                def.ty_scheme.ty.ret,
                                EffType::empty(),
                                fn_span,
                            ));
                            let code: Function =
                                b(ScriptFunction::new(apply_id, def.arg_names.clone()));
                            let function = ModuleFunction::new(def, code, None, locals);
                            let name = Ustr::from(&format!(
                                "{}-thunk",
                                trait_ref.qualified_method_name(method_index, input_tys)
                            ));
                            let id = self.fn_collector.next_id();
                            self.fn_collector.push(name, function);
                            id
                        };

                        (id, fn_ty)
                    })
                    .multiunzip();

                // Build and insert the implementation.
                let dictionary_ty = Type::tuple(tys);
                let dictionary_value = build_dictionary_value(&methods, self.impls.module_id);
                let imp = TraitImpl::new(
                    output_tys,
                    methods,
                    dictionary_value,
                    dictionary_ty,
                    false,
                    None,
                );
                let key = ConcreteTraitImplKey::new(trait_ref.clone(), input_tys.to_vec());
                let local_impl_id = self.impls.add_concrete_struct(key, imp);

                return Ok(TraitImplId::Local(local_impl_id));
            }
        }

        // No blanket implementation found, look for a derived implementation.
        for derive in &trait_ref.derivers {
            if let Some(impl_id) = derive.derive_impl(trait_ref, input_tys, fn_span, arena, self)? {
                return Ok(impl_id);
            } else {
                log::debug!(
                    "Tried derivation for trait {} with input types {:?}, but failed.",
                    trait_ref.name,
                    input_tys
                );
            }
        }

        // No matching implementation found.
        log::debug!(
            "No matching impl for trait \"{}\" found. Existing impls:",
            trait_ref.name
        );
        self.log_debug_impls(trait_ref);
        Err(internal_compilation_error!(TraitImplNotFound {
            trait_ref: trait_ref.clone(),
            input_tys: input_tys.to_vec(),
            fn_span,
        }))
    }

    /// Get a specific method implementation for the given trait reference and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If matching blanket implementation is found, a derivation is attempted, if available.
    /// Otherwise an error is returned.
    /// This function is implemented using solve_impl.
    pub fn solve_impl_method(
        &mut self,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        index: usize,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<FunctionId, InternalCompilationError> {
        let impl_id = self.solve_impl(trait_ref, input_tys, fn_span, arena)?;
        use TraitImplId::*;
        Ok(match impl_id {
            Local(id) => FunctionId::Local(self.impls.data[id.as_index()].methods[index]),
            Import(slot_id) => {
                let slot = &self.import_impl_slots[slot_id.as_index()];
                let module_id = slot.module;
                let key = slot.key.as_concrete().unwrap();
                let key = TraitKey::Concrete(key.clone());
                FunctionId::Import(self.import_impl_method(module_id, key, index as u32))
            }
        })
    }

    /// Get the output types for the given trait reference and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If matching blanket implementation is found, a derivation is attempted, if available.
    /// Otherwise an error is returned.
    /// This function is implemented using solve_impl.
    pub fn solve_output_types(
        &mut self,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        let impl_id = self.solve_impl(trait_ref, input_tys, fn_span, arena)?;
        Ok(self.get_impl_data_by_id(impl_id).output_tys.clone())
    }

    /// Get a specific trait implementation data by its id.
    pub fn get_impl_data_by_id(&self, impl_id: TraitImplId) -> &TraitImpl {
        use TraitImplId::*;
        match impl_id {
            Local(id) => &self.impls.data[id.as_index()],
            Import(slot_id) => {
                let slot = &self.import_impl_slots[slot_id.as_index()];
                let module_id = slot.module;
                let key = slot.key.as_concrete().unwrap();
                let other_impls = &self
                    .others
                    .get(module_id)
                    .unwrap_or_else(|| panic!("imported module #{module_id} not found"))
                    .module
                    .as_ref()
                    .unwrap()
                    .impls;
                let id = other_impls.concrete_key_to_id.get(key).unwrap_or_else(|| {
                    panic!("imported trait impl {key:?} not found in module #{module_id}")
                });
                &other_impls.data[id.as_index()]
            }
        }
    }

    /// Get a specific function from a given module.
    /// If necessary, the import slots are updated.
    pub fn get_function(
        &mut self,
        use_site: Location,
        module_path: &module::Path,
        function_name: Ustr,
    ) -> Result<FunctionId, InternalCompilationError> {
        let module_not_found_error = || {
            internal_compilation_error!(Internal {
                error: format!(
                    "Module {module_path} not found when looking for function {function_name}"
                ),
                span: use_site
            })
        };
        let (module_id, entry) = self
            .others
            .get_by_name(module_path)
            .ok_or_else(module_not_found_error)?;
        let module = entry.module().ok_or_else(module_not_found_error)?;
        module.get_function(function_name).ok_or_else(|| {
            internal_compilation_error!(Internal {
                error: format!("Function {function_name} not found in module {module_path}"),
                span: use_site
            })
        })?;
        Ok(FunctionId::Import(
            self.import_function(module_id, function_name),
        ))
    }

    /// Get a function from the current module if it is defined locally, otherwise import it.
    pub fn get_local_or_import_function(
        &mut self,
        use_site: Location,
        module_path: &module::Path,
        function_name: Ustr,
    ) -> Result<FunctionId, InternalCompilationError> {
        // We are only interested in named functions, not trait impl functions or lambdas, so we can ignore fn_collector.
        // if let Some(local_id) = self.fn_collector.get_function(function_name) {
        //     return Ok(FunctionId::Local(local_id));
        // }
        if let Some(local_id) = self.current_functions.get(&function_name).copied() {
            return Ok(FunctionId::Local(local_id));
        }
        self.get_function(use_site, module_path, function_name)
    }

    /// Import a function from another module, possibly updating the import slots.
    /// The function is assumed to exist.
    fn import_function(
        &mut self,
        module_id: ModuleId,
        function_name: Ustr,
    ) -> ImportFunctionSlotId {
        self.import_fn_slots
            .iter()
            .position(|slot| slot.module == module_id &&
                matches!(&slot.target, ImportFunctionTarget::NamedFunction(name) if *name == function_name)
            )
            .map(ImportFunctionSlotId::from_index)
            .unwrap_or_else(|| {
                let index = self.import_fn_slots.len();
                self.import_fn_slots.push(ImportFunctionSlot {
                    module: module_id,
                    target: ImportFunctionTarget::NamedFunction(function_name),
                });
                ImportFunctionSlotId::from_index(index)
            })
    }

    /// Import a trait impl method from another module, possibly updating the import slots.
    /// The trait impl is assumed to exist and the method index to be correct.
    fn import_impl_method(
        &mut self,
        module_id: ModuleId,
        key: TraitKey,
        method_index: u32,
    ) -> ImportFunctionSlotId {
        self.import_fn_slots
            .iter()
            .position(|slot| slot.module == module_id &&
                matches!(&slot.target, ImportFunctionTarget::TraitImplMethod { key: k, index: i } if k == &key && *i == method_index)
            )
            .map(ImportFunctionSlotId::from_index)
            .unwrap_or_else(|| {
                let index = self.import_fn_slots.len();
                self.import_fn_slots.push(ImportFunctionSlot {
                    module: module_id,
                    target: ImportFunctionTarget::TraitImplMethod {
                        key,
                        index: method_index,
                    },
                });
                ImportFunctionSlotId::from_index(index)
            })
    }

    /// Import a trait impl dictionary from another module, possibly updating the import slots.
    /// The trait key is assumed to exist.
    fn import_impl_dictionary(&mut self, module_id: ModuleId, key: TraitKey) -> ImportImplSlotId {
        self.import_impl_slots
            .iter()
            .position(|slot| slot.module == module_id && slot.key == key)
            .map(ImportImplSlotId::from_index)
            .unwrap_or_else(|| {
                let index = self.import_impl_slots.len();
                self.import_impl_slots.push(ImportImplSlot {
                    module: module_id,
                    key,
                });
                ImportImplSlotId::from_index(index)
            })
    }
}

impl TraitOutputQuery for TraitSolver<'_> {
    fn solve_output_types_query(
        &mut self,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        self.solve_output_types(trait_ref, input_tys, fn_span, arena)
    }

    fn improve_trait_application_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_ref: &TraitRef,
        input_tys: &[Type],
        output_tys: &[Type],
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        self.improve_trait_application_match(
            ty_inf,
            trait_ref,
            input_tys,
            output_tys,
            assumptions,
            fn_span,
            arena,
        )
    }
}

impl<'a> Drop for TraitSolver<'a> {
    fn drop(&mut self) {
        if !self.fn_collector.new_elements.is_empty() {
            log::warn!(
                "TraitSolver dropped without committing the created functions. Call .commit() to store them in the module."
            );
        }
    }
}
