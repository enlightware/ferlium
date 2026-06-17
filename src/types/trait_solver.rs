// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::{borrow::Cow, iter::repeat, mem};

use crate::{FxHashMap, FxHashSet, Modules, types::type_scheme::PubTypeConstraint};

use derive_new::new;
use ustr::Ustr;

use crate::{
    Location,
    compiler::error::InternalCompilationError,
    containers::b,
    hir::emit_value_impl::{function_value_method, generic_value_methods_for_type},
    hir::function::FunctionDefinition,
    hir::function::{PendingArgPassing, PendingValueArgPassing, ResolvedValueArgPassing},
    hir::hir_syn::{get_dictionary, load_local},
    hir::{
        CallArgument, FnInstData, Node, NodeArena, NodeKind, StaticApplication, value::LiteralValue,
    },
    internal_compilation_error,
    module::{
        self, BlanketImpls, BlanketTraitImplKey, BlanketTraitImpls, ConcreteTraitImplKey, Def,
        DefKind, DefTable, FunctionId, ImportFunctionSlot, ImportFunctionSlotId,
        ImportFunctionTarget, ImportImplSlot, ImportImplSlotId, LocalDecl, LocalDeclId,
        LocalFunctionId, LocalImplId, Module, ModuleEnv, ModuleFunction, ModuleId,
        PendingFunctionBody, PendingFunctionCollector, PendingModuleFunction, ResolvedValueLayout,
        TraitDictionary, TraitId, TraitImpl, TraitImplId, TraitImpls, TraitKey, TypeDefId,
        build_dictionary_value, id::Id,
    },
    std::{
        STD_MODULE_ID,
        core_traits_names::{REPR_TRAIT_NAME, TRIVIAL_COPY_TRAIT_NAME, VALUE_TRAIT_NAME},
        value::{
            is_function_surface_only_value_trait_application, is_value_trait,
            is_value_trait_for_function_type, value_layout_associated_const_values,
            value_layout_for_type,
        },
    },
    types::effects::{EffType, Effect, EffectVar},
    types::mutability::{MutType, MutVar},
    types::r#trait::{Trait, TraitAssociatedConstIndex, TraitMethodIndex},
    types::r#type::{FnArgType, Type, TypeDef, TypeDefSlot, TypeKind, TypeVar},
    types::type_inference::unify::UnifiedTypeInference,
    types::type_like::{TypeLike, instantiate_types},
    types::type_mapper::{BitmapInstantiationMapper, TypeMapper},
};

#[cfg(debug_assertions)]
use crate::types::type_visitor::AllVarsCollector;

/// Type definitions owned by the module currently being solved.
#[derive(Clone, Copy, Debug)]
pub struct CurrentTypeDefs<'a> {
    module_id: ModuleId,
    slots: &'a [TypeDefSlot],
}

impl<'a> CurrentTypeDefs<'a> {
    pub(crate) fn new(module_id: ModuleId, slots: &'a [TypeDefSlot]) -> Self {
        Self { module_id, slots }
    }

    fn get(self, id: TypeDefId) -> Option<&'a TypeDef> {
        if id.module == self.module_id {
            self.slots.get(id.index.as_index()).map(TypeDefSlot::def)
        } else {
            None
        }
    }
}

/// Trait solving is performed by this structure, mutating it by caching intermediate results.
#[allow(clippy::too_many_arguments)]
#[derive(Debug, new)]
#[must_use = "call .commit() to store the created functions"]
pub struct TraitSolver<'a> {
    /// Current module type definitions.
    pub current_type_defs: CurrentTypeDefs<'a>,
    /// Current module trait definitions.
    pub current_traits: &'a [Trait],
    /// Current module implementations.
    pub impls: &'a mut TraitImpls,
    /// Current module functions available by name.
    pub current_functions: FxHashMap<Ustr, LocalFunctionId>,
    /// Current module function import slots.
    pub import_fn_slots: &'a mut Vec<ImportFunctionSlot>,
    /// Current module trait import slots.
    pub import_impl_slots: &'a mut Vec<ImportImplSlot>,
    /// Collector for newly created current module functions.
    pub fn_collector: PendingFunctionCollector,
    /// Other modules available for fetching trait implementations and normal functions (read only).
    pub(crate) others: &'a Modules,
    /// Current recursion depth of the trait solver.
    #[new(default)]
    pub recursion_depth: usize,
    /// Current stack of trait implementations being solved, for cycle detection.
    #[new(default)]
    pub solving_stack: FxHashSet<(TraitId, Vec<Type>)>,
    /// Partially known trait applications currently being improved, for cycle detection.
    #[new(default)]
    active_improvements: FxHashSet<TraitImprovementKey>,
    /// Stack of defining modules for imported blanket impls currently being materialized.
    /// Only the top module's private impls are visible.
    #[new(default)]
    private_impl_scope: Vec<ModuleId>,
}

const TRAIT_SOLVER_RECURSION_LIMIT: usize = 128;

fn materialized_associated_const_values(
    trait_id: TraitId,
    trait_def: &Trait,
    input_tys: &[Type],
    template_values: &[LiteralValue],
    span: Location,
    solver: &TraitSolver<'_>,
) -> Result<Vec<LiteralValue>, InternalCompilationError> {
    if trait_def.associated_const_count() == 0 {
        return Ok(Vec::new());
    }
    if template_values.len() == trait_def.associated_const_count() {
        return Ok(template_values.to_vec());
    }
    // Temporary special case: blanket impls cannot yet store associated const
    // formulas, so materialized Value dictionaries synthesize layout metadata.
    if is_value_trait(trait_id, trait_def) {
        return Ok(
            value_layout_associated_const_values(input_tys[0], span, solver)?
                .into_iter()
                .map(LiteralValue::new_native)
                .collect(),
        );
    }
    Err(internal_compilation_error!(Internal {
        error: format!(
            "cannot materialize compiler-defined associated consts for trait {}",
            trait_def.name
        ),
        span,
    }))
}

/// Macro to create a trait solver from a module and a program.
/// This cannot be a function because of lifetime issues, as we must
/// mutably borrow parts of the module's data while not touching the function field.
macro_rules! trait_solver_from_module {
    ($module:expr, $program:expr) => {{
        let current_functions =
            crate::types::trait_solver::current_function_map(&$module.def_table);
        let function_count = $module.functions.len();
        TraitSolver::new(
            crate::types::trait_solver::CurrentTypeDefs::new(
                $module.module_id(),
                $module.type_defs.as_slice(),
            ),
            $module.traits.as_slice(),
            &mut $module.impls,
            current_functions,
            &mut $module.import_fn_slots,
            &mut $module.import_impl_slots,
            crate::module::PendingFunctionCollector::new(function_count),
            $program,
        )
    }};
}
pub(crate) use trait_solver_from_module;

/// Scratch overlay for running trait-solver queries without mutating a real module.
pub(crate) struct TraitSolverProbe<'a> {
    current_type_defs: CurrentTypeDefs<'a>,
    current_traits: &'a [Trait],
    impls: Cow<'a, TraitImpls>,
    current_functions: FxHashMap<Ustr, LocalFunctionId>,
    import_fn_slots: Vec<ImportFunctionSlot>,
    import_impl_slots: Vec<ImportImplSlot>,
    fn_collector: PendingFunctionCollector,
    active_improvements: FxHashSet<TraitImprovementKey>,
    private_impl_scope: Vec<ModuleId>,
    others: &'a Modules,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct TraitImprovementKey {
    trait_id: TraitId,
    input_tys: Vec<Type>,
    output_tys: Option<Vec<Type>>,
    output_effs: Option<Vec<EffType>>,
}

#[derive(Default)]
/// Renames inference variables deterministically so alpha-equivalent trait queries share a cycle-detection key.
struct AlphaCanonicalTypeMapper {
    ty_vars: FxHashMap<TypeVar, TypeVar>,
    mut_vars: FxHashMap<MutVar, MutVar>,
    effect_vars: FxHashMap<EffectVar, EffectVar>,
}

impl AlphaCanonicalTypeMapper {
    fn type_var(&mut self, var: TypeVar) -> TypeVar {
        let next = self.ty_vars.len() as u32;
        *self
            .ty_vars
            .entry(var)
            .or_insert_with(|| TypeVar::new(next))
    }

    fn mut_var(&mut self, var: MutVar) -> MutVar {
        let next = self.mut_vars.len() as u32;
        *self
            .mut_vars
            .entry(var)
            .or_insert_with(|| MutVar::new(next))
    }

    fn effect_var(&mut self, var: EffectVar) -> EffectVar {
        let next = self.effect_vars.len() as u32;
        *self
            .effect_vars
            .entry(var)
            .or_insert_with(|| EffectVar::new(next))
    }
}

impl TypeMapper for AlphaCanonicalTypeMapper {
    fn map_type(&mut self, ty: Type) -> Type {
        let Some(var) = ({ ty.data().as_variable().copied() }) else {
            return ty;
        };
        Type::variable(self.type_var(var))
    }

    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
        match mut_ty {
            MutType::Variable(var) => MutType::variable(self.mut_var(var)),
            MutType::Resolved(_) => mut_ty,
        }
    }

    fn map_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        EffType::from_vec(
            eff_ty
                .iter()
                .map(|effect| match effect {
                    Effect::Primitive(_) => effect,
                    Effect::Variable(var) => Effect::Variable(self.effect_var(var)),
                })
                .collect(),
        )
    }
}

pub(crate) fn current_function_map(def_table: &DefTable) -> FxHashMap<Ustr, LocalFunctionId> {
    def_table
        .iter()
        .filter_map(|(def, name)| {
            let name = name.as_ref()?;
            let local_id = def.kind.as_function().copied()?;
            Some((*name, local_id))
        })
        .collect()
}

/// Stub `TraitOutputQuery` for paths that statically never invoke a query
/// (concrete candidate matching only unifies types and never reaches `match_blanket_impl`).
struct NeverProbe;

impl TraitOutputQuery for NeverProbe {
    fn is_compiler_provided_no_output_trait_query(
        &mut self,
        _trait_id: TraitId,
        _input_tys: &[Type],
        _output_tys: &[Type],
        _output_effs: &[EffType],
    ) -> bool {
        false
    }

    fn solve_outputs_query(
        &mut self,
        _trait_id: TraitId,
        _input_tys: &[Type],
        _fn_span: Location,
        _arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        unreachable!(
            "NeverProbe should not be queried — concrete candidates do not call match_blanket_impl"
        )
    }

    fn improve_trait_application_query(
        &mut self,
        _ty_inf: &mut UnifiedTypeInference,
        _trait_id: TraitId,
        _input_tys: &[Type],
        _output_tys: Option<&[Type]>,
        _output_effs: Option<&[EffType]>,
        _assumptions: ConstraintAssumptions<'_>,
        _fn_span: Location,
        _arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        unreachable!(
            "NeverProbe should not be queried — concrete candidates do not call match_blanket_impl"
        )
    }
}

/// Minimal query interface needed by blanket matching.
///
/// This is a trait so the same matching code can run either against the real
/// solver, which may materialize concrete impls, or against `TraitSolverProbe`,
/// which answers the same questions through a scratch overlay.
trait TraitOutputQuery {
    fn is_compiler_provided_no_output_trait_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) -> bool;

    fn solve_outputs_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError>;

    /// Attempt to improve a trait application. `output_tys` and `output_effs`
    /// are `None` only for solver queries that intentionally ask for outputs
    /// from inputs alone; stored `HaveTrait` constraints pass full-arity lists.
    #[allow(clippy::too_many_arguments)]
    fn improve_trait_application_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError>;
}

/// Lazily materializes a scratch solver only if blanket matching reaches a
/// nested trait query. Head matching can reject many candidates without
/// needing to clone the solver state.
struct LazyTraitSolverProbe<'solver, 'a> {
    solver: &'solver TraitSolver<'a>,
    probe: Option<TraitSolverProbe<'a>>,
}

impl<'solver, 'a> LazyTraitSolverProbe<'solver, 'a> {
    fn new(solver: &'solver TraitSolver<'a>) -> Self {
        Self {
            solver,
            probe: None,
        }
    }

    fn probe(&mut self) -> &mut TraitSolverProbe<'a> {
        if self.probe.is_none() {
            self.probe = Some(TraitSolverProbe::from_solver(self.solver));
        }
        self.probe.as_mut().unwrap()
    }
}

impl TraitOutputQuery for LazyTraitSolverProbe<'_, '_> {
    fn is_compiler_provided_no_output_trait_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) -> bool {
        self.probe().is_compiler_provided_no_output_trait_query(
            trait_id,
            input_tys,
            output_tys,
            output_effs,
        )
    }

    fn solve_outputs_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        self.probe()
            .solve_outputs_query(trait_id, input_tys, fn_span, arena)
    }

    fn improve_trait_application_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        self.probe().improve_trait_application_query(
            ty_inf,
            trait_id,
            input_tys,
            output_tys,
            output_effs,
            assumptions,
            fn_span,
            arena,
        )
    }
}

/// Borrowed view over the ambient public trait constraints that may discharge
/// nested blanket-impl requirements.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ConstraintAssumptions<'a> {
    constraints: &'a [&'a PubTypeConstraint],
    skipped_index: Option<usize>,
}

impl<'a> ConstraintAssumptions<'a> {
    pub(crate) fn all(constraints: &'a [&'a PubTypeConstraint]) -> Self {
        Self {
            constraints,
            skipped_index: None,
        }
    }

    pub(crate) fn excluding(
        constraints: &'a [&'a PubTypeConstraint],
        skipped_index: usize,
    ) -> Self {
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
                (self.skipped_index != Some(index)).then_some(*constraint)
            })
    }
}

impl<'a> TraitSolverProbe<'a> {
    pub(crate) fn from_module(module: &'a Module, others: &'a Modules) -> Self {
        Self {
            current_type_defs: CurrentTypeDefs::new(
                module.module_id(),
                module.type_defs.as_slice(),
            ),
            current_traits: module.traits.as_slice(),
            impls: Cow::Borrowed(&module.impls),
            current_functions: current_function_map(&module.def_table),
            import_fn_slots: module.import_fn_slots.clone(),
            import_impl_slots: module.import_impl_slots.clone(),
            fn_collector: PendingFunctionCollector::new(module.functions.len()),
            active_improvements: FxHashSet::default(),
            private_impl_scope: Vec::new(),
            others,
        }
    }

    fn from_solver(solver: &TraitSolver<'a>) -> Self {
        let mut impls = solver.impls.clone();
        impls
            .concrete_key_to_id
            .retain(|_, id| impls.data[id.as_index()].public);
        Self {
            current_type_defs: solver.current_type_defs,
            current_traits: solver.current_traits,
            impls: Cow::Owned(impls),
            current_functions: solver.current_functions.clone(),
            import_fn_slots: solver.import_fn_slots.clone(),
            import_impl_slots: solver.import_impl_slots.clone(),
            fn_collector: solver.fn_collector.clone(),
            active_improvements: solver.active_improvements.clone(),
            private_impl_scope: solver.private_impl_scope.clone(),
            others: solver.others,
        }
    }

    fn with_solver<R>(&mut self, f: impl FnOnce(&mut TraitSolver<'_>) -> R) -> R {
        let initial_count = self.fn_collector.initial_count;
        let fn_collector = mem::replace(
            &mut self.fn_collector,
            PendingFunctionCollector::new(initial_count),
        );
        let mut solver = TraitSolver::new(
            self.current_type_defs,
            self.current_traits,
            self.impls.to_mut(),
            mem::take(&mut self.current_functions),
            &mut self.import_fn_slots,
            &mut self.import_impl_slots,
            fn_collector,
            self.others,
        );
        solver.active_improvements = mem::take(&mut self.active_improvements);
        solver.private_impl_scope = self.private_impl_scope.clone();
        let result = f(&mut solver);
        self.active_improvements = mem::take(&mut solver.active_improvements);
        self.private_impl_scope = mem::take(&mut solver.private_impl_scope);
        self.current_functions = mem::take(&mut solver.current_functions);
        self.fn_collector = mem::replace(
            &mut solver.fn_collector,
            PendingFunctionCollector::new(initial_count),
        );
        result
    }

    pub(crate) fn solve_outputs(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        self.with_solver(|solver| solver.solve_outputs(trait_id, input_tys, fn_span, arena))
    }
}

impl TraitOutputQuery for TraitSolverProbe<'_> {
    fn is_compiler_provided_no_output_trait_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) -> bool {
        let trait_def = trait_def_from_parts(
            self.current_type_defs.module_id,
            self.current_traits,
            self.others,
            trait_id,
        );
        is_compiler_provided_no_output_trait_application(
            trait_id,
            trait_def,
            input_tys,
            output_tys,
            output_effs,
        )
    }

    fn solve_outputs_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        self.solve_outputs(trait_id, input_tys, fn_span, arena)
    }

    fn improve_trait_application_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        self.with_solver(|solver| {
            solver.improve_trait_application_match(
                ty_inf,
                trait_id,
                input_tys,
                output_tys,
                output_effs,
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
        output_effs: Vec<EffType>,
    },
    /// A blanket impl head plus the generic information needed to instantiate
    /// and check its impl constraints.
    Blanket {
        input_tys: Vec<Type>,
        output_tys: Vec<Type>,
        output_effs: Vec<EffType>,
        ty_var_count: u32,
        eff_var_count: u32,
        constraints: Vec<PubTypeConstraint>,
    },
}

/// A nested trait constraint from a matched blanket impl after its inputs have
/// been fully resolved.
struct ResolvedTraitConstraint {
    /// Original source order of the constraint in the blanket impl.
    index: usize,
    trait_id: TraitId,
    input_tys: Vec<Type>,
    output_tys: Vec<Type>,
    output_effs: Vec<EffType>,
}

pub(crate) struct DerivedImplSnapshot {
    concrete_key_to_id: FxHashMap<ConcreteTraitImplKey, LocalImplId>,
    blanket_key_to_id: BlanketImpls,
    impl_data_len: usize,
    new_function_len: usize,
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
    /// Matching may succeed with concrete nested constraints that cannot be
    /// materialized until after reserving the concrete impl. Currently used for
    /// recursive `Value` materialization.
    DeferConcreteObligations,
}

/// Result of matching a blanket impl against a requested trait application.
enum BlanketImplMatch {
    /// The blanket impl is definitely incompatible.
    No,
    /// The blanket impl may still match later, but some nested trait
    /// constraints remain unresolved.
    Unknown,
    /// The blanket impl matches, yielding instantiated output types and effects
    /// and the resolved nested trait constraints in source order.
    Yes {
        output_tys: Vec<Type>,
        output_effs: Vec<EffType>,
        resolved_constraints: Vec<ResolvedTraitConstraint>,
    },
}

fn trait_def_from_parts<'a>(
    current_module_id: ModuleId,
    current_traits: &'a [Trait],
    others: &'a Modules,
    id: TraitId,
) -> &'a Trait {
    if id.module == current_module_id
        && let Some(trait_def) = current_traits.get(id.index.as_index())
    {
        return trait_def;
    }
    others
        .get(id.module)
        .and_then(|entry| entry.module())
        .unwrap_or_else(|| panic!("Trait module #{} is unavailable", id.module))
        .trait_def(id)
}

fn is_compiler_provided_no_output_trait_application(
    trait_id: TraitId,
    trait_def: &Trait,
    input_tys: &[Type],
    output_tys: &[Type],
    output_effs: &[EffType],
) -> bool {
    output_tys.is_empty()
        && output_effs.is_empty()
        && (is_value_trait_for_function_type(trait_id, trait_def, input_tys, output_tys)
            || is_function_surface_only_value_trait_application(
                trait_id, trait_def, input_tys, output_tys,
            ))
}

impl<'a> TraitSolver<'a> {
    /// Whether a partially unresolved trait application has enough input-side
    /// shape for improvement to learn from visible impl heads.
    ///
    /// A bare inference variable carries no impl-selection information, but a
    /// resolved or structured input such as `[int]`, `Option<T>`, or
    /// `MapIterator<I, T, O>` can make an impl candidate unique even when some
    /// other input is still unresolved.
    ///
    /// A bare function type is deliberately not a driver here: generic
    /// function values such as `map` or `filter_map` can carry large unresolved
    /// effect/type graphs, and probing ordinary trait impl heads from that
    /// shape cannot select a user-visible impl. Function `Value` handling is
    /// covered by compiler-provided special cases once applicable.
    pub(crate) fn input_tys_can_drive_improvement(input_tys: &[Type]) -> bool {
        input_tys
            .iter()
            .any(|ty| !matches!(&*ty.data(), TypeKind::Variable(_) | TypeKind::Function(_)))
    }

    fn can_use_other_impl(&self, module_id: ModuleId, imp: &TraitImpl) -> bool {
        imp.public || self.private_impl_scope.last().copied() == Some(module_id)
    }

    pub(crate) fn reject_inaccessible_private_repr(
        &self,
        id: TypeDefId,
        access_span: Location,
    ) -> Result<(), InternalCompilationError> {
        if id.module != self.current_type_defs.module_id && self.type_def(id).has_private_repr() {
            return Err(internal_compilation_error!(PrivateReprAccess {
                type_def: id,
                access_span,
            }));
        }
        Ok(())
    }

    pub fn trait_def(&self, id: TraitId) -> &Trait {
        trait_def_from_parts(
            self.current_type_defs.module_id,
            self.current_traits,
            self.others,
            id,
        )
    }

    pub fn std_trait_id(&self, name: &str) -> TraitId {
        // The solver only keeps the current module's trait definitions, not its
        // definition table, so current-std lookups cannot use the symbol table.
        if self.current_type_defs.module_id == STD_MODULE_ID
            && let Some((index, _)) = self
                .current_traits
                .iter()
                .enumerate()
                .find(|(_, trait_def)| trait_def.name == name)
        {
            return TraitId::new(
                STD_MODULE_ID,
                crate::module::LocalTraitId::from_index(index),
            );
        }
        Module::expect_std_trait_id(self.others, name)
    }

    pub fn type_def(&self, id: TypeDefId) -> &TypeDef {
        self.current_type_defs.get(id).unwrap_or_else(|| {
            self.others
                .get(id.module)
                .and_then(|entry| entry.module())
                .unwrap_or_else(|| panic!("Type definition module #{} is unavailable", id.module))
                .type_def(id)
        })
    }

    pub(crate) fn solve_concrete_trivial_copy_layout(
        &mut self,
        arena: &mut NodeArena,
        ty: Type,
        span: Location,
    ) -> Result<Option<ResolvedValueLayout>, InternalCompilationError> {
        if !ty.is_constant() {
            return Ok(None);
        }
        if self
            .solve_impl(
                self.std_trait_id(TRIVIAL_COPY_TRAIT_NAME),
                &[ty],
                span,
                arena,
            )
            .is_err()
        {
            return Ok(None);
        }
        // `TrivialCopy` is marker-only, so selecting its impl proves that a
        // representation copy is valid but does not itself carry layout data.
        // The layout is synthesized structurally from the same concrete type.
        Ok(Some(value_layout_for_type(ty, span, self)?))
    }

    pub(crate) fn resolved_arg_passing_for_no_temp_arg(
        &mut self,
        arena: &mut NodeArena,
        arg: &FnArgType,
        span: Location,
    ) -> Result<PendingArgPassing, InternalCompilationError> {
        if arg
            .mut_ty
            .as_resolved()
            .is_some_and(|mut_ty| mut_ty.is_mutable())
        {
            Ok(PendingArgPassing::MutableRef)
        } else if self
            .solve_concrete_trivial_copy_layout(arena, arg.ty, span)?
            .is_some()
        {
            Ok(PendingArgPassing::Value(PendingValueArgPassing::Resolved(
                ResolvedValueArgPassing::TrivialCopy,
            )))
        } else {
            Ok(PendingArgPassing::Value(PendingValueArgPassing::Resolved(
                ResolvedValueArgPassing::SharedRef,
            )))
        }
    }

    fn resolved_arg_passing_for_no_temp_args(
        &mut self,
        arena: &mut NodeArena,
        args: &[FnArgType],
        span: Location,
    ) -> Result<Vec<PendingArgPassing>, InternalCompilationError> {
        args.iter()
            .map(|arg| self.resolved_arg_passing_for_no_temp_arg(arena, arg, span))
            .collect()
    }

    /// Collect all visible concrete and blanket impl heads for a trait.
    ///
    /// This is used by trait improvement to probe whether a partially known
    /// trait application already has a unique matching impl.
    fn improvement_candidates(&self, trait_id: TraitId) -> Vec<TraitImprovementCandidate> {
        let mut candidates = Vec::new();

        for (key, id) in &self.impls.concrete_key_to_id {
            if key.trait_id == trait_id {
                let imp = &self.impls.data[id.as_index()];
                if !imp.public {
                    continue;
                }
                candidates.push(TraitImprovementCandidate::Concrete {
                    input_tys: key.input_tys.clone(),
                    output_tys: imp.output_tys.clone(),
                    output_effs: imp.output_effs.clone(),
                });
            }
        }

        if let Some(blankets) = self.impls.blanket_key_to_id.get(&trait_id) {
            for (sub_key, id) in blankets {
                let imp = &self.impls.data[id.as_index()];
                candidates.push(TraitImprovementCandidate::Blanket {
                    input_tys: sub_key.input_tys.clone(),
                    output_tys: imp.output_tys.clone(),
                    output_effs: imp.output_effs.clone(),
                    ty_var_count: sub_key.ty_var_count,
                    eff_var_count: sub_key.eff_var_count,
                    constraints: sub_key.constraints.clone(),
                });
            }
        }

        for (_, entry) in self.others.iter_named() {
            let Some(module) = entry.module() else {
                continue;
            };

            for (key, id) in &module.impls.concrete_key_to_id {
                if key.trait_id == trait_id {
                    let imp = &module.impls.data[id.as_index()];
                    if self.can_use_other_impl(module.module_id(), imp) {
                        candidates.push(TraitImprovementCandidate::Concrete {
                            input_tys: key.input_tys.clone(),
                            output_tys: imp.output_tys.clone(),
                            output_effs: imp.output_effs.clone(),
                        });
                    }
                }
            }

            if let Some(blankets) = module.impls.blanket_key_to_id.get(&trait_id) {
                for (sub_key, id) in blankets {
                    let imp = &module.impls.data[id.as_index()];
                    if self.can_use_other_impl(module.module_id(), imp) {
                        candidates.push(TraitImprovementCandidate::Blanket {
                            input_tys: sub_key.input_tys.clone(),
                            output_tys: imp.output_tys.clone(),
                            output_effs: imp.output_effs.clone(),
                            ty_var_count: sub_key.ty_var_count,
                            eff_var_count: sub_key.eff_var_count,
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
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        match candidate {
            TraitImprovementCandidate::Concrete {
                input_tys: candidate_inputs,
                output_tys: candidate_outputs,
                output_effs: candidate_output_effs,
            } => {
                for (candidate_input, input_ty) in candidate_inputs.iter().zip(input_tys.iter()) {
                    if ty_inf
                        .unify_same_type_with_sub_effects(
                            *candidate_input,
                            fn_span,
                            *input_ty,
                            fn_span,
                        )
                        .is_err()
                    {
                        return Ok(TraitImprovementMatch::No);
                    }
                }
                if let Some(output_tys) = output_tys {
                    for (candidate_output, output_ty) in
                        candidate_outputs.iter().zip(output_tys.iter())
                    {
                        if ty_inf
                            .unify_same_type_with_sub_effects(
                                *candidate_output,
                                fn_span,
                                *output_ty,
                                fn_span,
                            )
                            .is_err()
                        {
                            return Ok(TraitImprovementMatch::No);
                        }
                    }
                }
                if let Some(output_effs) = output_effs {
                    for (candidate_eff, output_eff) in
                        candidate_output_effs.iter().zip(output_effs.iter())
                    {
                        if Self::match_trait_output_effect(
                            ty_inf,
                            candidate_eff,
                            output_eff,
                            fn_span,
                        )
                        .is_err()
                        {
                            return Ok(TraitImprovementMatch::No);
                        }
                    }
                }
                Ok(TraitImprovementMatch::Yes)
            }
            TraitImprovementCandidate::Blanket {
                input_tys: candidate_inputs,
                output_tys: candidate_outputs,
                output_effs: candidate_output_effs,
                ty_var_count,
                eff_var_count,
                constraints,
            } => Ok(
                match Self::match_blanket_impl(
                    query,
                    ty_inf,
                    candidate_inputs,
                    candidate_outputs,
                    candidate_output_effs,
                    *ty_var_count,
                    *eff_var_count,
                    constraints,
                    input_tys,
                    output_tys,
                    output_effs,
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

    fn improve_trait_application_with_candidate_head(
        ty_inf: &mut UnifiedTypeInference,
        candidate: &TraitImprovementCandidate,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        fn_span: Location,
    ) -> Result<(), InternalCompilationError> {
        match candidate {
            TraitImprovementCandidate::Concrete {
                input_tys: candidate_inputs,
                output_tys: candidate_outputs,
                output_effs: candidate_output_effs,
            } => {
                for (candidate_input, input_ty) in candidate_inputs.iter().zip(input_tys.iter()) {
                    ty_inf.unify_same_type_with_sub_effects(
                        *candidate_input,
                        fn_span,
                        *input_ty,
                        fn_span,
                    )?;
                }
                if let Some(output_tys) = output_tys {
                    for (candidate_output, output_ty) in
                        candidate_outputs.iter().zip(output_tys.iter())
                    {
                        ty_inf.unify_same_type_with_sub_effects(
                            *candidate_output,
                            fn_span,
                            *output_ty,
                            fn_span,
                        )?;
                    }
                }
                if let Some(output_effs) = output_effs {
                    for (candidate_eff, output_eff) in
                        candidate_output_effs.iter().zip(output_effs.iter())
                    {
                        Self::match_trait_output_effect(
                            ty_inf,
                            candidate_eff,
                            output_eff,
                            fn_span,
                        )?;
                    }
                }
            }
            TraitImprovementCandidate::Blanket {
                input_tys: candidate_inputs,
                output_tys: candidate_outputs,
                output_effs: candidate_output_effs,
                ty_var_count,
                eff_var_count,
                constraints,
            } => {
                let mut eff_subst = ty_inf.fresh_effect_var_subst(*eff_var_count);
                eff_subst
                    .extend(ty_inf.fresh_effect_var_subst_for(constraints, candidate_output_effs));
                let inst_subst = (ty_inf.fresh_type_var_subst(*ty_var_count), eff_subst);
                let mut mapper = BitmapInstantiationMapper::new(&inst_subst);
                let candidate_inputs = instantiate_types(candidate_inputs, &mut mapper);
                let candidate_outputs = instantiate_types(candidate_outputs, &mut mapper);
                let candidate_output_effs: Vec<_> = candidate_output_effs
                    .iter()
                    .map(|eff| mapper.map_effect_type(eff))
                    .collect();
                for (candidate_input, input_ty) in candidate_inputs.iter().zip(input_tys.iter()) {
                    ty_inf.unify_same_type_with_sub_effects(
                        *candidate_input,
                        fn_span,
                        *input_ty,
                        fn_span,
                    )?;
                }
                if let Some(output_tys) = output_tys {
                    for (candidate_output, output_ty) in
                        candidate_outputs.iter().zip(output_tys.iter())
                    {
                        ty_inf.unify_same_type_with_sub_effects(
                            *candidate_output,
                            fn_span,
                            *output_ty,
                            fn_span,
                        )?;
                    }
                }
                if let Some(output_effs) = output_effs {
                    for (candidate_eff, output_eff) in
                        candidate_output_effs.iter().zip(output_effs.iter())
                    {
                        Self::match_trait_output_effect(
                            ty_inf,
                            candidate_eff,
                            output_eff,
                            fn_span,
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    fn match_trait_output_effect(
        ty_inf: &mut UnifiedTypeInference,
        impl_eff: &EffType,
        requested_eff: &EffType,
        fn_span: Location,
    ) -> Result<(), InternalCompilationError> {
        let impl_eff = ty_inf.substitute_in_effect_type(impl_eff);
        let requested_eff = ty_inf.substitute_in_effect_type(requested_eff);
        // A single impl-side effect variable is an associated-effect alias and
        // must stay equal to the requested slot. Concrete or composite effects
        // are lower bounds: the requested slot may contain additional effects.
        if impl_eff.to_single_variable().is_some() {
            ty_inf.unify_same_effect(impl_eff, fn_span, requested_eff, fn_span)
        } else {
            ty_inf.add_effect_dep(&impl_eff, fn_span, &requested_eff, fn_span)
        }
    }

    fn type_var_capacity_for_types<'t>(types: impl IntoIterator<Item = &'t Type>) -> u32 {
        types
            .into_iter()
            .flat_map(TypeLike::inner_ty_vars)
            .map(|var| var.name() + 1)
            .max()
            .unwrap_or(0)
    }

    fn impl_matches_requested_outputs(
        &self,
        imp: &TraitImpl,
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        fn_span: Location,
    ) -> bool {
        if requested_output_tys.is_none() && requested_output_effs.is_none() {
            return true;
        }
        if requested_output_tys.is_some_and(|tys| tys.len() != imp.output_tys.len())
            || requested_output_effs.is_some_and(|effs| effs.len() != imp.output_effs.len())
        {
            return false;
        }

        let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(Self::type_var_capacity_for_types(
            imp.output_tys
                .iter()
                .chain(requested_output_tys.unwrap_or_default()),
        ));
        if let Some(requested_output_tys) = requested_output_tys {
            for (impl_ty, requested_ty) in imp.output_tys.iter().zip(requested_output_tys.iter()) {
                if ty_inf
                    .unify_same_type_with_sub_effects(*impl_ty, fn_span, *requested_ty, fn_span)
                    .is_err()
                {
                    return false;
                }
            }
        }
        if let Some(requested_output_effs) = requested_output_effs {
            for (impl_eff, requested_eff) in
                imp.output_effs.iter().zip(requested_output_effs.iter())
            {
                if Self::match_trait_output_effect(&mut ty_inf, impl_eff, requested_eff, fn_span)
                    .is_err()
                {
                    return false;
                }
            }
        }
        true
    }

    /// Try to improve a deferred trait application from its partially known
    /// inputs and optional known outputs.
    ///
    /// The algorithm probes every visible impl in a fresh scratch solver under
    /// a snapshot of the current unifier. If exactly one candidate remains
    /// compatible, it commits the visible equalities learned by that probe,
    /// even when some nested blanket constraints are still unresolved.
    #[allow(clippy::too_many_arguments)]
    fn improve_trait_application_match(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        let mut key_mapper = AlphaCanonicalTypeMapper::default();
        let key = TraitImprovementKey {
            trait_id,
            input_tys: ty_inf
                .substitute_in_types(input_tys)
                .into_iter()
                .map(|ty| ty.map(&mut key_mapper))
                .collect(),
            output_tys: output_tys.map(|output_tys| {
                ty_inf
                    .substitute_in_types(output_tys)
                    .into_iter()
                    .map(|ty| ty.map(&mut key_mapper))
                    .collect()
            }),
            output_effs: output_effs.map(|output_effs| {
                output_effs
                    .iter()
                    .map(|eff| {
                        let eff = ty_inf.substitute_in_effect_type(eff);
                        key_mapper.map_effect_type(&eff)
                    })
                    .collect()
            }),
        };
        if !self.active_improvements.insert(key.clone()) {
            return Ok(TraitImprovementMatch::Unknown);
        }
        let result = self.improve_trait_application_match_actual(
            ty_inf,
            trait_id,
            input_tys,
            output_tys,
            output_effs,
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
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        let candidates = self.improvement_candidates(trait_id);
        let original_vars = input_tys
            .iter()
            .chain(output_tys.unwrap_or_default().iter())
            .flat_map(TypeLike::inner_ty_vars)
            .collect::<FxHashSet<_>>();
        type Candidate = (
            TraitImprovementCandidate,
            TraitImprovementMatch,
            Vec<Type>,
            Option<Vec<Type>>,
        );
        let mut unique_candidate: Option<Candidate> = None;
        let mut found_multiple_candidates = false;

        for candidate in candidates {
            let snapshot = ty_inf.snapshot();
            // Concrete candidates only run unification against `ty_inf` and never reach `match_blanket_impl`, so they do not need a probe.
            // Skipping the probe avoids cloning the impl table once per concrete candidate, which is the dominant cost of this loop.
            let matched = match &candidate {
                TraitImprovementCandidate::Concrete { .. } => Self::improvement_candidate_matches(
                    &mut NeverProbe,
                    ty_inf,
                    &candidate,
                    input_tys,
                    output_tys,
                    output_effs,
                    assumptions,
                    fn_span,
                    arena,
                )?,
                TraitImprovementCandidate::Blanket { .. } => {
                    let mut query = LazyTraitSolverProbe::new(self);
                    Self::improvement_candidate_matches(
                        &mut query,
                        ty_inf,
                        &candidate,
                        input_tys,
                        output_tys,
                        output_effs,
                        assumptions,
                        fn_span,
                        arena,
                    )?
                }
            };
            let improved_input_tys = ty_inf.substitute_in_types(input_tys);
            let improved_output_tys =
                output_tys.map(|output_tys| ty_inf.substitute_in_types(output_tys));
            ty_inf.rollback_to(snapshot);
            use TraitImprovementMatch::*;
            match matched {
                No => {}
                Unknown | Yes => {
                    if unique_candidate.is_some() {
                        found_multiple_candidates = true;
                        unique_candidate = None;
                        continue;
                    }
                    unique_candidate =
                        Some((candidate, matched, improved_input_tys, improved_output_tys));
                }
            }
        }

        if found_multiple_candidates {
            return Ok(TraitImprovementMatch::Unknown);
        }
        let Some((candidate, matched, improved_input_tys, improved_output_tys)) = unique_candidate
        else {
            // A deriver may become applicable once the remaining variables are
            // fixed, so absence of a visible impl head is not a definite miss.
            if !self.trait_def(trait_id).derivers.is_empty()
                && !input_tys.iter().all(|ty| ty.is_trait_input_resolved())
            {
                return Ok(TraitImprovementMatch::Unknown);
            }
            return Ok(TraitImprovementMatch::No);
        };

        // Visible impl uniqueness is not conclusive while a trait with derivers
        // still has unresolved inputs: a derived impl may become applicable
        // once those inputs are fixed.
        if !self.trait_def(trait_id).derivers.is_empty()
            && !input_tys.iter().all(|ty| ty.is_trait_input_resolved())
        {
            return Ok(TraitImprovementMatch::Unknown);
        }

        match matched {
            TraitImprovementMatch::No => unreachable!(),
            TraitImprovementMatch::Unknown => {
                let improved_vars = improved_input_tys
                    .iter()
                    .chain(improved_output_tys.as_deref().unwrap_or_default().iter())
                    .flat_map(TypeLike::inner_ty_vars)
                    .collect::<FxHashSet<_>>();
                if improved_vars.is_subset(&original_vars) {
                    for (input_ty, improved_input_ty) in
                        input_tys.iter().zip(improved_input_tys.iter())
                    {
                        ty_inf.unify_same_type_with_sub_effects(
                            *input_ty,
                            fn_span,
                            *improved_input_ty,
                            fn_span,
                        )?;
                    }
                    if let (Some(output_tys), Some(improved_output_tys)) =
                        (output_tys, improved_output_tys.as_deref())
                    {
                        for (output_ty, improved_output_ty) in
                            output_tys.iter().zip(improved_output_tys.iter())
                        {
                            ty_inf.unify_same_type_with_sub_effects(
                                *output_ty,
                                fn_span,
                                *improved_output_ty,
                                fn_span,
                            )?;
                        }
                    }
                } else {
                    Self::improve_trait_application_with_candidate_head(
                        ty_inf,
                        &candidate,
                        input_tys,
                        output_tys,
                        output_effs,
                        fn_span,
                    )?;
                }
                Ok(TraitImprovementMatch::Unknown)
            }
            TraitImprovementMatch::Yes => Self::improvement_candidate_matches(
                self,
                ty_inf,
                &candidate,
                input_tys,
                output_tys,
                output_effs,
                assumptions,
                fn_span,
                arena,
            ),
        }
    }

    /// Try to improve a deferred trait application from its partially known
    /// inputs and outputs.
    ///
    /// The algorithm probes every visible impl in a fresh scratch solver under
    /// a snapshot of the current unifier. If exactly one candidate remains
    /// compatible, it commits the visible equalities learned by that probe,
    /// even when some nested blanket constraints are still unresolved.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn try_improve_trait_application(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<bool, InternalCompilationError> {
        Ok(matches!(
            self.improve_trait_application_match(
                ty_inf,
                trait_id,
                input_tys,
                output_tys,
                output_effs,
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
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
    ) -> bool {
        assumptions.iter().any(|assumption| {
            let PubTypeConstraint::HaveTrait {
                trait_id: assumption_trait_id,
                input_tys: assumption_input_tys,
                output_tys: assumption_output_tys,
                ..
            } = assumption
            else {
                return false;
            };
            if *assumption_trait_id != trait_id
                || assumption_input_tys.len() != input_tys.len()
                || output_tys
                    .is_some_and(|output_tys| assumption_output_tys.len() != output_tys.len())
            {
                return false;
            }

            let substituted_assumption = ty_inf.substitute_in_constraint(assumption);
            let Some((ass_trait_id, ass_input_tys, ass_output_tys, ass_output_effs, _)) =
                substituted_assumption.as_have_trait()
            else {
                return false;
            };
            if !ass_input_tys.iter().all(|ty| ty.is_trait_input_resolved())
                || !ass_output_tys.iter().all(|ty| ty.is_trait_input_resolved())
            {
                return false;
            }
            if *ass_trait_id != trait_id
                || ass_input_tys.len() != input_tys.len()
                || output_tys.is_some_and(|output_tys| ass_output_tys.len() != output_tys.len())
            {
                return false;
            }
            ass_input_tys == input_tys
                && output_tys.is_none_or(|output_tys| ass_output_tys == output_tys)
                && output_effs.is_none_or(|output_effs| ass_output_effs == output_effs)
        })
    }

    fn normalize_blanket_remaining_constraints(
        ty_inf: &mut UnifiedTypeInference,
        constraints: impl IntoIterator<Item = (usize, PubTypeConstraint)>,
    ) -> Vec<(usize, PubTypeConstraint)> {
        constraints
            .into_iter()
            .map(|(index, constraint)| (index, ty_inf.substitute_in_constraint(&constraint)))
            .collect()
    }

    #[cfg(debug_assertions)]
    fn assert_blanket_impl_is_well_formed(
        imp_input_tys: &[Type],
        imp_constraints: &[PubTypeConstraint],
        imp_ty_var_count: u32,
        _imp_eff_var_count: u32,
        input_tys: &[Type],
    ) {
        assert_eq!(imp_input_tys.len(), input_tys.len());
        let mut ty_vars = FxHashSet::default();
        let mut mut_vars = FxHashSet::default();
        let mut eff_vars = FxHashSet::default();
        {
            let mut collector = AllVarsCollector {
                ty_vars: &mut ty_vars,
                mut_vars: &mut mut_vars,
                effect_vars: &mut eff_vars,
            };
            for ty in imp_input_tys {
                ty.visit(&mut collector);
            }
        }
        {
            let mut collector = AllVarsCollector {
                ty_vars: &mut ty_vars,
                mut_vars: &mut mut_vars,
                effect_vars: &mut eff_vars,
            };
            for constraint in imp_constraints {
                constraint.visit(&mut collector);
            }
        }
        assert!(mut_vars.is_empty());
        assert_eq!(ty_vars.len(), imp_ty_var_count as usize);
    }

    /// Match a blanket impl head plus its impl constraints against a requested
    /// trait application.
    ///
    /// This is the shared fixed-point engine used by both normal blanket impl
    /// solving and trait improvement. It instantiates the blanket-local type
    /// variables, unifies the impl head with the requested types, unifies known
    /// requested outputs when present, then iterates the impl constraints until
    /// no more progress is possible.
    #[allow(clippy::too_many_arguments)]
    fn match_blanket_impl<Q: TraitOutputQuery>(
        query: &mut Q,
        ty_inf: &mut UnifiedTypeInference,
        imp_input_tys: &[Type],
        imp_output_tys: &[Type],
        imp_output_effs: &[EffType],
        imp_ty_var_count: u32,
        imp_eff_var_count: u32,
        imp_constraints: &[PubTypeConstraint],
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
        mode: BlanketConstraintMode,
    ) -> Result<BlanketImplMatch, InternalCompilationError> {
        // First instantiate the blanket-local type and effect variables with
        // fresh inference variables in the caller-provided unifier.
        let mut eff_subst = ty_inf.fresh_effect_var_subst(imp_eff_var_count);
        eff_subst.extend(ty_inf.fresh_effect_var_subst_for(imp_constraints, imp_output_effs));
        let inst_subst = (ty_inf.fresh_type_var_subst(imp_ty_var_count), eff_subst);
        let mut mapper = BitmapInstantiationMapper::new(&inst_subst);
        let imp_input_tys = instantiate_types(imp_input_tys, &mut mapper);
        let mut imp_output_tys = instantiate_types(imp_output_tys, &mut mapper);
        let mut imp_output_effs: Vec<_> = imp_output_effs
            .iter()
            .map(|eff| mapper.map_effect_type(eff))
            .collect();
        let remaining = instantiate_types(imp_constraints, &mut mapper)
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
                .unify_same_type_with_sub_effects(*imp_input_ty, fn_span, *input_ty, fn_span)
                .is_err()
            {
                return Ok(BlanketImplMatch::No);
            }
        }
        if let Some(output_tys) = output_tys {
            for (imp_output_ty, output_ty) in imp_output_tys.iter().zip(output_tys.iter()) {
                if ty_inf
                    .unify_same_type_with_sub_effects(*imp_output_ty, fn_span, *output_ty, fn_span)
                    .is_err()
                {
                    return Ok(BlanketImplMatch::No);
                }
            }
        }
        if let Some(output_effs) = output_effs {
            for (imp_output_eff, output_eff) in imp_output_effs.iter().zip(output_effs.iter()) {
                if Self::match_trait_output_effect(ty_inf, imp_output_eff, output_eff, fn_span)
                    .is_err()
                {
                    return Ok(BlanketImplMatch::No);
                }
            }
        }

        let mut remaining = Self::normalize_blanket_remaining_constraints(ty_inf, remaining);
        loop {
            let old_remaining = mem::take(&mut remaining);
            let mut still_remaining = Vec::new();

            for (constraint_index, constraint) in old_remaining.iter() {
                // Re-substitute the constraint on every pass because earlier
                // solved constraints may have refined the type variables it uses.
                let substituted_constraint = ty_inf.substitute_in_constraint(constraint);
                let Some((
                    trait_id,
                    constraint_inputs,
                    constraint_outputs,
                    constraint_output_effs,
                    _span,
                )) = substituted_constraint.as_have_trait()
                else {
                    debug_assert!(substituted_constraint.as_have_trait().is_none());
                    if let Some(unresolved) =
                        ty_inf.unify_structural_pub_constraint(&substituted_constraint)?
                    {
                        still_remaining.push((*constraint_index, unresolved));
                    }
                    continue;
                };
                let trait_id = *trait_id;
                let constraint_inputs = constraint_inputs.clone();
                let constraint_outputs = constraint_outputs.clone();
                let constraint_output_effs = constraint_output_effs.clone();
                if Self::match_assumption(
                    ty_inf,
                    trait_id,
                    &constraint_inputs,
                    Some(&constraint_outputs),
                    Some(&constraint_output_effs),
                    assumptions,
                ) {
                    continue;
                }
                if !constraint_inputs
                    .iter()
                    .all(|ty| ty.is_trait_input_resolved())
                {
                    if Self::input_tys_can_drive_improvement(&constraint_inputs) {
                        match query.improve_trait_application_query(
                            ty_inf,
                            trait_id,
                            &constraint_inputs,
                            Some(&constraint_outputs),
                            Some(&constraint_output_effs),
                            assumptions,
                            fn_span,
                            arena,
                        )? {
                            TraitImprovementMatch::No => return Ok(BlanketImplMatch::No),
                            TraitImprovementMatch::Unknown => {}
                            TraitImprovementMatch::Yes => {}
                        }
                    }
                    still_remaining.push((*constraint_index, substituted_constraint));
                    continue;
                }
                let (solved_outputs, solved_output_effs) = if query
                    .is_compiler_provided_no_output_trait_query(
                        trait_id,
                        &constraint_inputs,
                        &constraint_outputs,
                        &constraint_output_effs,
                    ) {
                    (Vec::new(), Vec::new())
                } else {
                    match query.solve_outputs_query(trait_id, &constraint_inputs, fn_span, arena) {
                        Ok(outputs) => outputs,
                        Err(_)
                            if matches!(mode, BlanketConstraintMode::DeferConcreteObligations) =>
                        {
                            still_remaining.push((*constraint_index, substituted_constraint));
                            continue;
                        }
                        Err(_) => return Ok(BlanketImplMatch::No),
                    }
                };
                for (solved_output, constraint_output) in
                    solved_outputs.iter().zip(constraint_outputs.iter())
                {
                    if ty_inf
                        .unify_same_type_with_sub_effects(
                            *solved_output,
                            fn_span,
                            *constraint_output,
                            fn_span,
                        )
                        .is_err()
                    {
                        return Ok(BlanketImplMatch::No);
                    }
                }
                for (solved_output_eff, constraint_output_eff) in
                    solved_output_effs.iter().zip(constraint_output_effs.iter())
                {
                    if ty_inf
                        .add_effect_dep(solved_output_eff, fn_span, constraint_output_eff, fn_span)
                        .is_err()
                    {
                        return Ok(BlanketImplMatch::No);
                    }
                }
                resolved_constraints.push(ResolvedTraitConstraint {
                    index: *constraint_index,
                    trait_id,
                    input_tys: constraint_inputs,
                    output_tys: constraint_outputs,
                    output_effs: constraint_output_effs,
                });
            }

            // Fixed point reached: either all nested constraints are solved or
            // we have to stop according to the caller's mode.
            if still_remaining.is_empty() {
                break;
            }

            let still_remaining =
                Self::normalize_blanket_remaining_constraints(ty_inf, still_remaining);
            if still_remaining == old_remaining {
                match mode {
                    BlanketConstraintMode::RequireAllResolved => {
                        return Ok(BlanketImplMatch::No);
                    }
                    BlanketConstraintMode::AllowUnknown => {
                        return Ok(BlanketImplMatch::Unknown);
                    }
                    BlanketConstraintMode::DeferConcreteObligations => {
                        for (constraint_index, constraint) in still_remaining {
                            let substituted_constraint =
                                ty_inf.substitute_in_constraint(&constraint);
                            let Some((
                                trait_id,
                                constraint_inputs,
                                constraint_outputs,
                                constraint_output_effs,
                                _span,
                            )) = substituted_constraint.as_have_trait()
                            else {
                                return Ok(BlanketImplMatch::No);
                            };
                            let trait_id = *trait_id;
                            let constraint_inputs = constraint_inputs.clone();
                            let constraint_outputs = constraint_outputs.clone();
                            let constraint_output_effs = constraint_output_effs.clone();
                            if !constraint_inputs
                                .iter()
                                .all(|ty| ty.is_trait_input_resolved())
                            {
                                return Ok(BlanketImplMatch::No);
                            }
                            resolved_constraints.push(ResolvedTraitConstraint {
                                index: constraint_index,
                                trait_id,
                                input_tys: constraint_inputs,
                                output_tys: constraint_outputs,
                                output_effs: constraint_output_effs,
                            });
                        }
                        break;
                    }
                }
            }

            remaining = still_remaining;
        }

        // Finally, unify the instantiated blanket outputs with the requested
        // outputs if the caller supplied them, then return the resolved nested
        // trait constraints in source order.
        if let Some(output_tys) = output_tys {
            for (imp_output_ty, output_ty) in imp_output_tys.iter().zip(output_tys.iter()) {
                if ty_inf
                    .unify_same_type_with_sub_effects(*imp_output_ty, fn_span, *output_ty, fn_span)
                    .is_err()
                {
                    return Ok(BlanketImplMatch::No);
                }
            }
        }
        if let Some(output_effs) = output_effs {
            for (imp_output_eff, output_eff) in imp_output_effs.iter().zip(output_effs.iter()) {
                if Self::match_trait_output_effect(ty_inf, imp_output_eff, output_eff, fn_span)
                    .is_err()
                {
                    return Ok(BlanketImplMatch::No);
                }
            }
        }

        resolved_constraints.sort_by_key(|constraint| constraint.index);
        if ty_inf.finalize_effect_dependencies().is_err() {
            return Ok(BlanketImplMatch::No);
        }
        ty_inf.substitute_in_types_in_place(&mut imp_output_tys);
        ty_inf.substitute_in_effect_types_in_place(&mut imp_output_effs);
        Ok(BlanketImplMatch::Yes {
            output_tys: imp_output_tys,
            output_effs: imp_output_effs,
            resolved_constraints,
        })
    }

    /// Commit newly created pending functions as module placeholders.
    /// This must be called after trait solving is done,
    /// otherwise the created functions will be lost.
    pub fn commit(
        mut self,
        functions: &mut Vec<ModuleFunction>,
        def_table: &mut DefTable,
        pending_functions: &mut FxHashMap<LocalFunctionId, PendingModuleFunction>,
    ) -> Vec<LocalFunctionId> {
        let mut ids = Vec::with_capacity(self.fn_collector.new_elements.len());
        for (name, function, visibility) in self.fn_collector.new_elements.drain(..) {
            let id = LocalFunctionId::from_index(functions.len());
            def_table.insert(name, Def::new(DefKind::Function(id), visibility));
            let function = function.expect("committing a reserved generated function without code");
            functions.push(function.placeholder());
            pending_functions.insert(id, function);
            ids.push(id);
        }
        ids
    }

    /// Add a concrete trait implementation from the given code body, for single-function traits.
    pub(crate) fn add_concrete_impl_from_code(
        &mut self,
        body: PendingFunctionBody,
        locals: Vec<LocalDecl>,
        trait_id: TraitId,
        input_types: impl Into<Vec<Type>>,
        output_types: impl Into<Vec<Type>>,
    ) -> LocalImplId {
        let trait_def = trait_def_from_parts(
            self.current_type_defs.module_id,
            self.current_traits,
            self.others,
            trait_id,
        );
        let input_types = input_types.into();
        let output_types = output_types.into();
        let output_effs = trait_def.impl_output_effs_or_pure_defaults(vec![]);
        let definitions = trait_def.instantiate_for_tys(&input_types, &output_types, &output_effs);
        let definition = definitions
            .into_iter()
            .next()
            .expect("single-function trait should have one method");
        let runtime_arg_count = definition.arg_names.len();
        let function =
            PendingModuleFunction::from_body(definition, body, runtime_arg_count, None, locals);
        self.impls.add_concrete_pending(
            trait_id,
            trait_def,
            input_types,
            output_types,
            output_effs,
            [],
            vec![function],
            &mut self.fn_collector,
        )
    }

    pub(crate) fn snapshot_derived_impl_state(&self) -> DerivedImplSnapshot {
        DerivedImplSnapshot {
            concrete_key_to_id: self.impls.concrete_key_to_id.clone(),
            blanket_key_to_id: self.impls.blanket_key_to_id.clone(),
            impl_data_len: self.impls.data.len(),
            new_function_len: self.fn_collector.new_elements.len(),
        }
    }

    pub(crate) fn rollback_derived_impl_state(&mut self, snapshot: DerivedImplSnapshot) {
        self.impls.concrete_key_to_id = snapshot.concrete_key_to_id;
        self.impls.blanket_key_to_id = snapshot.blanket_key_to_id;
        self.impls.data.truncate(snapshot.impl_data_len);
        self.fn_collector
            .new_elements
            .truncate(snapshot.new_function_len);
    }

    pub(crate) fn reserve_concrete_impl_from_code_entries(
        &mut self,
        trait_id: TraitId,
        input_types: &[Type],
        output_types: &[Type],
        output_effs: &[EffType],
        associated_const_values: impl Into<Vec<LiteralValue>>,
    ) -> LocalImplId {
        let associated_const_values = associated_const_values.into();
        let trait_def = trait_def_from_parts(
            self.current_type_defs.module_id,
            self.current_traits,
            self.others,
            trait_id,
        );
        trait_def.validate_impl_shape(
            input_types,
            output_types,
            output_effs,
            associated_const_values.len(),
            trait_def.methods.len(),
        );
        let definitions = trait_def.instantiate_for_tys(input_types, output_types, output_effs);
        let mut methods = Vec::with_capacity(definitions.len());
        let mut tys = Vec::with_capacity(definitions.len());

        for (method_index, definition) in definitions.into_iter().enumerate() {
            let method_index = TraitMethodIndex::from_index(method_index);
            let id = self.fn_collector.next_id();
            let ty = Type::function_type(definition.ty_scheme.ty.clone());
            let name = trait_def
                .qualified_method_name(method_index, input_types)
                .into();
            self.fn_collector.reserve(name);
            methods.push(id);
            tys.push(ty);
        }

        let associated_const_tys = trait_def.instantiate_associated_const_tys_for_tys(
            input_types,
            output_types,
            output_effs,
        );
        let dictionary_ty = TraitImpls::dictionary_ty(tys, associated_const_tys);
        let dictionary_value = build_dictionary_value(&methods, &associated_const_values);
        let imp = TraitImpl::new(
            output_types.to_vec(),
            output_effs.to_vec(),
            methods,
            dictionary_value,
            dictionary_ty,
            false,
            None,
        )
        .with_associated_const_values(associated_const_values);
        let key = ConcreteTraitImplKey::new(trait_id, input_types.to_vec());
        self.impls.add_concrete_struct(key, imp)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn replace_concrete_impl_code_entries(
        &mut self,
        impl_id: LocalImplId,
        trait_id: TraitId,
        input_types: &[Type],
        output_types: &[Type],
        output_effs: &[EffType],
        code_entries: impl Into<Vec<(PendingFunctionBody, Vec<LocalDecl>)>>,
    ) {
        let methods = self.impls.data[impl_id.as_index()].methods.clone();
        let trait_def = trait_def_from_parts(
            self.current_type_defs.module_id,
            self.current_traits,
            self.others,
            trait_id,
        );
        let definitions = trait_def.instantiate_for_tys(input_types, output_types, output_effs);

        for ((method_id, definition), (body, locals)) in methods
            .into_iter()
            .zip(definitions)
            .zip(code_entries.into())
        {
            let runtime_arg_count = definition.arg_names.len();
            self.fn_collector.replace(
                method_id,
                PendingModuleFunction::from_body(definition, body, runtime_arg_count, None, locals),
            );
        }
    }

    fn blanket_method_thunk_code_entry(
        &mut self,
        function_id: FunctionId,
        definition: &FunctionDefinition,
        constraint_dict_infos: &[(NodeKind, Type)],
        fn_span: Location,
    ) -> Result<(PendingFunctionBody, Vec<LocalDecl>), InternalCompilationError> {
        let locals = definition.gen_locals_no_bounds(
            repeat(Location::new_synthesized()),
            Location::new_synthesized(),
        );
        let mut body_arena = NodeArena::default();

        let constraint_dict_nodes = constraint_dict_infos
            .iter()
            .map(|(kind, ty)| {
                body_arena.alloc(Node::new(
                    kind.clone(),
                    *ty,
                    EffType::empty(),
                    Location::new_synthesized(),
                ))
            })
            .collect();

        let argument_values = definition
            .ty_scheme
            .ty
            .args
            .iter()
            .enumerate()
            .map(|(arg_i, arg_ty)| {
                let id = LocalDeclId::from_index(arg_i);
                body_arena.alloc(Node::new(
                    load_local(id),
                    arg_ty.ty,
                    EffType::empty(),
                    fn_span,
                ))
            })
            .collect();
        let argument_passing = self.resolved_arg_passing_for_no_temp_args(
            &mut body_arena,
            &definition.ty_scheme.ty.args,
            fn_span,
        )?;
        let arguments = CallArgument::from_values_and_passing(argument_values, argument_passing);

        let apply = NodeKind::StaticApply(b(StaticApplication {
            function: function_id,
            function_path: None,
            function_span: fn_span,
            extra_arguments: constraint_dict_nodes,
            argument_names: definition.arg_names.clone(),
            arguments,
            ty: definition.ty_scheme.ty.clone(),
            inst_data: FnInstData::none(),
        }));
        let apply_id = body_arena.alloc(Node::new(
            apply,
            definition.ty_scheme.ty.ret,
            EffType::empty(),
            fn_span,
        ));
        Ok((PendingFunctionBody::new(body_arena, apply_id), locals))
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
                        self.can_use_other_impl(module.module_id(), &impls.data[id.as_index()])
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
                    if self.can_use_other_impl(module_id, imp) {
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

    /// Get the blanket trait implementations for the given trait id, without performing any solving.
    /// This searches in other modules first, then in the current module.
    fn get_blanket_impls<'s: 'b, 'b>(
        &'s self,
        trait_id: TraitId,
    ) -> impl Iterator<Item = (Option<ModuleId>, &'b BlanketTraitImpls)> + use<'b> {
        self.impls
            .blanket_key_to_id
            .get(&trait_id)
            .map(|blankets| (None, blankets))
            .into_iter()
            .chain(
                self.others
                    .enumerates()
                    .flat_map(move |(module_id, entry, _)| {
                        entry.module().and_then(|module| {
                            module
                                .impls
                                .blanket_key_to_id
                                .get(&trait_id)
                                .map(|imp| (Some(module_id), imp))
                        })
                    }),
            )
    }

    /// Print all known implementations for the given trait id.
    fn log_debug_impls(&self, trait_id: TraitId) {
        log::debug!("In current module:");
        let mut fake_current = Module::new(self.current_type_defs.module_id);
        fake_current.traits = self.current_traits.to_vec();
        let env = ModuleEnv::new(&fake_current, self.others);
        self.impls.log_debug_impls_headers(trait_id, env);
        for (module_path, entry) in self.others.iter_named() {
            if let Some(module) = &entry.module {
                let impls = &module.impls;
                if impls.blanket_key_to_id.contains_key(&trait_id) {
                    log::debug!("In module {}:", module_path);
                    impls.log_debug_impls_headers(trait_id, env);
                }
            }
        }
    }

    pub(crate) fn materialize_generated_value_impl_from_methods(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        span: Location,
        methods: Vec<LocalFunctionId>,
    ) -> Result<(TraitImplId, Type), InternalCompilationError> {
        let (method_tys, associated_const_tys, dictionary_ty_for_use) = {
            let trait_def = self.trait_def(trait_id);
            assert_eq!(methods.len(), trait_def.methods.len());
            let definitions = trait_def.instantiate_for_tys(input_tys, &[], &[]);
            let method_tys = definitions
                .into_iter()
                .map(|definition| Type::function_type(definition.ty_scheme.ty))
                .collect::<Vec<_>>();
            let associated_const_tys =
                trait_def.instantiate_associated_const_tys_for_tys(input_tys, &[], &[]);
            let dictionary_ty_for_use = trait_def.get_dictionary_type_for_tys(input_tys, &[], &[]);
            (method_tys, associated_const_tys, dictionary_ty_for_use)
        };
        let associated_const_values =
            value_layout_associated_const_values(input_tys[0], span, self)?;
        let associated_const_values = associated_const_values
            .into_iter()
            .map(LiteralValue::new_native)
            .collect::<Vec<_>>();
        let dictionary_ty = TraitImpls::dictionary_ty(method_tys, associated_const_tys);
        let dictionary_value = build_dictionary_value(&methods, &associated_const_values);
        let imp = TraitImpl::new(
            Vec::new(),
            Vec::new(),
            methods,
            dictionary_value,
            dictionary_ty,
            false,
            None,
        )
        .with_associated_const_values(associated_const_values);
        let impl_id = if input_tys.iter().all(Type::is_constant) {
            let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
            if let Some(impl_id) = self.impls.concrete().get(&key).copied() {
                impl_id
            } else {
                self.impls.add_concrete_struct(key, imp)
            }
        } else {
            self.impls.add_anonymous_dictionary_struct(imp)
        };
        Ok((TraitImplId::Local(impl_id), dictionary_ty_for_use))
    }

    fn compiler_provided_value_dictionary_node_kind(
        &mut self,
        arena: &mut NodeArena,
        trait_id: TraitId,
        input_tys: &[Type],
        span: Location,
    ) -> Result<(NodeKind, Type), InternalCompilationError> {
        let trait_def = self.trait_def(trait_id);
        let methods = if is_value_trait_for_function_type(trait_id, trait_def, input_tys, &[]) {
            let method_count = trait_def.methods.len();
            (0..method_count)
                .map(TraitMethodIndex::from_index)
                .map(|method_index| function_value_method(self, method_index, span))
                .collect::<Result<Vec<_>, _>>()?
        } else {
            generic_value_methods_for_type(self, trait_id, input_tys, span, arena)?
        };
        let (impl_id, dictionary_ty) =
            self.materialize_generated_value_impl_from_methods(trait_id, input_tys, span, methods)?;
        Ok((get_dictionary(impl_id), dictionary_ty))
    }

    fn materialize_constraint_dictionary_infos(
        &mut self,
        resolved_constraints: impl IntoIterator<Item = ResolvedTraitConstraint>,
        fn_span: Location,
        arena: &mut NodeArena,
        validate_outputs: bool,
    ) -> Result<Option<Vec<(NodeKind, Type)>>, InternalCompilationError> {
        let mut constraint_dict_infos = Vec::new();
        for resolved_constraint in resolved_constraints {
            // Marker traits have no runtime dictionary entries.
            if !self
                .trait_def(resolved_constraint.trait_id)
                .has_runtime_dictionary_entries()
            {
                continue;
            }
            if self.is_compiler_provided_no_output_trait_query(
                resolved_constraint.trait_id,
                &resolved_constraint.input_tys,
                &resolved_constraint.output_tys,
                &resolved_constraint.output_effs,
            ) {
                let info = self.compiler_provided_value_dictionary_node_kind(
                    arena,
                    resolved_constraint.trait_id,
                    &resolved_constraint.input_tys,
                    fn_span,
                )?;
                constraint_dict_infos.push(info);
                continue;
            }
            let dict_id = match self.solve_impl(
                resolved_constraint.trait_id,
                &resolved_constraint.input_tys,
                fn_span,
                arena,
            ) {
                Ok(functions) => functions,
                Err(err) => {
                    log::debug!(
                        "Blanket impl constraint failed while solving {} for {:?}: {:?}",
                        self.trait_def(resolved_constraint.trait_id).name,
                        resolved_constraint.input_tys,
                        err
                    );
                    return Ok(None);
                }
            };
            let dict_impl_data = self.get_impl_data_by_id(dict_id);
            if validate_outputs
                && (dict_impl_data.output_tys != resolved_constraint.output_tys
                    || !dict_impl_data
                        .output_effs
                        .iter()
                        .zip(resolved_constraint.output_effs.iter())
                        .all(|(solved_eff, constraint_eff)| solved_eff == constraint_eff))
            {
                return Ok(None);
            }
            constraint_dict_infos.push((get_dictionary(dict_id), dict_impl_data.dictionary_ty));
        }
        Ok(Some(constraint_dict_infos))
    }

    /// Get a concrete trait implementation for the given trait id and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If matching blanket implementation is found, a derivation is attempted, if available.
    /// Otherwise an error is returned.
    /// This is the trait solver's core function.
    pub fn solve_impl(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImplId, InternalCompilationError> {
        self.solve_impl_application(trait_id, input_tys, None, None, fn_span, arena)
    }

    #[allow(clippy::too_many_arguments)]
    fn solve_impl_application(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImplId, InternalCompilationError> {
        // Sanity checks
        assert!(
            input_tys.iter().all(|ty| ty.is_trait_input_resolved()),
            "Getting trait implementation for unresolved input type shapes"
        );

        // Cycle detection
        let key = (trait_id, input_tys.to_vec());
        let concrete_key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
        if let Some(imp) = self.get_concrete_impl(&concrete_key) {
            if self.impl_matches_requested_outputs(
                self.get_impl_data_by_id(imp),
                requested_output_tys,
                requested_output_effs,
                fn_span,
            ) {
                return Ok(imp);
            }
        }
        if self.solving_stack.contains(&key) {
            return Err(internal_compilation_error!(TraitSolverCycleDetected {
                trait_ref: trait_id,
                input_tys: input_tys.to_vec(),
                fn_span,
            }));
        }

        // Recursion limit check
        if self.recursion_depth > TRAIT_SOLVER_RECURSION_LIMIT {
            return Err(internal_compilation_error!(
                TraitSolverRecursionLimitExceeded {
                    trait_ref: trait_id,
                    input_tys: input_tys.to_vec(),
                    fn_span,
                }
            ));
        }

        self.recursion_depth += 1;
        self.solving_stack.insert(key.clone());

        let result = self.solve_impl_actual(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            fn_span,
            arena,
        );

        self.solving_stack.remove(&key);
        self.recursion_depth -= 1;
        result
    }

    fn solve_impl_actual(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImplId, InternalCompilationError> {
        let value_trait_id = self.std_trait_id(VALUE_TRAIT_NAME);
        // Special case for `Repr` trait.
        if trait_id == self.std_trait_id(REPR_TRAIT_NAME) {
            let input_ty = input_tys[0];
            let ty_data = input_ty.data();
            let output_ty = if ty_data.is_named() {
                let named = ty_data.as_named().unwrap().clone();
                self.reject_inaccessible_private_repr(named.def, fn_span)?;
                self.type_def(named.def)
                    .instantiated_shape_with_effects(&named.params, &named.effect_params)
            } else {
                input_ty
            };

            // Only search in current module, create a new implementation if not found.
            let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
            let local_id = if let Some(id) = self.impls.concrete_key_to_id.get(&key) {
                *id
            } else {
                let imp = TraitImpl {
                    output_tys: vec![output_ty],
                    output_effs: vec![],
                    methods: vec![],
                    associated_const_values: vec![],
                    dictionary_value: TraitDictionary::new(&[], &[]),
                    dictionary_ty: Type::tuple([]),
                    public: false,
                    source_span: None,
                };
                self.impls.add_concrete_struct(key, imp)
            };
            return Ok(TraitImplId::Local(local_id));
        }

        // If a concrete implementation is found, return it.
        let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
        if let Some(imp) = self.get_concrete_impl(&key) {
            if self.impl_matches_requested_outputs(
                self.get_impl_data_by_id(imp),
                requested_output_tys,
                requested_output_effs,
                fn_span,
            ) {
                return Ok(imp);
            }
        }

        // No concrete implementation found, search for a matching blanket implementation.
        // We first clone all blanket implementations to avoid borrowing issues.
        let blankets = self
            .get_blanket_impls(trait_id)
            .map(|(module_id, blankets)| (module_id, blankets.clone()))
            .collect::<Vec<_>>();
        // Then we iterate over all blanket implementations, trying to unify their input types
        for (imp_module_id, blanket_impls) in blankets {
            'impl_loop: for (sub_key, impl_id) in blanket_impls.iter() {
                let imp_input_tys = &sub_key.input_tys;
                let imp_ty_var_count = sub_key.ty_var_count;
                let imp_eff_var_count = sub_key.eff_var_count;
                let imp_constraints = &sub_key.constraints;
                let (imp_public, imp_output_tys, imp_output_effs) =
                    if let Some(module_id) = imp_module_id {
                        let imp = &self
                            .others
                            .get(module_id)
                            .unwrap()
                            .module
                            .as_ref()
                            .unwrap()
                            .impls
                            .data[impl_id.as_index()];
                        (
                            self.can_use_other_impl(module_id, imp),
                            imp.output_tys.clone(),
                            imp.output_effs.clone(),
                        )
                    } else {
                        let imp = &self.impls.data[impl_id.as_index()];
                        (true, imp.output_tys.clone(), imp.output_effs.clone())
                    };
                if !imp_public {
                    continue 'impl_loop;
                }
                if let Some(module_id) = imp_module_id {
                    self.private_impl_scope.push(module_id);
                }
                macro_rules! continue_impl_loop {
                    () => {{
                        if imp_module_id.is_some() {
                            self.private_impl_scope.pop();
                        }
                        continue 'impl_loop;
                    }};
                }

                // Sanity checks
                #[cfg(debug_assertions)]
                Self::assert_blanket_impl_is_well_formed(
                    imp_input_tys,
                    imp_constraints,
                    imp_ty_var_count,
                    imp_eff_var_count,
                    input_tys,
                );

                // Match the blanket implementation and resolve the blanket constraints to a
                // fixed point before materializing the concrete implementation.
                let mut ty_inf =
                    UnifiedTypeInference::new_with_ty_vars(Self::type_var_capacity_for_types(
                        input_tys
                            .iter()
                            .chain(requested_output_tys.unwrap_or_default()),
                    ));
                let blanket_constraint_mode = if trait_id == value_trait_id {
                    BlanketConstraintMode::DeferConcreteObligations
                } else {
                    BlanketConstraintMode::RequireAllResolved
                };
                let blanket_match = Self::match_blanket_impl(
                    self,
                    &mut ty_inf,
                    imp_input_tys,
                    &imp_output_tys,
                    &imp_output_effs,
                    imp_ty_var_count,
                    imp_eff_var_count,
                    imp_constraints,
                    input_tys,
                    requested_output_tys,
                    requested_output_effs,
                    ConstraintAssumptions::all(&[]),
                    fn_span,
                    arena,
                    blanket_constraint_mode,
                )?;
                let BlanketImplMatch::Yes {
                    output_tys,
                    output_effs,
                    resolved_constraints,
                } = blanket_match
                else {
                    continue_impl_loop!();
                };
                let output_effs_depend_on_application =
                    output_effs.iter().any(EffType::has_variables);
                // The matched impl is being materialized for constant input types:
                // any output effect variable left unbound by the head and constraint
                // solving is unconstrained, so it resolves to the empty (pure) effect.
                let output_effs: Vec<_> = output_effs
                    .iter()
                    .map(|eff| EffType::multiple_primitive(&eff.inner_non_vars()))
                    .collect();

                // Non-Value blanket impls can materialize all constraint dictionaries up front.
                if trait_id != value_trait_id {
                    let Some(constraint_dict_infos) = self
                        .materialize_constraint_dictionary_infos(
                            resolved_constraints,
                            fn_span,
                            arena,
                            // `match_blanket_impl` already validated nested outputs against the
                            // current unifier; rechecking here is too strict for effect variables
                            // that are intentionally left to the caller's effect solver.
                            false,
                        )?
                    else {
                        continue_impl_loop!();
                    };

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
                    let associated_const_values = {
                        let trait_def = trait_def_from_parts(
                            self.current_type_defs.module_id,
                            self.current_traits,
                            self.others,
                            trait_id,
                        );
                        materialized_associated_const_values(
                            trait_id,
                            trait_def,
                            input_tys,
                            &imp.associated_const_values,
                            fn_span,
                            self,
                        )?
                    };

                    // Then, for every function in the blanket implementation, if needed create a thunk function
                    // importing it and closing over the constraint dictionaries.
                    let trait_key =
                        TraitKey::Blanket(BlanketTraitImplKey::new(trait_id, sub_key.clone()));
                    let trait_def = trait_def_from_parts(
                        self.current_type_defs.module_id,
                        self.current_traits,
                        self.others,
                        trait_id,
                    );
                    let definitions =
                        trait_def.instantiate_for_tys(input_tys, &output_tys, &output_effs);
                    let gen_functions = imp.methods.clone(); // clone to avoid borrowing issues
                    let mut methods = Vec::with_capacity(gen_functions.len());
                    let mut tys = Vec::with_capacity(gen_functions.len());
                    for (method_index, (fn_id, def)) in
                        gen_functions.iter().zip(definitions).enumerate()
                    {
                        let method_index = TraitMethodIndex::from_index(method_index);
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
                                        method_index,
                                    );
                                    FunctionId::Import(slot_id)
                                }
                                None => FunctionId::Local(*fn_id),
                            };

                            let (body, locals) = self.blanket_method_thunk_code_entry(
                                function_id,
                                &def,
                                &constraint_dict_infos,
                                fn_span,
                            )?;
                            let runtime_arg_count = def.arg_names.len();
                            let function = PendingModuleFunction::from_body(
                                def,
                                body,
                                runtime_arg_count,
                                None,
                                locals,
                            );
                            let name = Ustr::from(&format!(
                                "{}-thunk",
                                trait_def.qualified_method_name(method_index, input_tys)
                            ));
                            let id = self.fn_collector.next_id();
                            self.fn_collector.push(name, function);
                            id
                        };

                        methods.push(id);
                        tys.push(fn_ty);
                    }

                    // Build and insert the implementation.
                    let associated_const_tys = trait_def.instantiate_associated_const_tys_for_tys(
                        input_tys,
                        &output_tys,
                        &output_effs,
                    );
                    let dictionary_ty = TraitImpls::dictionary_ty(tys, associated_const_tys);
                    let dictionary_value =
                        build_dictionary_value(&methods, &associated_const_values);
                    let imp = TraitImpl::new(
                        output_tys,
                        output_effs,
                        methods,
                        dictionary_value,
                        dictionary_ty,
                        false,
                        None,
                    )
                    .with_associated_const_values(associated_const_values);
                    let local_impl_id = if output_effs_depend_on_application {
                        // Concrete impl lookup is keyed only by input types. If
                        // output effects still had variables before the
                        // materialized dictionary defaulted them, caching this
                        // impl would make that default leak into later
                        // applications with different output-effect bindings.
                        self.impls.add_anonymous_dictionary_struct(imp)
                    } else {
                        let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
                        self.impls.add_concrete_struct(key, imp)
                    };

                    if imp_module_id.is_some() {
                        self.private_impl_scope.pop();
                    }
                    return Ok(TraitImplId::Local(local_impl_id));
                }

                // Value blanket impls may be recursive, so reserve the concrete impl before
                // materializing any deferred constraint dictionaries.
                let (imp_associated_const_values, gen_functions) =
                    if let Some(module_id) = imp_module_id {
                        let imp = &self
                            .others
                            .get(module_id)
                            .unwrap()
                            .module
                            .as_ref()
                            .unwrap()
                            .impls
                            .data[impl_id.as_index()];
                        (imp.associated_const_values.clone(), imp.methods.clone())
                    } else {
                        let imp = &self.impls.data[impl_id.as_index()];
                        (imp.associated_const_values.clone(), imp.methods.clone())
                    };
                let associated_const_values = {
                    let trait_def = trait_def_from_parts(
                        self.current_type_defs.module_id,
                        self.current_traits,
                        self.others,
                        trait_id,
                    );
                    materialized_associated_const_values(
                        trait_id,
                        trait_def,
                        input_tys,
                        &imp_associated_const_values,
                        fn_span,
                        self,
                    )?
                };
                let materialization_snapshot = self.snapshot_derived_impl_state();
                let local_impl_id = self.reserve_concrete_impl_from_code_entries(
                    trait_id,
                    input_tys,
                    &output_tys,
                    &output_effs,
                    associated_const_values,
                );

                // Now that recursive self-references can resolve to the reserved impl,
                // materialize the deferred constraint dictionaries.
                let Some(constraint_dict_infos) = self.materialize_constraint_dictionary_infos(
                    resolved_constraints,
                    fn_span,
                    arena,
                    // Recursive `Value` materialization reserves a concrete impl before
                    // resolving dictionaries, so keep the pre-existing post-check.
                    true,
                )?
                else {
                    self.rollback_derived_impl_state(materialization_snapshot);
                    continue_impl_loop!();
                };

                // Then, for every function in the blanket implementation, if needed create a thunk function
                // importing it and closing over the constraint dictionaries.
                let trait_key =
                    TraitKey::Blanket(BlanketTraitImplKey::new(trait_id, sub_key.clone()));
                let definitions = trait_def_from_parts(
                    self.current_type_defs.module_id,
                    self.current_traits,
                    self.others,
                    trait_id,
                )
                .instantiate_for_tys(input_tys, &output_tys, &output_effs);
                let code_entries = gen_functions
                    .iter()
                    .zip(definitions)
                    .enumerate()
                    .map(|(method_index, (fn_id, def))| {
                        let method_index = TraitMethodIndex::from_index(method_index);
                        let function_id = match imp_module_id {
                            Some(module_id) => {
                                let slot_id = self.import_impl_method(
                                    module_id,
                                    trait_key.clone(),
                                    method_index,
                                );
                                FunctionId::Import(slot_id)
                            }
                            None => FunctionId::Local(*fn_id),
                        };

                        self.blanket_method_thunk_code_entry(
                            function_id,
                            &def,
                            &constraint_dict_infos,
                            fn_span,
                        )
                    })
                    .collect::<Result<Vec<_>, InternalCompilationError>>()?;

                self.replace_concrete_impl_code_entries(
                    local_impl_id,
                    trait_id,
                    input_tys,
                    &output_tys,
                    &output_effs,
                    code_entries,
                );

                if imp_module_id.is_some() {
                    self.private_impl_scope.pop();
                }
                return Ok(TraitImplId::Local(local_impl_id));
            }
        }

        // No blanket implementation found, look for a derived implementation.
        let (trait_name, derivers) = {
            let trait_def = self.trait_def(trait_id);
            (trait_def.name, trait_def.derivers.clone())
        };
        for derive in derivers {
            if let Some(impl_id) = derive.derive_impl(trait_id, input_tys, fn_span, arena, self)? {
                return Ok(impl_id);
            } else {
                log::debug!(
                    "Tried derivation for trait {} with input types {:?}, but failed.",
                    trait_name,
                    input_tys
                );
            }
        }

        // No matching implementation found.
        log::debug!(
            "No matching impl for trait \"{}\" found. Existing impls:",
            trait_name
        );
        self.log_debug_impls(trait_id);
        Err(internal_compilation_error!(TraitImplNotFound {
            trait_ref: trait_id,
            input_tys: input_tys.to_vec(),
            fn_span,
        }))
    }

    /// Get a specific method implementation for the given trait id and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If matching blanket implementation is found, a derivation is attempted, if available.
    /// Otherwise an error is returned.
    /// This function is implemented using solve_impl.
    pub fn solve_impl_method(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        index: TraitMethodIndex,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<FunctionId, InternalCompilationError> {
        let impl_id = self.solve_impl(trait_id, input_tys, fn_span, arena)?;
        use TraitImplId::*;
        Ok(match impl_id {
            Local(id) => {
                FunctionId::Local(self.impls.data[id.as_index()].methods[index.as_index()])
            }
            Import(slot_id) => {
                let slot = &self.import_impl_slots[slot_id.as_index()];
                let module_id = slot.module;
                let key = slot.key.as_concrete().unwrap();
                let key = TraitKey::Concrete(key.clone());
                FunctionId::Import(self.import_impl_method(module_id, key, index))
            }
        })
    }

    /// Get the output types for the given trait id and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If matching blanket implementation is found, a derivation is attempted, if available.
    /// Otherwise an error is returned.
    /// This function is implemented using solve_impl.
    pub fn solve_output_types(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        let impl_id = self.solve_impl(trait_id, input_tys, fn_span, arena)?;
        Ok(self.get_impl_data_by_id(impl_id).output_tys.clone())
    }

    /// Get the output types and effects for the given trait id and input types.
    /// This function is implemented using solve_impl, like `solve_output_types`.
    pub fn solve_outputs(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        let impl_id = self.solve_impl(trait_id, input_tys, fn_span, arena)?;
        let impl_data = self.get_impl_data_by_id(impl_id);
        Ok((impl_data.output_tys.clone(), impl_data.output_effs.clone()))
    }

    /// Solve a full trait application.
    ///
    /// Impl identity is selected by trait id and resolved input types, but
    /// associated output types and effects are application parameters. They are
    /// matched against the selected impl for this application and must not be
    /// treated as canonical values of the input-keyed impl cache.
    pub fn solve_application_outputs(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: &[Type],
        requested_output_effs: &[EffType],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        let impl_id = self.solve_impl_application(
            trait_id,
            input_tys,
            Some(requested_output_tys),
            Some(requested_output_effs),
            fn_span,
            arena,
        )?;
        let impl_data = self.get_impl_data_by_id(impl_id);
        Ok((impl_data.output_tys.clone(), impl_data.output_effs.clone()))
    }

    pub fn solve_associated_const(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        associated_const_index: TraitAssociatedConstIndex,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<LiteralValue, InternalCompilationError> {
        assert!(
            associated_const_index.as_index() < self.trait_def(trait_id).associated_const_count(),
            "associated const index {} out of bounds for trait {}",
            associated_const_index,
            self.trait_def(trait_id).name
        );
        let impl_id = self.solve_impl(trait_id, input_tys, fn_span, arena)?;
        Ok(self
            .get_impl_data_by_id(impl_id)
            .associated_const_value(associated_const_index)
            .unwrap_or_else(|| {
                panic!(
                    "implementation of trait {} is missing associated const #{}",
                    self.trait_def(trait_id).name,
                    associated_const_index
                )
            }))
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
        method_index: TraitMethodIndex,
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
    fn is_compiler_provided_no_output_trait_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) -> bool {
        is_compiler_provided_no_output_trait_application(
            trait_id,
            self.trait_def(trait_id),
            input_tys,
            output_tys,
            output_effs,
        )
    }

    fn solve_outputs_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        self.solve_outputs(trait_id, input_tys, fn_span, arena)
    }

    fn improve_trait_application_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        self.improve_trait_application_match(
            ty_inf,
            trait_id,
            input_tys,
            output_tys,
            output_effs,
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
