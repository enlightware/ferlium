// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{borrow::Cow, iter::repeat, mem, rc::Rc};

use ustr::Ustr;

#[cfg(debug_assertions)]
use crate::types::type_visitor::AllVarsCollector;
use crate::{
    FxHashMap, FxHashSet, Location, Modules,
    ast::UnnamedArg,
    compiler::error::InternalCompilationError,
    containers::b,
    hir::{
        CallArgument, FnInstData, Node, NodeArena, NodeKind, StaticApplication,
        dictionary::DictionaryReq,
        emit_value_impl::{function_value_method, generic_value_methods_for_type},
        function::{CallableDefinition, arg_conventions_for_args},
        hir_syn::{get_dictionary, load_local},
        value::LiteralValue,
    },
    internal_compilation_error,
    module::{
        self, BlanketImpls, BlanketTraitImplSubKey, BlanketTraitImpls, CandidateSearch,
        ConcreteImpls, ConcreteTraitImplKey, CurrentTypeItems, DefTable,
        DictionaryEntryRequirements, FunctionId, LocalDecl, LocalDeclId, LocalFunctionId,
        LocalImplId, LocalTraitId, Module, ModuleEnv, ModuleId, PendingFunctionBody,
        PendingFunctionCollector, PendingModuleFunction, ProjectionKey, QualifiedNameEnv,
        ResolvedValueLayout, TraitDictionary, TraitId, TraitImpl, TraitImplId, TraitImpls,
        TypeDefId, Visibility, build_capturing_dictionary_value, build_dictionary_value,
        dictionary_capture_plan, id::Id,
    },
    std::{
        STD_MODULE_ID,
        core_traits_names::{REPR_TRAIT_NAME, TRIVIAL_COPY_TRAIT_NAME, VALUE_TRAIT_NAME},
        value::{
            TypeLayoutEnv, generated_value_evidence_types, generated_value_layout_getter,
            is_compiler_provided_value_trait_application,
            is_function_surface_only_value_trait_application, is_value_trait,
            is_value_trait_for_function_type, value_layout_associated_const_values,
            value_layout_for_type, value_layout_getter_evidence_types,
        },
    },
    types::{
        effect_polarity::{EffectPolarity, trait_output_effect_polarities},
        effects::{EffType, Effect, EffectVar},
        mutability::{MutType, MutVar},
        r#trait::{Trait, TraitAssociatedConstIndex, TraitDictionaryEntryIndex, TraitMethodIndex},
        r#type::{CallImplType, FnType, SubscriptType, Type, TypeDef, TypeKind, TypeVar},
        type_inference::{substitution::InstSubst, unify::UnifiedTypeInference},
        type_like::{TypeLike, instantiate_types},
        type_mapper::{
            BitmapInstantiationMapper, EffectErasingMapper, SimpleInstantiationMapper, TypeMapper,
        },
        type_properties::{TypePropertyEnv, concrete_type_is_trivial_copy, trivial_copy_impl_key},
        type_scheme::{PubTypeConstraint, TypeScheme},
    },
};

/// Evidence for the generic call and the canonical hidden arguments of its thunk.
/// Keeping these together prevents materialization and capture planning from
/// disagreeing about the callable entry's ABI.
#[derive(Clone)]
struct BlanketMethodRequirements {
    callee: Vec<DictionaryReq>,
    entry: DictionaryEntryRequirements,
}

/// Materialized constants have capture-free literal getters; only method thunks
/// contribute evidence requirements to a blanket implementation's dictionary.
fn blanket_dictionary(
    trait_id: TraitId,
    input_tys: &[Type],
    methods: &[LocalFunctionId],
    associated_const_getters: &[LocalFunctionId],
    requirements: &[BlanketMethodRequirements],
) -> TraitDictionary {
    let (capture_schema, mut entry_capture_mappings) = dictionary_capture_plan(
        trait_id,
        input_tys,
        requirements.iter().map(|requirements| &requirements.entry),
    );
    entry_capture_mappings.extend((0..associated_const_getters.len()).map(|_| Vec::new()));
    build_capturing_dictionary_value(
        methods,
        associated_const_getters,
        capture_schema,
        entry_capture_mappings,
    )
}

/// Trait solving is performed by this structure, mutating it by caching intermediate results.
#[allow(clippy::too_many_arguments)]
#[derive(Debug)]
#[must_use = "call .finish().commit() to store the created functions"]
pub struct TraitSolver<'a> {
    /// Current module type-level items. Kept separately from `others` because the current module can be mid-compilation and not yet committed.
    pub(crate) current_type_items: CurrentTypeItems<'a>,
    /// Current module implementations.
    pub impls: &'a mut TraitImpls,
    /// Borrowed definitions for looking up existing named functions. Generated
    /// functions remain in `fn_collector` until commit.
    current_def_table: &'a DefTable,
    /// Current module dependencies discovered while solving.
    pub deps: &'a mut FxHashSet<ModuleId>,
    /// Current-module projection subscript capability types, materialized eagerly for real solvers and lazily for probes.
    current_projection_subscript_types: CurrentProjectionSubscriptTypes<'a>,
    /// Collector for newly created current module functions.
    pub fn_collector: PendingFunctionCollector,
    /// Other modules available for fetching trait implementations and normal functions (read only).
    pub(crate) others: &'a Modules,
    /// Current recursion depth of the trait solver.
    pub recursion_depth: usize,
    /// Whether this solver is deciding by structure if an impl applies, ignoring all effects.
    selecting_by_structure: bool,
    /// Current stack of trait implementations being solved, for cycle detection.
    pub solving_stack: FxHashSet<(TraitId, Vec<Type>)>,
    /// Partially known trait applications currently being improved, for cycle detection.
    active_improvements: FxHashSet<TraitImprovementKey>,
    /// Stack of defining modules for imported blanket impls currently being materialized.
    /// Only the top module's private impls are visible.
    private_impl_scope: Vec<ModuleId>,
    /// Additional module whose private impls are visible to a privileged scratch expression.
    privileged_impl_module: Option<ModuleId>,
    /// Successful fully-concrete, unconstrained output probes made during inference or defaulting.
    ///
    /// This is deliberately per-solver. A [`TraitSolverProbe`] can hide private implementations
    /// from its source solver, so it must not inherit answers from this cache.
    unmaterialized_output_cache: FxHashMap<TraitId, Vec<TraitOutputCacheEntry>>,
    /// While requesting a dictionary for a callable, the effect variables it quantifies: a reused
    /// dictionary must serve every value they may take. Taken by the request's top-level frame.
    quantified_request_effect_vars: FxHashSet<EffectVar>,
}

/// The trait selection context that can affect a probe's semantic answer.
#[derive(Debug, Clone)]
struct TraitOutputCacheEntry {
    input_tys: Vec<Type>,
    /// Only the top imported-blanket module exposes private implementations.
    private_impl_module: Option<ModuleId>,
    privileged_impl_module: Option<ModuleId>,
    output_tys: Vec<Type>,
    output_effs: Vec<EffType>,
}

impl<'a> TraitSolver<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        current_type_items: CurrentTypeItems<'a>,
        impls: &'a mut TraitImpls,
        current_def_table: &'a DefTable,
        deps: &'a mut FxHashSet<ModuleId>,
        current_projection_subscript_types: CurrentProjectionSubscriptTypes<'a>,
        fn_collector: PendingFunctionCollector,
        others: &'a Modules,
    ) -> Self {
        debug_assert_eq!(current_type_items.module.id, impls.module_id);
        Self {
            current_type_items,
            impls,
            current_def_table,
            deps,
            current_projection_subscript_types,
            fn_collector,
            others,
            recursion_depth: 0,
            solving_stack: FxHashSet::default(),
            active_improvements: FxHashSet::default(),
            private_impl_scope: Vec::new(),
            selecting_by_structure: false,
            privileged_impl_module: None,
            unmaterialized_output_cache: FxHashMap::default(),
            quantified_request_effect_vars: FxHashSet::default(),
        }
    }

    /// Run `f` with the private impls of `module` visible, as when solving inside that module.
    pub(crate) fn in_private_impl_scope<R>(
        &mut self,
        module: ModuleId,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.private_impl_scope.push(module);
        let result = f(self);
        self.private_impl_scope.pop();
        result
    }

    /// Allow this solver to use private trait implementations from `module_id`.
    ///
    /// This is used by the private scratch-expression machinery when dispatching on a value whose
    /// type originates in another module. It does not grant access to private names or type
    /// representations.
    pub(crate) fn allow_private_impls_from(&mut self, module_id: ModuleId) {
        debug_assert!(self.privileged_impl_module.is_none());
        self.privileged_impl_module = Some(module_id);
    }
}

pub(crate) const TRAIT_SOLVER_RECURSION_LIMIT: usize = 128;

/// Improvement nests deeper frames than solving, and giving up only leaves an application to be
/// resolved later, so its limit is lower.
const IMPROVEMENT_DEPTH_LIMIT: usize = 32;

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

/// Whether an implementation's output effect fits the one a requirement names, by polarity:
/// a performed effect may be smaller, a received one larger. Rows are compared effect by effect,
/// which holds whatever their variables stand for.
pub(crate) fn output_effect_fits(
    solved: &EffType,
    required: &EffType,
    polarity: EffectPolarity,
) -> bool {
    let included =
        |smaller: &EffType, larger: &EffType| smaller.iter().all(|eff| larger.contains(eff));
    match polarity {
        EffectPolarity::Positive => included(solved, required),
        EffectPolarity::Negative => included(required, solved),
        EffectPolarity::Invariant => solved == required,
    }
}

/// Macro to create a trait solver from a module and a program.
/// This cannot be a function because of lifetime issues, as we must
/// mutably borrow parts of the module's data while not touching the function field.
macro_rules! trait_solver_from_module {
    ($module:expr, $program:expr) => {{
        let current_projection_subscript_types =
            crate::types::trait_solver::CurrentProjectionSubscriptTypes::from_map(
                crate::types::trait_solver::current_projection_subscript_type_map(&$module),
            );
        let function_count = $module.functions.len();
        TraitSolver::new(
            crate::module::CurrentTypeItems::new(
                crate::module::ModuleIdentity {
                    id: $module.module_id(),
                    path: &$module.path,
                },
                &$module.type_aliases,
                $module.type_defs.as_slice(),
                $module.traits.as_slice(),
                &$module.projection_subscripts,
            ),
            &mut $module.impls,
            &$module.def_table,
            &mut $module.deps,
            current_projection_subscript_types,
            crate::module::PendingFunctionCollector::new(function_count),
            $program,
        )
    }};
}
pub(crate) use trait_solver_from_module;

/// Scratch overlay for running trait-solver queries without mutating a real module.
pub(crate) struct TraitSolverProbe<'a> {
    current_type_items: CurrentTypeItems<'a>,
    impls: Cow<'a, TraitImpls>,
    current_def_table: &'a DefTable,
    current_projection_subscript_types: CurrentProjectionSubscriptTypes<'a>,
    deps: FxHashSet<ModuleId>,
    fn_collector: PendingFunctionCollector,
    active_improvements: FxHashSet<TraitImprovementKey>,
    private_impl_scope: Vec<ModuleId>,
    privileged_impl_module: Option<ModuleId>,
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

struct DefaultedEffectRowsMapper<'a> {
    variables: &'a FxHashSet<EffectVar>,
}

impl TypeMapper for DefaultedEffectRowsMapper<'_> {
    fn map_type(&mut self, ty: Type) -> Type {
        ty
    }

    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
        mut_ty
    }

    fn map_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        eff_ty
            .iter()
            .filter(|effect| match effect {
                Effect::Variable(var) => !self.variables.contains(var),
                Effect::Primitive(_) => true,
            })
            .collect()
    }
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

/// Rename variables by deterministic first occurrence, preserving the structure and concrete parts
/// of the types. This is an identity only for compiler-generated artifacts whose variables remain
/// quantified; it must not replace semantic type identity in ordinary trait lookup.
pub(crate) fn alpha_canonicalize_types(types: &[Type]) -> Vec<Type> {
    let mut mapper = AlphaCanonicalTypeMapper::default();
    types.iter().map(|ty| ty.map(&mut mapper)).collect()
}

/// The identity of a generated dictionary: its trait application, inputs and outputs, renamed
/// together by first occurrence, as outputs may stay open in the caller's variables. Each output
/// effect is encoded as the effect of a nullary function type, so the key shares the representation
/// of input-keyed applications without colliding with them.
pub(crate) fn application_key(
    trait_id: TraitId,
    input_tys: &[Type],
    output_tys: Option<&[Type]>,
    output_effs: Option<&[EffType]>,
) -> ConcreteTraitImplKey {
    let mut mapper = AlphaCanonicalTypeMapper::default();
    let mut tys = input_tys
        .iter()
        .chain(output_tys.unwrap_or_default())
        .map(|ty| ty.map(&mut mapper))
        .collect::<Vec<_>>();
    if let Some(output_effs) = output_effs {
        tys.extend(output_effs.iter().map(|eff| {
            Type::function_type(FnType::new_by_val(
                [],
                Type::unit(),
                mapper.map_effect_type(eff),
            ))
        }));
    }
    ConcreteTraitImplKey::new(trait_id, tys)
}

/// Alpha-canonicalize types and return the instantiation from canonical variables back to the
/// caller's variables. Generated dictionary definitions use the canonical side; construction
/// sites apply the returned substitution to their capture schemas.
pub(crate) fn alpha_canonicalize_types_with_instantiation(
    types: &[Type],
) -> (Vec<Type>, InstSubst) {
    let mut mapper = AlphaCanonicalTypeMapper::default();
    let canonical = types.iter().map(|ty| ty.map(&mut mapper)).collect();
    let ty_subst = mapper
        .ty_vars
        .into_iter()
        .map(|(original, canonical)| (canonical, Type::variable(original)))
        .collect();
    let eff_subst = mapper
        .effect_vars
        .into_iter()
        .map(|(original, canonical)| (canonical, EffType::single_variable(original)))
        .collect();
    (canonical, (ty_subst, eff_subst))
}

pub(crate) fn alpha_canonicalize_dictionary_requirements(
    requirements: &[DictionaryReq],
) -> Vec<DictionaryReq> {
    let mut mapper = AlphaCanonicalTypeMapper::default();
    requirements
        .iter()
        .map(|requirement| requirement.instantiate(&mut mapper))
        .collect()
}

#[derive(Debug, Clone)]
pub(crate) struct CurrentProjectionSubscriptTypes<'a> {
    source: CurrentProjectionSubscriptTypeSource<'a>,
    types: Option<Rc<FxHashMap<ProjectionKey, SubscriptType>>>,
}

#[derive(Debug, Clone, Copy)]
enum CurrentProjectionSubscriptTypeSource<'a> {
    Module(&'a Module),
    Materialized,
}

impl<'a> CurrentProjectionSubscriptTypes<'a> {
    pub(crate) fn from_module(module: &'a Module) -> Self {
        Self {
            source: CurrentProjectionSubscriptTypeSource::Module(module),
            types: None,
        }
    }

    pub(crate) fn from_map(types: FxHashMap<ProjectionKey, SubscriptType>) -> Self {
        Self {
            source: CurrentProjectionSubscriptTypeSource::Materialized,
            types: Some(Rc::new(types)),
        }
    }

    #[cfg(test)]
    pub(crate) fn empty() -> Self {
        Self::from_map(FxHashMap::default())
    }

    fn get(&mut self, key: ProjectionKey) -> Option<SubscriptType> {
        if self.types.is_none() {
            let CurrentProjectionSubscriptTypeSource::Module(source) = self.source else {
                return None;
            };
            self.types = Some(Rc::new(current_projection_subscript_type_map(source)));
        }
        self.types
            .as_ref()
            .and_then(|types| types.get(&key).cloned())
    }

    fn cache_materialized_types_from(&mut self, other: &CurrentProjectionSubscriptTypes<'_>) {
        if let Some(types) = &other.types {
            self.types = Some(Rc::clone(types));
        }
    }
}

pub(crate) fn current_projection_subscript_type_map(
    module: &Module,
) -> FxHashMap<ProjectionKey, SubscriptType> {
    module
        .projection_subscripts
        .iter()
        .filter_map(|(key, entry)| {
            let subscript = module.get_subscript_by_id(entry.subscript)?;
            Some((*key, subscript.type_scheme(module)?.ty))
        })
        .collect()
}

/// Stub `TraitOutputQuery` for paths that statically never invoke a query
/// (concrete candidate matching only unifies types and never reaches `match_blanket_impl`).
struct NeverProbe;

impl TraitOutputQuery for NeverProbe {
    fn output_effect_polarities_query(&mut self, _trait_id: TraitId) -> Vec<EffectPolarity> {
        unreachable!("concrete candidate matching never queries nested trait outputs")
    }

    fn unify_non_trait_constraint_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        constraint: &PubTypeConstraint,
        _assumptions: ConstraintAssumptions<'_>,
        _arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        ty_inf.unify_structural_pub_constraint(constraint)
    }

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
        _output_effs: Option<&[EffType]>,
        _fn_span: Location,
        _arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        unreachable!(
            "NeverProbe should not be queried — concrete candidates do not call match_blanket_impl"
        )
    }

    fn solve_outputs_by_structure_query(
        &mut self,
        _trait_id: TraitId,
        _input_tys: &[Type],
        _fn_span: Location,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        unreachable!("concrete improvement candidates have no nested queries")
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
    fn unify_non_trait_constraint_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        constraint: &PubTypeConstraint,
        assumptions: ConstraintAssumptions<'_>,
        arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError>;

    fn is_compiler_provided_no_output_trait_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) -> bool;

    /// The outputs of the implementation selected for `input_tys`; requested output effects, if
    /// any, take part in matching it.
    fn solve_outputs_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_effs: Option<&[EffType]>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError>;

    /// The outputs of the impl that `trait_id` selects for `input_tys` by structure, ignoring all
    /// effects: an impl selected with the wrong effects still gives its output types.
    fn solve_outputs_by_structure_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<Vec<Type>, InternalCompilationError>;

    /// The polarity of each output effect of `trait_id`.
    fn output_effect_polarities_query(&mut self, trait_id: TraitId) -> Vec<EffectPolarity>;

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
    fn output_effect_polarities_query(&mut self, trait_id: TraitId) -> Vec<EffectPolarity> {
        self.solver.output_effect_polarities(trait_id)
    }

    fn unify_non_trait_constraint_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        constraint: &PubTypeConstraint,
        assumptions: ConstraintAssumptions<'_>,
        arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        self.probe()
            .unify_non_trait_constraint_query(ty_inf, constraint, assumptions, arena)
    }

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
        output_effs: Option<&[EffType]>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        self.probe()
            .solve_outputs_query(trait_id, input_tys, output_effs, fn_span, arena)
    }

    fn solve_outputs_by_structure_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        self.probe()
            .solve_outputs_by_structure_query(trait_id, input_tys, fn_span)
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
            current_type_items: CurrentTypeItems::new_from_module(module),
            impls: Cow::Borrowed(&module.impls),
            current_def_table: &module.def_table,
            current_projection_subscript_types: CurrentProjectionSubscriptTypes::from_module(
                module,
            ),
            deps: module.deps.clone(),
            fn_collector: PendingFunctionCollector::new(module.functions.len()),
            active_improvements: FxHashSet::default(),
            private_impl_scope: Vec::new(),
            privileged_impl_module: None,
            others,
        }
    }

    fn from_solver(solver: &TraitSolver<'a>) -> Self {
        let mut impls = solver.impls.clone();
        // Most probes have no private concrete entries. Do not detach the shared
        // index for a retain that would leave it unchanged.
        if impls
            .concrete_key_to_id
            .values()
            .any(|id| !impls.data[id.as_index()].public)
        {
            Rc::make_mut(&mut impls.concrete_key_to_id)
                .retain(|_, id| impls.data[id.as_index()].public);
        }
        Self {
            current_type_items: solver.current_type_items,
            impls: Cow::Owned(impls),
            current_def_table: solver.current_def_table,
            current_projection_subscript_types: solver.current_projection_subscript_types.clone(),
            deps: solver.deps.clone(),
            fn_collector: solver.fn_collector.clone(),
            active_improvements: solver.active_improvements.clone(),
            private_impl_scope: solver.private_impl_scope.clone(),
            privileged_impl_module: solver.privileged_impl_module,
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
            self.current_type_items,
            self.impls.to_mut(),
            self.current_def_table,
            &mut self.deps,
            self.current_projection_subscript_types.clone(),
            fn_collector,
            self.others,
        );
        solver.active_improvements = mem::take(&mut self.active_improvements);
        solver.private_impl_scope = self.private_impl_scope.clone();
        solver.privileged_impl_module = self.privileged_impl_module;
        let result = f(&mut solver);
        self.active_improvements = mem::take(&mut solver.active_improvements);
        self.private_impl_scope = mem::take(&mut solver.private_impl_scope);
        self.privileged_impl_module = solver.privileged_impl_module;
        self.current_projection_subscript_types
            .cache_materialized_types_from(&solver.current_projection_subscript_types);
        self.fn_collector = mem::replace(
            &mut solver.fn_collector,
            PendingFunctionCollector::new(initial_count),
        );
        result
    }

    pub(crate) fn concrete_type_is_trivial_copy(&mut self, ty: Type) -> bool {
        self.with_solver(|solver| solver.concrete_type_is_trivial_copy(ty))
    }
}

impl TraitOutputQuery for TraitSolverProbe<'_> {
    fn output_effect_polarities_query(&mut self, trait_id: TraitId) -> Vec<EffectPolarity> {
        self.with_solver(|solver| solver.output_effect_polarities(trait_id))
    }

    fn unify_non_trait_constraint_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        constraint: &PubTypeConstraint,
        assumptions: ConstraintAssumptions<'_>,
        arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        self.with_solver(|solver| {
            ty_inf.unify_pub_constraint(constraint, assumptions, |_| false, solver, arena)
        })
    }

    fn is_compiler_provided_no_output_trait_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) -> bool {
        self.with_solver(|solver| {
            is_compiler_provided_no_output_trait_application(
                trait_id,
                solver.trait_def(trait_id),
                input_tys,
                output_tys,
                output_effs,
                solver,
            )
        })
    }

    fn solve_outputs_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_effs: Option<&[EffType]>,
        fn_span: Location,
        _arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        self.with_solver(|solver| {
            solver.solve_application_outputs_without_materializing(
                trait_id,
                input_tys,
                None,
                output_effs,
                fn_span,
            )
        })
    }

    fn solve_outputs_by_structure_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        self.with_solver(|solver| {
            solver.solve_outputs_by_structure_query(trait_id, input_tys, fn_span)
        })
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
                true,
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

/// The blanket impls of a trait visible from a module with the given local table: the local
/// ones first, then those of each other module.
fn visible_blanket_impls<'b>(
    local: &'b BlanketImpls,
    others: &'b Modules,
    trait_id: TraitId,
) -> impl Iterator<Item = (Option<ModuleId>, &'b BlanketTraitImpls)> + use<'b> {
    local
        .get(&trait_id)
        .map(|blankets| (None, blankets))
        .into_iter()
        .chain(others.enumerates().flat_map(move |(module_id, entry, _)| {
            entry.module().and_then(|module| {
                module
                    .impls
                    .blanket_key_to_id
                    .get(&trait_id)
                    .map(|blankets| (Some(module_id), blankets))
            })
        }))
}

/// Whether an impl's input types may match the requested ones, see [`input_head_may_match`].
pub(crate) fn input_heads_may_match(candidates: &[Type], inputs: &[Type]) -> bool {
    candidates
        .iter()
        .zip(inputs)
        .all(|(&candidate, &input)| input_head_may_match(candidate, input))
}

/// A necessary condition for the same-type relation that matches impl inputs.
/// Reject only fixed outer-constructor conflicts; unknowns, nested arguments,
/// mutability and effects still go through the full match. In particular Never
/// is not a wildcard here: matching checks equality, not bottom subtyping.
fn input_head_may_match(candidate: Type, input: Type) -> bool {
    use TypeKind::*;
    match (&*candidate.data(), &*input.data()) {
        (Variable(_), _) | (_, Variable(_)) => true,
        (Native(a), Native(b)) => a.bare_ty == b.bare_ty,
        (Named(a), Named(b)) => a.def == b.def,
        (Tuple(a), Tuple(b)) => a.len() == b.len(),
        (Function(a), Function(b)) => a.args.len() == b.args.len(),
        (a, b) => mem::discriminant(a) == mem::discriminant(b),
    }
}

/// An application resolved symbolically by a blanket implementation: the implementation's
/// outputs and constraints in terms of the application's variables. Type and effect variables
/// from `type_var_base` and `effect_var_base` on are the implementation's own, which the caller
/// renames to fresh variables.
pub(crate) struct SymbolicApplication {
    /// The implementation's inputs, unrelated to the application's, which the caller relates.
    pub(crate) input_tys: Vec<Type>,
    pub(crate) output_tys: Vec<Type>,
    pub(crate) output_effs: Vec<EffType>,
    pub(crate) obligations: Vec<PubTypeConstraint>,
    /// The module of an implementation from another module, whose private impls its
    /// obligations may use, as when its dictionary is materialized.
    pub(crate) private_impl_scope: Option<ModuleId>,
    pub(crate) type_var_base: u32,
    pub(crate) effect_var_base: u32,
}

/// A blanket implementation whose inputs match an application, before its caller accepts it.
struct BlanketCandidate<'k> {
    /// The module of the implementation, `None` for the current one.
    module: Option<ModuleId>,
    impl_id: LocalImplId,
    sub_key: &'k BlanketTraitImplSubKey,
    /// The implementation's outputs, in its own variables.
    declared_output_tys: Vec<Type>,
    declared_output_effs: Vec<EffType>,
    /// The outputs at this application.
    output_tys: Vec<Type>,
    output_effs: Vec<EffType>,
    runtime_requirements: Vec<ResolvedRuntimeRequirement>,
    /// The implementation's generic parameters resolved at this application.
    instantiation: InstSubst,
}

/// A runtime hidden requirement from a matched blanket impl after substitution.
struct ResolvedRuntimeRequirement {
    /// Original source order of the constraint in the blanket impl.
    index: usize,
    req: DictionaryReq,
}

pub(crate) struct DerivedImplSnapshot {
    concrete_key_to_id: Rc<ConcreteImpls>,
    blanket_key_to_id: Rc<BlanketImpls>,
    generated_value_key_to_id: Rc<FxHashMap<Vec<Type>, LocalImplId>>,
    application_key_to_id: Rc<ConcreteImpls>,
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
#[derive(Clone, Copy)]
enum BlanketConstraintMode {
    /// Matching is only considered successful if every nested trait constraint
    /// can be resolved immediately.
    RequireAllResolved,
    /// As `RequireAllResolved`, on arguments without effects: whether the impl applies by
    /// structure, which effects never decide. So nested outputs lose their effects too.
    Structural,
    /// As `AllowUnknown`, by structure as in `Structural`.
    StructuralAllowUnknown,
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
    /// and the resolved runtime hidden requirements in source order.
    Yes {
        output_tys: Vec<Type>,
        output_effs: Vec<EffType>,
        runtime_requirements: Vec<ResolvedRuntimeRequirement>,
        /// The blanket implementation's generic parameters resolved at this application.
        instantiation: InstSubst,
    },
}

fn trait_def_from_parts<'a>(
    current: CurrentTypeItems<'a>,
    others: &'a Modules,
    id: TraitId,
) -> &'a Trait {
    if let Some(trait_def) = current.trait_def(id) {
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
    env: &impl TypeLayoutEnv,
) -> bool {
    output_tys.is_empty()
        && output_effs.is_empty()
        && is_compiler_provided_value_trait_application(
            trait_id, trait_def, input_tys, output_tys, env,
        )
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
        imp.public
            || self.private_impl_scope.last().copied() == Some(module_id)
            || self.privileged_impl_module == Some(module_id)
    }

    pub(crate) fn reject_inaccessible_private_repr(
        &self,
        id: TypeDefId,
        access_span: Location,
    ) -> Result<(), InternalCompilationError> {
        if id.module != self.current_type_items.module.id && self.type_def(id).has_private_repr() {
            return Err(internal_compilation_error!(PrivateReprAccess {
                type_def: id,
                access_span,
            }));
        }
        Ok(())
    }

    pub fn trait_def(&self, id: TraitId) -> &Trait {
        trait_def_from_parts(self.current_type_items, self.others, id)
    }

    pub fn std_trait_id(&self, name: &str) -> TraitId {
        // The solver only keeps the current module's trait definitions, not its
        // definition table, so current-std lookups cannot use the symbol table.
        if self.current_type_items.module.id == STD_MODULE_ID
            && let Some((index, _)) = self
                .current_type_items
                .traits
                .iter()
                .enumerate()
                .find(|(_, trait_def)| trait_def.name == name)
        {
            return TraitId::new(STD_MODULE_ID, LocalTraitId::from_index(index));
        }
        Module::expect_std_trait_id(self.others, name)
    }

    pub fn type_def(&self, id: TypeDefId) -> &TypeDef {
        self.current_type_items.type_def(id).unwrap_or_else(|| {
            self.others
                .get(id.module)
                .and_then(|entry| entry.module())
                .unwrap_or_else(|| panic!("Type definition module #{} is unavailable", id.module))
                .type_def(id)
        })
    }

    pub(crate) fn projection_subscript_type(
        &mut self,
        receiver_ty: Type,
        field: Ustr,
    ) -> Option<SubscriptType> {
        let key = ProjectionKey::explicit_for_receiver_ty(receiver_ty, field)?;
        let receiver_params = {
            let data = receiver_ty.data();
            match &*data {
                TypeKind::Named(named) => named.params.clone(),
                TypeKind::Native(_) => Default::default(),
                _ => return None,
            }
        };
        let subscript = self.projection_subscript_id(key)?;
        let subscript_ty = if subscript.module == self.current_type_items.module.id {
            self.current_projection_subscript_types.get(key)?
        } else {
            let module = self
                .others
                .get(subscript.module)
                .and_then(|entry| entry.module())?;
            module
                .get_subscript_by_id(subscript.subscript)?
                .type_scheme(module)?
                .ty
        };
        let subst = (
            receiver_params
                .iter()
                .copied()
                .enumerate()
                .map(|(index, ty)| (TypeVar::new(index as u32), ty))
                .collect(),
            FxHashMap::default(),
        );
        Some(subscript_ty.instantiate_simple(&subst))
    }

    pub(crate) fn projection_subscript_id(
        &mut self,
        key: ProjectionKey,
    ) -> Option<module::SubscriptId> {
        if let Some(entry) = self.current_type_items.projection_subscripts.get(&key) {
            return Some(module::SubscriptId::new(
                self.current_type_items.module.id,
                entry.subscript,
            ));
        }

        self.others.enumerate().find_map(|(module_id, entry, _)| {
            let module = entry.module()?;
            let entry = module.get_projection_subscript(key)?;
            if entry.visibility != module::Visibility::Public {
                return None;
            }
            self.deps.insert(module_id);
            Some(module::SubscriptId::new(module_id, entry.subscript))
        })
    }

    pub(crate) fn qualified_name_env(&self) -> QualifiedNameEnv<'_> {
        QualifiedNameEnv::new(self.current_type_items, self.others)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn impl_associated_const_names(
        &self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
        ty_var_count: u32,
        eff_var_count: u32,
        constraints: &[PubTypeConstraint],
    ) -> Vec<Ustr> {
        let trait_def = self.trait_def(trait_id);
        let env = self.qualified_name_env();
        (0..trait_def.associated_const_count())
            .map(TraitAssociatedConstIndex::from_index)
            .map(|index| {
                env.disambiguated_impl_associated_const_name(
                    trait_id,
                    trait_def,
                    index,
                    input_tys,
                    output_tys,
                    output_effs,
                    ty_var_count,
                    eff_var_count,
                    constraints,
                )
                .into()
            })
            .collect()
    }

    pub(crate) fn solve_concrete_trivial_copy_layout(
        &mut self,
        ty: Type,
        span: Location,
    ) -> Result<Option<ResolvedValueLayout>, InternalCompilationError> {
        if !self.concrete_type_is_trivial_copy(ty) {
            return Ok(None);
        }
        Ok(Some(value_layout_for_type(ty, span, self)?))
    }

    /// Return whether representation-copying this concrete type is semantically valid.
    ///
    /// See [`concrete_type_is_trivial_copy`] for the rule; the solver supplies the environment,
    /// which unlike a `ModuleEnv`'s also sees the impls of the module being compiled.
    pub(crate) fn concrete_type_is_trivial_copy(&self, ty: Type) -> bool {
        concrete_type_is_trivial_copy(ty, self)
    }

    /// Probe the canonical module that owns the trait rather than the current
    /// visibility scope. Native-only marker properties must not change when an
    /// unrelated module is added to or removed from the solver environment.
    fn has_canonical_trait_impl(&self, key: &ConcreteTraitImplKey) -> bool {
        if key.trait_id.module == self.current_type_items.module.id {
            return self.impls.concrete_key_to_id.contains_key(key);
        }
        self.others
            .get(key.trait_id.module)
            .and_then(|entry| entry.module())
            .is_some_and(|module| module.impls.concrete_key_to_id.contains_key(key))
    }

    /// Collect visible impls whose outer input constructors may match the application.
    ///
    /// This is used by trait improvement to probe whether a partially known
    /// trait application already has a unique matching impl.
    fn improvement_candidates(
        &self,
        trait_id: TraitId,
        input_tys: &[Type],
    ) -> Vec<TraitImprovementCandidate> {
        fn semantic_constraints(constraints: &[PubTypeConstraint]) -> Vec<PubTypeConstraint> {
            constraints
                .iter()
                // Payload layout is code-generation evidence. It has no outputs and cannot make
                // an implementation applicable or inapplicable, so speculative improvement must
                // not pay to instantiate and solve it for every candidate. The full constraint
                // list is still used when the selected blanket implementation is materialized.
                .filter(|constraint| {
                    !matches!(constraint, PubTypeConstraint::VariantPayloadLayout { .. })
                })
                .cloned()
                .collect()
        }

        let compatible =
            |candidate_inputs: &[Type]| input_heads_may_match(candidate_inputs, input_tys);
        let mut candidates = Vec::new();

        for (key, id) in self.impls.concrete_key_to_id.iter() {
            if key.trait_id == trait_id {
                let imp = &self.impls.data[id.as_index()];
                if !imp.public || !compatible(&key.input_tys) {
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
                if !compatible(&sub_key.input_tys) {
                    continue;
                }
                candidates.push(TraitImprovementCandidate::Blanket {
                    input_tys: sub_key.input_tys.clone(),
                    output_tys: imp.output_tys.clone(),
                    output_effs: imp.output_effs.clone(),
                    ty_var_count: sub_key.ty_var_count,
                    eff_var_count: sub_key.eff_var_count,
                    constraints: semantic_constraints(&sub_key.constraints),
                });
            }
        }

        for (_, entry) in self.others.iter_named() {
            let Some(module) = entry.module() else {
                continue;
            };

            for (key, id) in module.impls.concrete_key_to_id.iter() {
                if key.trait_id == trait_id {
                    let imp = &module.impls.data[id.as_index()];
                    if self.can_use_other_impl(module.module_id(), imp)
                        && compatible(&key.input_tys)
                    {
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
                    if self.can_use_other_impl(module.module_id(), imp)
                        && compatible(&sub_key.input_tys)
                    {
                        candidates.push(TraitImprovementCandidate::Blanket {
                            input_tys: sub_key.input_tys.clone(),
                            output_tys: imp.output_tys.clone(),
                            output_effs: imp.output_effs.clone(),
                            ty_var_count: sub_key.ty_var_count,
                            eff_var_count: sub_key.eff_var_count,
                            constraints: semantic_constraints(&sub_key.constraints),
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
        output_polarities: &[EffectPolarity],
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
                    for ((candidate_eff, output_eff), polarity) in candidate_output_effs
                        .iter()
                        .zip(output_effs.iter())
                        .zip(output_polarities)
                    {
                        if Self::match_trait_output_effect(
                            ty_inf,
                            candidate_eff,
                            output_eff,
                            *polarity,
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
                    output_polarities,
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

    /// Whether an improvement candidate may apply when all effects are ignored.
    #[allow(clippy::too_many_arguments)]
    fn improvement_candidate_applies_by_structure<Q: TraitOutputQuery>(
        query: &mut Q,
        ty_inf: &mut UnifiedTypeInference,
        candidate: &TraitImprovementCandidate,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<bool, InternalCompilationError> {
        let input_tys = instantiate_types(input_tys, &mut EffectErasingMapper);
        let output_tys = output_tys.map(|tys| instantiate_types(tys, &mut EffectErasingMapper));
        let erased_candidate = match candidate {
            TraitImprovementCandidate::Concrete {
                input_tys: candidate_inputs,
                output_tys: candidate_outputs,
                output_effs,
            } => TraitImprovementCandidate::Concrete {
                input_tys: instantiate_types(candidate_inputs, &mut EffectErasingMapper),
                output_tys: instantiate_types(candidate_outputs, &mut EffectErasingMapper),
                output_effs: output_effs.clone(),
            },
            TraitImprovementCandidate::Blanket {
                input_tys: candidate_inputs,
                output_tys: candidate_outputs,
                output_effs,
                ty_var_count,
                eff_var_count,
                constraints,
            } => {
                let erased_inputs = instantiate_types(candidate_inputs, &mut EffectErasingMapper);
                let erased_outputs = instantiate_types(candidate_outputs, &mut EffectErasingMapper);
                let erased_constraints = instantiate_types(constraints, &mut EffectErasingMapper);
                let matched = Self::match_blanket_impl(
                    query,
                    ty_inf,
                    &erased_inputs,
                    &erased_outputs,
                    &vec![EffType::empty(); output_effs.len()],
                    &[],
                    *ty_var_count,
                    *eff_var_count,
                    &erased_constraints,
                    &input_tys,
                    output_tys.as_deref(),
                    None,
                    assumptions,
                    fn_span,
                    arena,
                    BlanketConstraintMode::StructuralAllowUnknown,
                )?;
                return Ok(!matches!(matched, BlanketImplMatch::No));
            }
        };
        Ok(!matches!(
            Self::improvement_candidate_matches(
                query,
                ty_inf,
                &erased_candidate,
                &[],
                &input_tys,
                output_tys.as_deref(),
                None,
                assumptions,
                fn_span,
                arena,
            )?,
            TraitImprovementMatch::No
        ))
    }

    fn improve_trait_application_with_candidate_head(
        ty_inf: &mut UnifiedTypeInference,
        candidate: &TraitImprovementCandidate,
        output_polarities: &[EffectPolarity],
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
                    for ((candidate_eff, output_eff), polarity) in candidate_output_effs
                        .iter()
                        .zip(output_effs.iter())
                        .zip(output_polarities)
                    {
                        Self::match_trait_output_effect(
                            ty_inf,
                            candidate_eff,
                            output_eff,
                            *polarity,
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
                constraints: _,
            } => {
                let inst_subst = (
                    ty_inf.fresh_type_var_subst(*ty_var_count),
                    ty_inf.fresh_effect_var_subst(*eff_var_count),
                );
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
                    for ((candidate_eff, output_eff), polarity) in candidate_output_effs
                        .iter()
                        .zip(output_effs.iter())
                        .zip(output_polarities)
                    {
                        Self::match_trait_output_effect(
                            ty_inf,
                            candidate_eff,
                            output_eff,
                            *polarity,
                            fn_span,
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Relate an implementation's output effect to the requested one by the output's polarity:
    /// an effect the methods perform may be smaller than requested, one they receive larger.
    pub(crate) fn match_trait_output_effect(
        ty_inf: &mut UnifiedTypeInference,
        impl_eff: &EffType,
        requested_eff: &EffType,
        polarity: EffectPolarity,
        fn_span: Location,
    ) -> Result<(), InternalCompilationError> {
        match polarity {
            EffectPolarity::Positive => {
                ty_inf.add_effect_dep(impl_eff, fn_span, requested_eff, fn_span)
            }
            EffectPolarity::Negative => {
                ty_inf.add_effect_dep(requested_eff, fn_span, impl_eff, fn_span)
            }
            EffectPolarity::Invariant => {
                ty_inf.unify_same_effect(impl_eff, fn_span, requested_eff, fn_span)
            }
        }
    }

    /// The polarity of each output effect of `trait_id`.
    pub(crate) fn output_effect_polarities(&self, trait_id: TraitId) -> Vec<EffectPolarity> {
        trait_output_effect_polarities(trait_id, &|id| self.trait_def(id))
    }

    fn type_var_capacity_for_types<'t>(types: impl IntoIterator<Item = &'t Type>) -> u32 {
        types
            .into_iter()
            .flat_map(TypeLike::inner_ty_vars)
            .map(|var| var.name() + 1)
            .max()
            .unwrap_or(0)
    }

    fn effect_var_capacity<'t>(
        types: impl IntoIterator<Item = &'t Type>,
        effects: &[EffType],
    ) -> u32 {
        types
            .into_iter()
            .flat_map(TypeLike::inner_effect_vars)
            .chain(effects.iter().flat_map(EffType::inner_vars))
            .map(|var| var.name() + 1)
            .max()
            .unwrap_or(0)
    }

    fn impl_matches_requested_outputs(
        &self,
        imp: &TraitImpl,
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        quantified_effect_vars: &FxHashSet<EffectVar>,
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
        // The request's effect variables are renamed apart from the dictionary's. Those its caller
        // quantifies are rigid: the dictionary must serve every value they may take.
        let mut requested_vars = FxHashSet::default();
        for ty in requested_output_tys.unwrap_or_default() {
            requested_vars.extend(ty.inner_effect_vars());
        }
        for eff in requested_output_effs.unwrap_or_default() {
            eff.fill_with_inner_effect_vars(&mut requested_vars);
        }
        let mut impl_vars = FxHashSet::default();
        for ty in &imp.output_tys {
            impl_vars.extend(ty.inner_effect_vars());
        }
        for eff in &imp.output_effs {
            eff.fill_with_inner_effect_vars(&mut impl_vars);
        }
        let used = requested_vars
            .iter()
            .chain(&impl_vars)
            .map(|var| var.name() + 1)
            .max()
            .unwrap_or(0);
        while ty_inf.effect_var_count() < used {
            ty_inf.fresh_effect_var();
        }
        let mut requested_vars = requested_vars.into_iter().collect::<Vec<_>>();
        requested_vars.sort_by_key(|var| var.name());
        let renaming: InstSubst = (
            FxHashMap::default(),
            requested_vars
                .into_iter()
                .map(|var| {
                    let renamed = if quantified_effect_vars.contains(&var) {
                        ty_inf.fresh_rigid_effect_var()
                    } else {
                        ty_inf.fresh_effect_var()
                    };
                    (var, EffType::single_variable(renamed))
                })
                .collect(),
        );
        let requested_output_tys = requested_output_tys.map(|tys| {
            tys.iter()
                .map(|ty| ty.map(&mut SimpleInstantiationMapper::new(&renaming)))
                .collect::<Vec<_>>()
        });
        let requested_output_effs = requested_output_effs.map(|effs| {
            effs.iter()
                .map(|eff| eff.instantiate(&renaming.1))
                .collect::<Vec<_>>()
        });
        if let Some(requested_output_tys) = &requested_output_tys {
            for (impl_ty, requested_ty) in imp.output_tys.iter().zip(requested_output_tys.iter()) {
                if ty_inf
                    .unify_same_type_with_sub_effects(*impl_ty, fn_span, *requested_ty, fn_span)
                    .is_err()
                {
                    return false;
                }
            }
        }
        if let Some(requested_output_effs) = &requested_output_effs {
            let polarities = self.output_effect_polarities(imp.trait_id);
            for ((impl_eff, requested_eff), polarity) in imp
                .output_effs
                .iter()
                .zip(requested_output_effs.iter())
                .zip(polarities)
            {
                if Self::match_trait_output_effect(
                    &mut ty_inf,
                    impl_eff,
                    requested_eff,
                    polarity,
                    fn_span,
                )
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
    /// The algorithm discards incompatible outer input constructors, then probes
    /// the remaining visible impls under a snapshot of the unifier. If exactly one candidate remains
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
        answer_used: bool,
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
        // A cycle, or nesting over ever-growing types, learns nothing conclusive.
        if self.active_improvements.len() > IMPROVEMENT_DEPTH_LIMIT
            || !self.active_improvements.insert(key.clone())
        {
            return Ok(TraitImprovementMatch::Unknown);
        }
        let result = self.improve_trait_application_match_actual(
            ty_inf,
            trait_id,
            input_tys,
            output_tys,
            output_effs,
            assumptions,
            answer_used,
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
        answer_used: bool,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        // Resolve current input bindings before testing heads. Candidate variables
        // belong to the impl's own namespace and must remain wildcards here.
        let normalized_inputs = ty_inf.substitute_in_types(input_tys);
        // A written generic stands for every type: an impl that fits only by narrowing it may
        // apply to some instances, but cannot be selected.
        let generics = ty_inf.declared_generic_roots();
        // When only written generics are unknown and nobody reads the answer, the requirement stays
        // on the caller's signature whatever impls exist, so no impl needs to be looked at. In
        // particular, this does not wait for a pending impl that calls this function.
        if !answer_used
            && !generics.is_empty()
            && self.nothing_to_learn(
                ty_inf,
                trait_id,
                &normalized_inputs,
                output_tys,
                output_effs,
                &generics,
            )
        {
            return Ok(TraitImprovementMatch::Unknown);
        }
        let candidates = self.improvement_candidates(trait_id, &normalized_inputs);
        let output_polarities = self.output_effect_polarities(trait_id);
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
            let mut snapshot = ty_inf.snapshot();
            // Concrete candidates only run unification against `ty_inf` and never reach `match_blanket_impl`, so they do not need a probe.
            // Skipping the probe avoids cloning the impl table once per concrete candidate, which is the dominant cost of this loop.
            let matched = match &candidate {
                TraitImprovementCandidate::Concrete { .. } => Self::improvement_candidate_matches(
                    &mut NeverProbe,
                    ty_inf,
                    &candidate,
                    &output_polarities,
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
                        &output_polarities,
                        input_tys,
                        output_tys,
                        output_effs,
                        assumptions,
                        fn_span,
                        arena,
                    )?
                }
            };
            // Effects never decide which candidates there are: one ruled out by them alone remains,
            // with what it would teach unknown.
            let matched = if matches!(matched, TraitImprovementMatch::No) {
                ty_inf.rollback_to(snapshot);
                let structural_snapshot = ty_inf.snapshot();
                let by_structure = match &candidate {
                    TraitImprovementCandidate::Concrete { .. } => {
                        Self::improvement_candidate_applies_by_structure(
                            &mut NeverProbe,
                            ty_inf,
                            &candidate,
                            input_tys,
                            output_tys,
                            assumptions,
                            fn_span,
                            arena,
                        )?
                    }
                    TraitImprovementCandidate::Blanket { .. } => {
                        let mut query = LazyTraitSolverProbe::new(self);
                        Self::improvement_candidate_applies_by_structure(
                            &mut query,
                            ty_inf,
                            &candidate,
                            input_tys,
                            output_tys,
                            assumptions,
                            fn_span,
                            arena,
                        )?
                    }
                };
                ty_inf.rollback_to(structural_snapshot);
                snapshot = ty_inf.snapshot();
                if by_structure {
                    TraitImprovementMatch::Unknown
                } else {
                    TraitImprovementMatch::No
                }
            } else {
                matched
            };
            let improved_input_tys = ty_inf.substitute_in_types(input_tys);
            let improved_output_tys =
                output_tys.map(|output_tys| ty_inf.substitute_in_types(output_tys));
            let keeps_generics = ty_inf.declared_generics_intact(&generics);
            ty_inf.rollback_to(snapshot);
            use TraitImprovementMatch::*;
            match matched {
                No => {}
                // This candidate fits only some instances of a written generic, so it may apply
                // but cannot be selected.
                Unknown | Yes if !keeps_generics => {
                    found_multiple_candidates = true;
                    unique_candidate = None;
                }
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
        // A pending impl may be another candidate, or the only one. One that fits only by
        // narrowing a written generic cannot be selected, but it can prevent selecting another.
        if self.impls.pending.blocks(trait_id, &normalized_inputs) {
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
                        &output_polarities,
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
                &output_polarities,
                input_tys,
                output_tys,
                output_effs,
                assumptions,
                fn_span,
                arena,
            ),
        }
    }

    /// Whether the written generics in `generics` are all that a trait application leaves unknown.
    fn nothing_to_learn(
        &self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        generics: &[Type],
    ) -> bool {
        let trait_def = self.trait_def(trait_id);
        if (output_tys.is_none() && trait_def.output_type_count() > 0)
            || (output_effs.is_none() && trait_def.output_effect_count() > 0)
        {
            return false;
        }
        let output_tys = ty_inf.substitute_in_types(output_tys.unwrap_or_default());
        let output_effs = ty_inf.substitute_in_effect_types(output_effs.unwrap_or_default());
        let tys = || input_tys.iter().chain(&output_tys);
        output_effs.iter().all(|eff| eff.inner_vars().is_empty())
            && tys()
                .all(|ty| ty.inner_effect_vars().is_empty() && ty.inner_mut_ty_vars().is_empty())
            && tys()
                .flat_map(TypeLike::inner_ty_vars)
                .all(|var| generics.contains(&Type::variable(var)))
    }

    /// Try to improve a deferred trait application from its partially known
    /// inputs and outputs.
    ///
    /// The algorithm discards incompatible outer input constructors, then probes
    /// the remaining visible impls under a snapshot of the unifier. If exactly one candidate remains
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
                false,
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
            let Some((_, ass_trait_id, ass_input_tys, ass_output_tys, ass_output_effs, _)) =
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
        imp_output_tys: &[Type],
        imp_output_effs: &[EffType],
        imp_constraints: &[PubTypeConstraint],
        imp_ty_var_count: u32,
        imp_eff_var_count: u32,
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
            for ty in imp_input_tys.iter().chain(imp_output_tys) {
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
        // Every effect variable of the impl, wherever it occurs, is one of its quantifiers.
        for eff in imp_output_effs {
            eff.fill_with_inner_effect_vars(&mut eff_vars);
        }
        assert_eq!(
            eff_vars,
            (0..imp_eff_var_count).map(EffectVar::new).collect()
        );
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
        output_polarities: &[EffectPolarity],
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
        let local_effects_start = ty_inf.effect_var_count();
        let inst_subst = (
            ty_inf.fresh_type_var_subst(imp_ty_var_count),
            ty_inf.fresh_effect_var_subst(imp_eff_var_count),
        );
        let mut mapper = BitmapInstantiationMapper::new(&inst_subst);
        let imp_input_tys = instantiate_types(imp_input_tys, &mut mapper);
        let mut imp_output_tys = instantiate_types(imp_output_tys, &mut mapper);
        let mut imp_output_effs: Vec<_> = imp_output_effs
            .iter()
            .map(|eff| mapper.map_effect_type(eff))
            .collect();
        let mut runtime_requirements = Vec::new();
        let structural = matches!(
            mode,
            BlanketConstraintMode::Structural | BlanketConstraintMode::StructuralAllowUnknown
        );

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
            for ((imp_output_eff, output_eff), polarity) in imp_output_effs
                .iter()
                .zip(output_effs.iter())
                .zip(output_polarities)
            {
                if Self::match_trait_output_effect(
                    ty_inf,
                    imp_output_eff,
                    output_eff,
                    *polarity,
                    fn_span,
                )
                .is_err()
                {
                    return Ok(BlanketImplMatch::No);
                }
            }
        }

        // Most candidates fail above, so only now pay for instantiating the constraints.
        let remaining = instantiate_types(imp_constraints, &mut mapper)
            .into_iter()
            .enumerate()
            .collect::<Vec<_>>();
        let mut remaining = Self::normalize_blanket_remaining_constraints(ty_inf, remaining);
        loop {
            let old_remaining = mem::take(&mut remaining);
            let mut still_remaining = Vec::new();

            for (constraint_index, constraint) in old_remaining.iter() {
                // Re-substitute the constraint on every pass because earlier
                // solved constraints may have refined the type variables it uses.
                let substituted_constraint = ty_inf.substitute_in_constraint(constraint);
                let Some((
                    _,
                    trait_id,
                    constraint_inputs,
                    constraint_outputs,
                    constraint_output_effs,
                    _span,
                )) = substituted_constraint.as_have_trait()
                else {
                    debug_assert!(substituted_constraint.as_have_trait().is_none());
                    let runtime_requirement = match &substituted_constraint {
                        PubTypeConstraint::ProjectionSubscriptIs {
                            requirement,
                            field,
                            subscript_ty,
                            ..
                        } => Some(DictionaryReq::new_projection_subscript(
                            *requirement,
                            *field,
                            subscript_ty.clone(),
                        )),
                        PubTypeConstraint::TypeHasVariant {
                            variant_ty,
                            tag,
                            payload_ty,
                            ..
                        } => Some(DictionaryReq::new_variant_payload_indirection(
                            *variant_ty,
                            *tag,
                            *payload_ty,
                        )),
                        PubTypeConstraint::VariantPayloadLayout { .. } => {
                            // This is an inference-only trigger. The payload's ordinary `Value`
                            // leaves are separate constraints and therefore separate runtime
                            // requirements; the case-qualified trigger has no ABI slot.
                            continue;
                        }
                        _ => None,
                    };
                    if let Some(unresolved) = query.unify_non_trait_constraint_query(
                        ty_inf,
                        &substituted_constraint,
                        assumptions,
                        arena,
                    )? {
                        still_remaining.push((*constraint_index, unresolved));
                    } else if let Some(req) = runtime_requirement {
                        runtime_requirements.push(ResolvedRuntimeRequirement {
                            index: *constraint_index,
                            req,
                        });
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
                    let solved = if structural {
                        query
                            .solve_outputs_by_structure_query(trait_id, &constraint_inputs, fn_span)
                            .map(|output_tys| (output_tys, Vec::new()))
                    } else {
                        query.solve_outputs_query(
                            trait_id,
                            &constraint_inputs,
                            Some(&constraint_output_effs),
                            fn_span,
                            arena,
                        )
                    };
                    match solved {
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
                let solved_outputs = if structural {
                    instantiate_types(&solved_outputs, &mut EffectErasingMapper)
                } else {
                    solved_outputs
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
                // The nested implementation's outputs relate to the constraint's by their
                // polarity, as at the top level.
                if structural {
                    continue;
                }
                let polarities = query.output_effect_polarities_query(trait_id);
                for ((solved_output_eff, constraint_output_eff), polarity) in solved_output_effs
                    .iter()
                    .zip(constraint_output_effs.iter())
                    .zip(polarities)
                {
                    if Self::match_trait_output_effect(
                        ty_inf,
                        solved_output_eff,
                        constraint_output_eff,
                        polarity,
                        fn_span,
                    )
                    .is_err()
                    {
                        return Ok(BlanketImplMatch::No);
                    }
                }
                runtime_requirements.push(ResolvedRuntimeRequirement {
                    index: *constraint_index,
                    req: DictionaryReq::new_trait_impl(
                        trait_id,
                        constraint_inputs,
                        constraint_outputs,
                        constraint_output_effs,
                    ),
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
                    BlanketConstraintMode::RequireAllResolved
                    | BlanketConstraintMode::Structural => {
                        return Ok(BlanketImplMatch::No);
                    }
                    BlanketConstraintMode::AllowUnknown
                    | BlanketConstraintMode::StructuralAllowUnknown => {
                        return Ok(BlanketImplMatch::Unknown);
                    }
                    BlanketConstraintMode::DeferConcreteObligations => {
                        for (constraint_index, constraint) in still_remaining {
                            let substituted_constraint =
                                ty_inf.substitute_in_constraint(&constraint);
                            let Some((
                                _,
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
                            runtime_requirements.push(ResolvedRuntimeRequirement {
                                index: constraint_index,
                                req: DictionaryReq::new_trait_impl(
                                    trait_id,
                                    constraint_inputs,
                                    constraint_outputs,
                                    constraint_output_effs,
                                ),
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
            for ((imp_output_eff, output_eff), polarity) in imp_output_effs
                .iter()
                .zip(output_effs.iter())
                .zip(output_polarities)
            {
                if Self::match_trait_output_effect(
                    ty_inf,
                    imp_output_eff,
                    output_eff,
                    *polarity,
                    fn_span,
                )
                .is_err()
                {
                    return Ok(BlanketImplMatch::No);
                }
            }
        }

        // In a scratch match, the implementation's own effect variables take their least
        // solution; the caller's own inference, matching for improvement, may still bound them.
        if !matches!(
            mode,
            BlanketConstraintMode::AllowUnknown | BlanketConstraintMode::StructuralAllowUnknown
        ) && ty_inf.minimize_effects_from(local_effects_start).is_err()
        {
            return Ok(BlanketImplMatch::No);
        }
        // The match reads its results through the published effects, but `ty_inf` may be the
        // caller's own inference, which goes on afterwards.
        let effects_finalized = ty_inf.effects_finalized();
        if ty_inf.finalize_effect_dependencies().is_err() {
            return Ok(BlanketImplMatch::No);
        }
        for requirement in &mut runtime_requirements {
            match &mut requirement.req {
                DictionaryReq::ProjectionSubscript { subscript_ty, .. } => {
                    ty_inf.substitute_in_subscript_type_in_place(subscript_ty);
                }
                DictionaryReq::VariantPayloadIndirection {
                    variant_ty,
                    payload_ty,
                    ..
                } => {
                    *variant_ty = ty_inf.substitute_in_type(*variant_ty);
                    *payload_ty = ty_inf.substitute_in_type(*payload_ty);
                }
                DictionaryReq::TraitImpl {
                    input_tys,
                    output_tys,
                    output_effs,
                    ..
                } => {
                    ty_inf.substitute_in_types_in_place(input_tys);
                    ty_inf.substitute_in_types_in_place(output_tys);
                    ty_inf.substitute_in_effect_types_in_place(output_effs);
                }
            }
        }
        runtime_requirements.sort_by_key(|requirement| requirement.index);
        ty_inf.substitute_in_types_in_place(&mut imp_output_tys);
        ty_inf.substitute_in_effect_types_in_place(&mut imp_output_effs);
        let mut instantiation = inst_subst;
        for ty in instantiation.0.values_mut() {
            *ty = ty_inf.substitute_in_type(*ty);
        }
        for eff in instantiation.1.values_mut() {
            *eff = ty_inf.substitute_in_effect_type(eff);
        }
        ty_inf.restore_effects_finalized(effects_finalized);
        Ok(BlanketImplMatch::Yes {
            output_tys: imp_output_tys,
            output_effs: imp_output_effs,
            runtime_requirements,
            instantiation,
        })
    }

    /// Finish solving and release borrowed module definitions before committing
    /// generated functions back to the module.
    #[must_use = "commit the generated functions to the module"]
    pub fn finish(mut self) -> PendingFunctionCollector {
        let initial_count = self.fn_collector.initial_count;
        mem::replace(
            &mut self.fn_collector,
            PendingFunctionCollector::new(initial_count),
        )
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
        let trait_def = trait_def_from_parts(self.current_type_items, self.others, trait_id);
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
        let qualified_name_env = QualifiedNameEnv::new(self.current_type_items, self.others);
        self.impls.add_concrete_pending(
            trait_id,
            trait_def,
            input_types,
            output_types,
            output_effs,
            [],
            vec![function],
            &mut self.fn_collector,
            &qualified_name_env,
        )
    }

    pub(crate) fn snapshot_derived_impl_state(&self) -> DerivedImplSnapshot {
        DerivedImplSnapshot {
            concrete_key_to_id: self.impls.concrete_key_to_id.clone(),
            blanket_key_to_id: self.impls.blanket_key_to_id.clone(),
            generated_value_key_to_id: self.impls.generated_value_key_to_id.clone(),
            application_key_to_id: self.impls.application_key_to_id.clone(),
            impl_data_len: self.impls.data.len(),
            new_function_len: self.fn_collector.new_elements.len(),
        }
    }

    pub(crate) fn rollback_derived_impl_state(&mut self, snapshot: DerivedImplSnapshot) {
        self.impls.concrete_key_to_id = snapshot.concrete_key_to_id;
        self.impls.blanket_key_to_id = snapshot.blanket_key_to_id;
        self.impls.generated_value_key_to_id = snapshot.generated_value_key_to_id;
        self.impls.application_key_to_id = snapshot.application_key_to_id;
        if self.impls.data.len() != snapshot.impl_data_len {
            Rc::make_mut(&mut self.impls.data).truncate(snapshot.impl_data_len);
        }
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
        let trait_def = trait_def_from_parts(self.current_type_items, self.others, trait_id);
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
            let name = self
                .qualified_name_env()
                .disambiguated_impl_method_name(
                    trait_id,
                    trait_def,
                    method_index,
                    input_types,
                    output_types,
                    output_effs,
                    0,
                    0,
                    &[],
                )
                .into();
            self.fn_collector
                .reserve_with_visibility(name, Visibility::Module);
            methods.push(id);
            tys.push(ty);
        }

        let associated_const_tys = trait_def.instantiate_associated_const_tys_for_tys(
            input_types,
            output_types,
            output_effs,
        );
        let associated_const_names = self.impl_associated_const_names(
            trait_id,
            input_types,
            output_types,
            output_effs,
            0,
            0,
            &[],
        );
        let associated_const_getters = TraitImpls::bundle_pending_trivial_associated_const_getters(
            &associated_const_values,
            &associated_const_tys,
            &mut self.fn_collector,
            |index| associated_const_names[index],
        );
        let dictionary_ty = TraitImpls::dictionary_ty(tys, associated_const_tys);
        let dictionary_value = build_dictionary_value(&methods, &associated_const_getters);
        let imp = TraitImpl::new(
            trait_id,
            output_types.to_vec(),
            output_effs.to_vec(),
            methods,
            dictionary_value,
            dictionary_ty,
            false,
            None,
        )
        .with_associated_const_values(associated_const_values)
        .with_associated_const_getters(associated_const_getters);
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
        runtime_requirements: &[DictionaryReq],
        code_entries: impl Into<Vec<(PendingFunctionBody, Vec<LocalDecl>)>>,
    ) {
        let methods = self.impls.data[impl_id.as_index()].methods.clone();
        let trait_def = trait_def_from_parts(self.current_type_items, self.others, trait_id);
        let definitions = trait_def.instantiate_for_tys(input_types, output_types, output_effs);

        let mut code_entries = code_entries.into();
        crate::hir::trait_defaults::complete_pending_methods(
            trait_def,
            &definitions,
            DictionaryReq::new_trait_impl(
                trait_id,
                input_types.to_vec(),
                output_types.to_vec(),
                output_effs.to_vec(),
            ),
            &mut code_entries,
        );

        for ((method_id, definition), (body, locals)) in
            methods.into_iter().zip(definitions).zip(code_entries)
        {
            let runtime_arg_count = definition.arg_names.len();
            let definition = Self::dictionary_entry_definition(
                &definition,
                runtime_requirements,
                body.arena[body.entry_node_id].span,
            );
            self.fn_collector.replace(
                method_id,
                PendingModuleFunction::from_body(definition, body, runtime_arg_count, None, locals),
            );
        }
    }

    /// Whether `requirement` is closed and its application is being solved.
    fn closes_a_cycle(&self, requirement: &DictionaryReq) -> bool {
        let DictionaryReq::TraitImpl {
            trait_id,
            input_tys,
            ..
        } = requirement
        else {
            return false;
        };
        requirement.is_closed_trait_impl()
            && self.solving_stack.contains(&(*trait_id, input_tys.clone()))
    }

    fn blanket_method_requirements(
        &self,
        dictionary: &TraitDictionary,
        method_count: usize,
        prerequisites: &[DictionaryReq],
        self_requirement: DictionaryReq,
    ) -> Vec<BlanketMethodRequirements> {
        (0..method_count)
            .map(|index| {
                let mut requirements = prerequisites.to_vec();
                if dictionary
                    .entry_uses_self_dictionary(TraitDictionaryEntryIndex::from_index(index))
                    && !requirements.contains(&self_requirement)
                {
                    requirements.push(self_requirement.clone());
                }
                // Evidence for an application still being solved closes a cycle of recursive
                // `Value` dictionaries: capturing it would nest them endlessly, so the thunk
                // resolves it itself, once the dictionaries exist.
                let entry_requirements = requirements.iter().filter(|requirement| {
                    **requirement == self_requirement || !self.closes_a_cycle(requirement)
                });
                BlanketMethodRequirements {
                    entry: DictionaryEntryRequirements::canonical(entry_requirements, |id| {
                        self.trait_def(id)
                    }),
                    callee: requirements,
                }
            })
            .collect()
    }

    fn blanket_method_inst_data(
        blanket_ty_var_count: u32,
        blanket_eff_var_count: u32,
        blanket_instantiation: &InstSubst,
        runtime_requirements: Vec<DictionaryReq>,
        fn_span: Location,
    ) -> Result<FnInstData, InternalCompilationError> {
        // Blanket registration guarantees that every method callable quantifies all blanket type
        // variables in canonical numeric order, including variables visible only in impl
        // constraints and therefore absent from the reconstructed trait method signature.
        let ty_args = (0..blanket_ty_var_count)
            .map(TypeVar::new)
            .map(|quantifier| {
                blanket_instantiation
                    .0
                    .get(&quantifier)
                    .copied()
                    .ok_or_else(|| {
                        internal_compilation_error!(Internal {
                            error: format!(
                                "blanket method type quantifier {quantifier} was not resolved"
                            ),
                            span: fn_span,
                        })
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        // Registration likewise quantifies all blanket effect variables, including those visible
        // only in impl constraints.
        let eff_args = (0..blanket_eff_var_count)
            .map(EffectVar::new)
            .map(|quantifier| {
                blanket_instantiation
                    .1
                    .get(&quantifier)
                    .cloned()
                    .ok_or_else(|| {
                        internal_compilation_error!(Internal {
                            error: format!(
                                "blanket method effect quantifier {quantifier} was not resolved"
                            ),
                            span: fn_span,
                        })
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(FnInstData::new(runtime_requirements, ty_args, eff_args))
    }

    fn dictionary_entry_definition(
        definition: &CallableDefinition,
        requirements: &[DictionaryReq],
        span: Location,
    ) -> CallableDefinition {
        if requirements.is_empty() {
            return definition.clone();
        }
        let constraints = requirements
            .iter()
            .map(|requirement| match requirement {
                DictionaryReq::ProjectionSubscript {
                    requirement,
                    field,
                    subscript_ty,
                } => PubTypeConstraint::new_projection_subscript_is(
                    *requirement,
                    span,
                    *field,
                    span,
                    subscript_ty.clone(),
                ),
                DictionaryReq::VariantPayloadIndirection {
                    variant_ty,
                    tag,
                    payload_ty,
                } => PubTypeConstraint::new_type_has_variant(
                    *variant_ty,
                    span,
                    *tag,
                    *payload_ty,
                    span,
                ),
                DictionaryReq::TraitImpl {
                    trait_id,
                    input_tys,
                    output_tys,
                    output_effs,
                } => PubTypeConstraint::new_have_trait(
                    *trait_id,
                    input_tys.clone(),
                    output_tys.clone(),
                    output_effs.clone(),
                    span,
                ),
            })
            .collect();
        let mut definition = definition.clone();
        definition.ty_scheme = TypeScheme::new_infer_quantifiers_with_constraints(
            definition.ty_scheme.ty.clone(),
            constraints,
        );
        definition
    }

    #[allow(clippy::too_many_arguments)]
    fn materialize_blanket_method_thunk(
        &mut self,
        function: LocalFunctionId,
        source_module: Option<ModuleId>,
        definition: &CallableDefinition,
        type_var_count: u32,
        effect_var_count: u32,
        instantiation: &InstSubst,
        requirements: &BlanketMethodRequirements,
        span: Location,
    ) -> Result<PendingModuleFunction, InternalCompilationError> {
        let function = self.function_id(
            source_module.unwrap_or(self.current_type_items.module.id),
            function,
        );
        let inst_data = Self::blanket_method_inst_data(
            type_var_count,
            effect_var_count,
            instantiation,
            requirements.callee.clone(),
            span,
        )?;
        let (body, locals) =
            self.blanket_method_thunk_code_entry(function, definition, &[], inst_data, span)?;
        Ok(PendingModuleFunction::from_body(
            Self::dictionary_entry_definition(definition, requirements.entry.as_slice(), span),
            body,
            definition.arg_names.len(),
            None,
            locals,
        ))
    }

    fn blanket_method_thunk_code_entry(
        &mut self,
        function_id: FunctionId,
        definition: &CallableDefinition,
        explicit_runtime_arg_infos: &[(NodeKind, Type)],
        inst_data: FnInstData,
        fn_span: Location,
    ) -> Result<(PendingFunctionBody, Vec<LocalDecl>), InternalCompilationError> {
        let locals = definition.gen_locals_no_bounds(
            repeat(Location::new_synthesized()),
            Location::new_synthesized(),
        );
        let mut body_arena = NodeArena::default();

        let explicit_runtime_args = explicit_runtime_arg_infos
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
        let argument_passing = arg_conventions_for_args(&definition.ty_scheme.ty.args);
        let arguments = CallArgument::from_values_and_passing(argument_values, argument_passing);

        let apply = NodeKind::StaticApply(b(StaticApplication {
            function: function_id,
            function_path: None,
            function_span: fn_span,
            extra_arguments: explicit_runtime_args,
            argument_names: definition.arg_names.clone(),
            argument_name_hint_policy: UnnamedArg::None,
            arguments,
            ty: CallImplType::new(
                definition.ty_scheme.ty.clone(),
                definition.result_convention,
            ),
            inst_data,
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
    /// An absence that a pending impl may fill is recorded as blocked.
    pub fn has_concrete_impl(&self, key: &ConcreteTraitImplKey) -> bool {
        let found = self.impls.concrete_key_to_id.contains_key(key)
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
            });
        if !found {
            self.impls.pending.blocks(key.trait_id, &key.input_tys);
        }
        found
    }

    /// Whether an implementation applies to these inputs by structure, with effects ignored,
    /// as selection sees them, without keeping what solving generates.
    pub(crate) fn has_impl_by_structure(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
    ) -> bool {
        self.solve_outputs_by_structure_query(trait_id, input_tys, fn_span)
            .is_ok()
    }

    /// Get a concrete trait implementation by its key, without performing any solving.
    /// This searches in current module first, then in other modules.
    /// Only public implementations from other modules are considered.
    /// If found in other modules, the value dependencies are updated.
    pub fn get_concrete_impl(&mut self, key: &ConcreteTraitImplKey) -> Option<TraitImplId> {
        if let Some(id) = self.impls.concrete_key_to_id.get(key) {
            return Some(TraitImplId::new(self.current_type_items.module.id, *id));
        }
        let found = self.others.enumerates().find_map(|(module_id, entry, _)| {
            entry.module().and_then(|module| {
                let impls = &module.impls;
                impls.concrete_key_to_id.get(key).and_then(|id| {
                    let imp = &impls.data[id.as_index()];
                    if self.can_use_other_impl(module_id, imp) {
                        Some((module_id, *id))
                    } else {
                        None
                    }
                })
            })
        });
        found.map(|(module_id, impl_id)| {
            self.deps.insert(module_id);
            TraitImplId::new(module_id, impl_id)
        })
    }

    /// Print all known implementations for the given trait id.
    fn log_debug_impls(&self, trait_id: TraitId) {
        if !log::log_enabled!(log::Level::Trace) {
            return;
        }
        log::trace!("In current module:");
        let mut fake_current = Module::new(
            self.current_type_items.module.id,
            self.current_type_items.module.path.clone(),
        );
        fake_current.type_aliases = self.current_type_items.type_aliases.clone();
        fake_current.traits = self.current_type_items.traits.to_vec();
        let env = ModuleEnv::new(&fake_current, self.others);
        self.impls.log_debug_impls_headers(trait_id, env);
        for (module_path, entry) in self.others.iter_named() {
            if let Some(module) = entry.module() {
                let impls = &module.impls;
                if impls.blanket_key_to_id.contains_key(&trait_id) {
                    log::trace!("In module {}:", module_path);
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
        let canonical_input_tys = alpha_canonicalize_types(input_tys);
        let (method_tys, associated_const_tys, dictionary_ty_for_use) = {
            let trait_def = self.trait_def(trait_id);
            assert_eq!(methods.len(), trait_def.methods.len());
            let definitions = trait_def.instantiate_for_tys(&canonical_input_tys, &[], &[]);
            let method_tys = definitions
                .into_iter()
                .map(|definition| Type::function_type(definition.ty_scheme.ty))
                .collect::<Vec<_>>();
            let associated_const_tys =
                trait_def.instantiate_associated_const_tys_for_tys(&canonical_input_tys, &[], &[]);
            let dictionary_ty_for_use = trait_def.get_dictionary_type_for_tys(input_tys, &[], &[]);
            (method_tys, associated_const_tys, dictionary_ty_for_use)
        };
        if input_tys.iter().all(Type::is_constant) {
            let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
            if let Some(local_impl_id) = self.impls.concrete().get(&key).copied() {
                return Ok((
                    TraitImplId::new(self.current_type_items.module.id, local_impl_id),
                    dictionary_ty_for_use,
                ));
            }
        }
        if let Some(local_impl_id) = self
            .impls
            .generated_value_key_to_id
            .get(&canonical_input_tys)
            .copied()
        {
            return Ok((
                TraitImplId::new(self.current_type_items.module.id, local_impl_id),
                dictionary_ty_for_use,
            ));
        }
        let associated_const_names =
            self.impl_associated_const_names(trait_id, &canonical_input_tys, &[], &[], 0, 0, &[]);
        let requirements = generated_value_evidence_types(canonical_input_tys[0], self)
            .unwrap_or_default()
            .into_iter()
            .map(|ty| DictionaryReq::new_trait_impl(trait_id, vec![ty], vec![], vec![]))
            .collect::<Vec<_>>();
        let static_values =
            value_layout_associated_const_values(canonical_input_tys[0], span, self).ok();
        let (associated_const_values, associated_const_getters, getter_requirements) =
            if let Some(values) = static_values {
                let values = values
                    .into_iter()
                    .map(LiteralValue::new_native)
                    .collect::<Vec<_>>();
                let getters = TraitImpls::bundle_pending_trivial_associated_const_getters(
                    &values,
                    &associated_const_tys,
                    &mut self.fn_collector,
                    |index| associated_const_names[index],
                );
                let getter_requirements = vec![Vec::new(); getters.len()];
                (values, getters, getter_requirements)
            } else {
                let mut getters = Vec::with_capacity(associated_const_tys.len());
                let mut getter_requirements = Vec::with_capacity(associated_const_tys.len());
                for index in
                    (0..associated_const_tys.len()).map(TraitAssociatedConstIndex::from_index)
                {
                    getter_requirements.push(
                        value_layout_getter_evidence_types(
                            canonical_input_tys[0],
                            index,
                            span,
                            self,
                        )?
                        .into_iter()
                        .map(|ty| DictionaryReq::new_trait_impl(trait_id, vec![ty], vec![], vec![]))
                        .collect(),
                    );
                    let getter =
                        generated_value_layout_getter(canonical_input_tys[0], index, span, self)?;
                    let id = self.fn_collector.next_id();
                    self.fn_collector.push_with_visibility(
                        associated_const_names[index.as_index()],
                        getter,
                        Visibility::Module,
                    );
                    getters.push(id);
                }
                (Vec::new(), getters, getter_requirements)
            };
        let dictionary_ty = TraitImpls::dictionary_ty(method_tys, associated_const_tys);
        let entry_requirements = (0..methods.len())
            .map(|index| {
                let mut entry = requirements.clone();
                // Function-value methods supply their own ne body and need no self evidence.
                if self.trait_def(trait_id).default_methods[index].is_some()
                    && !canonical_input_tys[0].is_function()
                {
                    entry.push(DictionaryReq::new_trait_impl(
                        trait_id,
                        canonical_input_tys.clone(),
                        vec![],
                        vec![],
                    ));
                }
                entry
            })
            .chain(getter_requirements)
            .map(|requirements| {
                DictionaryEntryRequirements::canonical(&requirements, |id| self.trait_def(id))
            })
            .collect::<Vec<_>>();
        let (capture_schema, entry_capture_mappings) =
            dictionary_capture_plan(trait_id, &canonical_input_tys, &entry_requirements);
        let dictionary_value = build_capturing_dictionary_value(
            &methods,
            &associated_const_getters,
            capture_schema,
            entry_capture_mappings,
        );
        let imp = TraitImpl::new(
            trait_id,
            Vec::new(),
            Vec::new(),
            methods,
            dictionary_value,
            dictionary_ty,
            false,
            None,
        )
        .with_associated_const_values(associated_const_values)
        .with_associated_const_getters(associated_const_getters);
        let impl_id = if input_tys.iter().all(Type::is_constant) {
            let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
            self.impls.add_concrete_struct(key, imp)
        } else {
            let impl_id = self.impls.add_anonymous_dictionary_struct(imp);
            Rc::make_mut(&mut self.impls.generated_value_key_to_id)
                .insert(canonical_input_tys, impl_id);
            impl_id
        };
        Ok((
            TraitImplId::new(self.current_type_items.module.id, impl_id),
            dictionary_ty_for_use,
        ))
    }

    pub(crate) fn materialize_compiler_provided_value_dictionary(
        &mut self,
        arena: &mut NodeArena,
        trait_id: TraitId,
        input_tys: &[Type],
        span: Location,
    ) -> Result<(TraitImplId, Type), InternalCompilationError> {
        // Look through the concrete generated-Value cache before deriving method bodies. The
        // lower-level materializer also checks this key, but by then
        // `generic_value_methods_for_type` has already recursively generated every method. Layout
        // evidence asks for the same ground payload dictionaries frequently, and reserved concrete
        // entries deliberately make this fast path safe for recursive `Value` derivation as well.
        let cached_local_id = if input_tys.iter().all(Type::is_constant) {
            let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
            self.impls.concrete_key_to_id.get(&key).copied()
        } else {
            // Open dictionaries are alpha-canonical caches whose derivation can still contribute
            // constraints in the caller's inference world. Keep their existing lower-level cache
            // check after method derivation; only ground dictionaries are context-free here.
            None
        };
        if let Some(local_id) = cached_local_id {
            let dictionary_ty =
                self.trait_def(trait_id)
                    .get_dictionary_type_for_tys(input_tys, &[], &[]);
            return Ok((
                TraitImplId::new(self.current_type_items.module.id, local_id),
                dictionary_ty,
            ));
        }

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
        self.materialize_generated_value_impl_from_methods(trait_id, input_tys, span, methods)
    }

    fn compiler_provided_value_dictionary_node_kind(
        &mut self,
        arena: &mut NodeArena,
        trait_id: TraitId,
        input_tys: &[Type],
        span: Location,
    ) -> Result<(NodeKind, Type), InternalCompilationError> {
        let (impl_id, dictionary_ty) =
            self.materialize_compiler_provided_value_dictionary(arena, trait_id, input_tys, span)?;
        Ok((get_dictionary(impl_id), dictionary_ty))
    }

    fn runtime_requirements_from_resolved(
        &self,
        resolved_requirements: &[ResolvedRuntimeRequirement],
        source_constraints: &[PubTypeConstraint],
    ) -> Vec<DictionaryReq> {
        let value_trait_id = self.std_trait_id(VALUE_TRAIT_NAME);
        let mut source_slots = Vec::new();
        let mut requirements = Vec::new();
        for resolved in resolved_requirements {
            let source_constraint = &source_constraints[resolved.index];
            let source_requirement = match source_constraint {
                PubTypeConstraint::HaveTrait {
                    trait_id,
                    input_tys,
                    output_tys,
                    ..
                } if !self.trait_def(*trait_id).has_runtime_dictionary_entries()
                    || is_value_trait_for_function_type(
                        *trait_id,
                        self.trait_def(*trait_id),
                        input_tys,
                        output_tys,
                    )
                    || is_function_surface_only_value_trait_application(
                        *trait_id,
                        self.trait_def(*trait_id),
                        input_tys,
                        output_tys,
                    ) =>
                {
                    None
                }
                _ => source_constraint.dictionary_requirement_key(value_trait_id),
            };
            let Some(source_requirement) = source_requirement else {
                continue;
            };

            // Slot sharing is determined by the generic callee's ABI. Two different source slots
            // may resolve to equal requirements at this instantiation; in that case the same
            // dictionary value is passed twice, once in each original position.
            if source_slots.contains(&source_requirement) {
                continue;
            }

            let requirement = match &resolved.req {
                DictionaryReq::ProjectionSubscript { .. } => Some(resolved.req.clone()),
                DictionaryReq::VariantPayloadIndirection { .. } => Some(resolved.req.clone()),
                DictionaryReq::TraitImpl {
                    trait_id,
                    input_tys,
                    output_tys,
                    output_effs,
                } => {
                    let trait_def = self.trait_def(*trait_id);
                    if !trait_def.has_runtime_dictionary_entries() {
                        None
                    } else {
                        Some(DictionaryReq::new_trait_impl(
                            *trait_id,
                            input_tys.clone(),
                            output_tys.clone(),
                            output_effs.clone(),
                        ))
                    }
                }
            };
            if let Some(requirement) = requirement {
                source_slots.push(source_requirement);
                requirements.push(requirement);
            }
        }
        requirements
    }

    fn close_defaulted_requirement_effect_rows(
        requirements: &mut [DictionaryReq],
        variables: &FxHashSet<EffectVar>,
    ) {
        if variables.is_empty() {
            return;
        }
        let mut mapper = DefaultedEffectRowsMapper { variables };
        for requirement in requirements {
            requirement.instantiate_in_place(&mut mapper);
        }
    }

    fn validate_runtime_requirements(
        &mut self,
        resolved_requirements: &[ResolvedRuntimeRequirement],
        fn_span: Location,
        arena: &mut NodeArena,
        validate_outputs: bool,
    ) -> Result<bool, InternalCompilationError> {
        for resolved_requirement in resolved_requirements {
            let DictionaryReq::TraitImpl {
                trait_id,
                input_tys,
                output_tys,
                output_effs,
            } = &resolved_requirement.req
            else {
                continue;
            };
            // Marker traits have no runtime dictionary entries.
            if !self.trait_def(*trait_id).has_runtime_dictionary_entries() {
                continue;
            }
            if self.is_compiler_provided_no_output_trait_query(
                *trait_id,
                input_tys,
                output_tys,
                output_effs,
            ) {
                self.compiler_provided_value_dictionary_node_kind(
                    arena, *trait_id, input_tys, fn_span,
                )?;
                continue;
            }
            let dict_id = match self.solve_impl(*trait_id, input_tys, fn_span, arena) {
                Ok(functions) => functions,
                Err(err) => {
                    log::trace!(
                        "Blanket impl constraint failed while solving {} for {:?}: {:?}",
                        self.trait_def(*trait_id).name,
                        input_tys,
                        err
                    );
                    return Ok(false);
                }
            };
            let dict_impl_data = self.get_impl_data_by_id(dict_id);
            // By structure, only the types of the outputs count, without their effects.
            if self.selecting_by_structure {
                if validate_outputs
                    && instantiate_types(&dict_impl_data.output_tys, &mut EffectErasingMapper)
                        != *output_tys
                {
                    return Ok(false);
                }
                continue;
            }
            // Output effects relate by their polarity, as when matching.
            if validate_outputs
                && (dict_impl_data.output_tys != *output_tys
                    || !dict_impl_data
                        .output_effs
                        .iter()
                        .zip(output_effs.iter())
                        .zip(self.output_effect_polarities(*trait_id))
                        .all(|((solved_eff, constraint_eff), polarity)| {
                            output_effect_fits(solved_eff, constraint_eff, polarity)
                        }))
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Get a concrete trait implementation for the given trait id and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If matching blanket implementation is found, a derivation is attempted, if available.
    /// Otherwise an error is returned.
    /// This is the trait solver's core function.
    /// The implementation for the application `trait_id` at `input_tys`, requested with the
    /// outputs it was inferred with: a dictionary is for the application it is requested for.
    /// Outputs that are missing or still open are left out of the request.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn solve_impl_for_application(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
        quantified_effect_vars: &FxHashSet<EffectVar>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImplId, InternalCompilationError> {
        // Inference is over: an effect variable the caller does not quantify can no longer grow,
        // so it takes its least solution, the empty row. Closing it here, once, leaves nested
        // requests with only the caller's quantified variables.
        let mut flexible = FxHashSet::default();
        for ty in input_tys.iter().chain(output_tys) {
            flexible.extend(ty.inner_effect_vars());
        }
        for eff in output_effs {
            eff.fill_with_inner_effect_vars(&mut flexible);
        }
        flexible.retain(|var| !quantified_effect_vars.contains(var));
        let closed;
        let (input_tys, output_tys, output_effs) = if flexible.is_empty() {
            (input_tys, output_tys, output_effs)
        } else {
            let mut mapper = DefaultedEffectRowsMapper {
                variables: &flexible,
            };
            closed = (
                instantiate_types(input_tys, &mut mapper),
                instantiate_types(output_tys, &mut mapper),
                output_effs
                    .iter()
                    .map(|eff| mapper.map_effect_type(eff))
                    .collect::<Vec<_>>(),
            );
            (&closed.0[..], &closed.1[..], &closed.2[..])
        };
        let trait_def = self.trait_def(trait_id);
        let requested_output_tys = (output_tys.len() == trait_def.output_type_count() as usize
            && output_tys.iter().all(|ty| ty.is_constant()))
        .then_some(output_tys);
        let requested_output_effs =
            (output_effs.len() == trait_def.output_effect_count() as usize).then_some(output_effs);
        let previous = mem::replace(
            &mut self.quantified_request_effect_vars,
            quantified_effect_vars.clone(),
        );
        let result = self.solve_impl_application(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            fn_span,
            arena,
        );
        self.quantified_request_effect_vars = previous;
        result
    }

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
        // The quantified variables name the top-level request's variables only; nested requests
        // made while materializing are in the implementation's variables.
        let quantified_effect_vars = mem::take(&mut self.quantified_request_effect_vars);

        // Cycle detection
        let key = (trait_id, input_tys.to_vec());
        let concrete_key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
        if let Some(imp) = self.get_concrete_impl(&concrete_key) {
            if self.impl_matches_requested_outputs(
                self.get_impl_data_by_id(imp),
                requested_output_tys,
                requested_output_effs,
                &quantified_effect_vars,
                fn_span,
            ) {
                return Ok(imp);
            }
        }
        {
            let canonical_key = application_key(
                trait_id,
                input_tys,
                requested_output_tys,
                requested_output_effs,
            );
            if let Some(local_impl_id) = self
                .impls
                .application_key_to_id
                .get(&canonical_key)
                .copied()
            {
                return Ok(TraitImplId::new(
                    self.current_type_items.module.id,
                    local_impl_id,
                ));
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
            // Callers may read this failure as "this impl does not apply", yet nothing is known.
            self.impls.pending.block_all();
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
            &quantified_effect_vars,
            fn_span,
            arena,
        );

        self.solving_stack.remove(&key);
        self.recursion_depth -= 1;
        result
    }

    #[allow(clippy::too_many_arguments)]
    fn solve_impl_actual(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        quantified_effect_vars: &FxHashSet<EffectVar>,
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
                    trait_id,
                    output_tys: vec![output_ty],
                    output_effs: vec![],
                    methods: vec![],
                    associated_const_values: vec![],
                    associated_const_getters: vec![],
                    dictionary_value: TraitDictionary::new(&[], &[]),
                    dictionary_ty: Type::tuple([]),
                    public: false,
                    source_span: None,
                };
                self.impls.add_concrete_struct(key, imp)
            };
            return Ok(TraitImplId::new(
                self.current_type_items.module.id,
                local_id,
            ));
        }

        // If a concrete implementation is found, return it.
        let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
        if let Some(imp) = self.get_concrete_impl(&key) {
            if self.impl_matches_requested_outputs(
                self.get_impl_data_by_id(imp),
                requested_output_tys,
                requested_output_effs,
                quantified_effect_vars,
                fn_span,
            ) {
                return Ok(imp);
            }
            // The inputs select this impl: outputs differing only in effects are not a reason to
            // look for another one.
            if let Some(requested_output_tys) = requested_output_tys
                && !self.selecting_by_structure
                && instantiate_types(requested_output_tys, &mut EffectErasingMapper)
                    == instantiate_types(
                        &self.get_impl_data_by_id(imp).output_tys,
                        &mut EffectErasingMapper,
                    )
                && requested_output_tys != &self.get_impl_data_by_id(imp).output_tys[..]
            {
                return Err(internal_compilation_error!(TraitImplEffectsMismatch {
                    input_ty: input_tys[0],
                    fn_span,
                }));
            }
        }

        // No concrete implementation found, search for a matching blanket implementation.
        let mut search = CandidateSearch::new(&self.impls.pending);
        let blanket_constraint_mode = if self.selecting_by_structure {
            BlanketConstraintMode::Structural
        } else if trait_id == value_trait_id {
            BlanketConstraintMode::DeferConcreteObligations
        } else {
            BlanketConstraintMode::RequireAllResolved
        };
        if let Some(impl_id) = self.select_blanket_candidate(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            blanket_constraint_mode,
            &mut search,
            fn_span,
            arena,
            |solver, candidate, arena| {
                solver.materialize_blanket_candidate(
                    trait_id,
                    input_tys,
                    requested_output_tys,
                    requested_output_effs,
                    candidate,
                    fn_span,
                    arena,
                )
            },
        )? {
            return Ok(impl_id);
        }

        // A pending impl may still provide this application: neither derive nor conclude that
        // none exists.
        if self.impls.pending.blocks(trait_id, input_tys) {
            return Err(internal_compilation_error!(TraitImplNotFound {
                trait_ref: trait_id,
                input_tys: input_tys.to_vec(),
                fn_span,
            }));
        }

        // No blanket implementation found, look for a derived implementation.
        let (trait_name, derivers) = {
            let trait_def = self.trait_def(trait_id);
            (trait_def.name, trait_def.derivers.clone())
        };
        // Derived implementations do not depend on the effects of the callables in their input
        // types: derive them for these effects at their least solution, which any row includes.
        // This holds because no derived method calls a callable of its input: they print, hash,
        // compare, clone or drop it, and serialization and defaults have no callable instance.
        let effect_vars = input_tys
            .iter()
            .flat_map(TypeLike::inner_effect_vars)
            .collect::<FxHashSet<_>>();
        let erased_input_tys;
        let input_tys = if effect_vars.is_empty() {
            input_tys
        } else {
            let subst = (
                FxHashMap::default(),
                effect_vars
                    .into_iter()
                    .map(|var| (var, EffType::empty()))
                    .collect(),
            );
            let mut mapper = BitmapInstantiationMapper::new(&subst);
            erased_input_tys = input_tys
                .iter()
                .map(|ty| ty.map(&mut mapper))
                .collect::<Vec<_>>();
            let key = ConcreteTraitImplKey::new(trait_id, erased_input_tys.clone());
            if let Some(impl_id) = self.get_concrete_impl(&key) {
                return Ok(impl_id);
            }
            &erased_input_tys
        };
        for derive in derivers {
            if let Some(impl_id) = derive.derive_impl(trait_id, input_tys, fn_span, arena, self)? {
                return Ok(impl_id);
            } else {
                log::trace!(
                    "Tried derivation for trait {} with input types {:?}, but failed.",
                    trait_name,
                    input_tys
                );
            }
        }

        // No matching implementation found.
        log::trace!(
            "No matching impl for trait \"{}\" found. Existing impls:",
            trait_name
        );
        self.log_debug_impls(trait_id);
        if let Some(requested_output_effs) = requested_output_effs
            && let Some(imp) = self.get_concrete_impl(&key)
        {
            let mismatches = self.output_effect_mismatches(
                self.get_impl_data_by_id(imp),
                requested_output_effs,
                quantified_effect_vars,
                fn_span,
            );
            if !mismatches.is_empty() {
                return Err(internal_compilation_error!(
                    TraitImplOutputEffectsMismatch {
                        trait_ref: trait_id,
                        input_tys: input_tys.to_vec(),
                        mismatches,
                        fn_span,
                    }
                ));
            }
        }
        Err(internal_compilation_error!(TraitImplNotFound {
            trait_ref: trait_id,
            input_tys: input_tys.to_vec(),
            fn_span,
        }))
    }

    /// The output effects of `imp` that do not relate to the requested ones by polarity, each with
    /// its name, its declared row and the requested one.
    fn output_effect_mismatches(
        &self,
        imp: &TraitImpl,
        requested_output_effs: &[EffType],
        quantified_effect_vars: &FxHashSet<EffectVar>,
        fn_span: Location,
    ) -> Vec<(Ustr, EffType, EffType)> {
        let names = &self.trait_def(imp.trait_id).output_effect_names;
        (0..imp.output_effs.len().min(requested_output_effs.len()))
            .filter_map(|index| {
                // Request this output alone; the others take the implementation's own rows.
                let mut requested = imp.output_effs.clone();
                requested[index] = requested_output_effs[index].clone();
                (!self.impl_matches_requested_outputs(
                    imp,
                    None,
                    Some(&requested),
                    quantified_effect_vars,
                    fn_span,
                ))
                .then(|| {
                    (
                        names[index],
                        imp.output_effs[index].clone(),
                        requested_output_effs[index].clone(),
                    )
                })
            })
            .collect()
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
        let method_id = self.get_impl_data_by_id(impl_id).methods[index.as_index()];
        Ok(self.function_id(impl_id.module, method_id))
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
        _arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        self.solve_application_outputs_without_materializing(
            trait_id, input_tys, None, None, fn_span,
        )
    }

    /// Solve a full trait application.
    ///
    /// Impl identity is selected by trait id and resolved input types, but
    /// associated output types and effects are application parameters. They are
    /// matched against the selected impl for this application and must not be
    /// treated as canonical values of the input-keyed impl cache.
    /// Resolve an application by the blanket implementation the solver selects for it,
    /// symbolically: return that implementation's outputs and constraints in terms of the
    /// application's own variables, without materializing a dictionary. `None` if no blanket
    /// implementation applies.
    /// The runtime requirements of a matched blanket impl failed. If they hold without any effect,
    /// the impl applies and only its effects are wrong; other failures, such as a cycle, stand.
    fn reject_if_requirements_fail_on_effects(
        &mut self,
        requirements: &[ResolvedRuntimeRequirement],
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<(), InternalCompilationError> {
        if self.selecting_by_structure {
            return Ok(());
        }
        let erased = requirements
            .iter()
            .map(|requirement| ResolvedRuntimeRequirement {
                index: requirement.index,
                req: match &requirement.req {
                    DictionaryReq::TraitImpl {
                        trait_id,
                        input_tys,
                        output_tys,
                        output_effs,
                    } => DictionaryReq::new_trait_impl(
                        *trait_id,
                        instantiate_types(input_tys, &mut EffectErasingMapper),
                        instantiate_types(output_tys, &mut EffectErasingMapper),
                        vec![EffType::empty(); output_effs.len()],
                    ),
                    other => other.clone(),
                },
            })
            .collect::<Vec<_>>();
        let snapshot = self.snapshot_derived_impl_state();
        let mut arena = NodeArena::default();
        self.selecting_by_structure = true;
        let holds = self.validate_runtime_requirements(&erased, fn_span, &mut arena, true);
        self.selecting_by_structure = false;
        self.rollback_derived_impl_state(snapshot);
        if holds? {
            return Err(internal_compilation_error!(TraitImplEffectsMismatch {
                input_ty: input_tys[0],
                fn_span,
            }));
        }
        Ok(())
    }

    /// A blanket impl did not match. If it applies by structure, ignoring all effects, it is
    /// nevertheless the selected impl, since effects never select one: its effects are then wrong,
    /// and no other impl or derivation may serve the application.
    fn reject_if_applies_by_structure(
        &mut self,
        (sub_key, imp_output_tys): (&BlanketTraitImplSubKey, &[Type]),
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        fn_span: Location,
    ) -> Result<(), InternalCompilationError> {
        // Already checking by structure: this candidate's answer is the one being sought.
        if self.selecting_by_structure {
            return Ok(());
        }
        let erased_input_tys = instantiate_types(input_tys, &mut EffectErasingMapper);
        let erased_output_tys =
            requested_output_tys.map(|tys| instantiate_types(tys, &mut EffectErasingMapper));
        let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(Self::type_var_capacity_for_types(
            erased_input_tys
                .iter()
                .chain(erased_output_tys.as_deref().unwrap_or_default()),
        ));
        let snapshot = self.snapshot_derived_impl_state();
        let mut arena = NodeArena::default();
        self.selecting_by_structure = true;
        let matched = Self::match_blanket_impl(
            self,
            &mut ty_inf,
            &instantiate_types(&sub_key.input_tys, &mut EffectErasingMapper),
            &instantiate_types(imp_output_tys, &mut EffectErasingMapper),
            &[],
            &[],
            sub_key.ty_var_count,
            0,
            &instantiate_types(&sub_key.constraints, &mut EffectErasingMapper),
            &erased_input_tys,
            erased_output_tys.as_deref(),
            None,
            ConstraintAssumptions::all(&[]),
            fn_span,
            &mut arena,
            BlanketConstraintMode::Structural,
        );
        self.selecting_by_structure = false;
        self.rollback_derived_impl_state(snapshot);
        if matches!(matched?, BlanketImplMatch::Yes { .. }) {
            return Err(internal_compilation_error!(TraitImplEffectsMismatch {
                input_ty: input_tys[0],
                fn_span,
            }));
        }
        Ok(())
    }

    /// Walk the visible blanket implementations in order and hand each one whose inputs match the
    /// application to `accept`, which validates it and returns its result, or `None` to go on to
    /// the next candidate. A candidate that does not match but applies by structure is rejected,
    /// as effects cannot select another implementation. While a candidate from another module is
    /// matched and accepted, that module is the private impl scope.
    #[allow(clippy::too_many_arguments)]
    fn select_blanket_candidate<R>(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        mode: BlanketConstraintMode,
        search: &mut CandidateSearch,
        fn_span: Location,
        arena: &mut NodeArena,
        mut accept: impl FnMut(
            &mut Self,
            BlanketCandidate<'_>,
            &mut NodeArena,
        ) -> Result<Option<R>, InternalCompilationError>,
    ) -> Result<Option<R>, InternalCompilationError> {
        let output_polarities = self.output_effect_polarities(trait_id);
        // Share the local table to avoid borrowing issues: adding a blanket implementation
        // during the search copies it and leaves this view unchanged.
        let local_blankets = self.impls.blanket_key_to_id.clone();
        let blankets = visible_blanket_impls(&local_blankets, self.others, trait_id);
        let fully_determined = input_tys.iter().all(Type::is_constant);
        // By structure, the candidate is seen without effects, as the application is.
        let by_structure = matches!(mode, BlanketConstraintMode::Structural);
        for (module, blanket_impls) in blankets {
            for (sub_key, impl_id) in blanket_impls.iter() {
                if !input_heads_may_match(&sub_key.input_tys, input_tys) {
                    continue;
                }
                search.next_candidate();
                let (public, declared_output_tys, declared_output_effs) = match module {
                    Some(module_id) => {
                        let imp = &self
                            .others
                            .get(module_id)
                            .unwrap()
                            .module()
                            .unwrap()
                            .impls
                            .data[impl_id.as_index()];
                        (
                            self.can_use_other_impl(module_id, imp),
                            imp.output_tys.clone(),
                            imp.output_effs.clone(),
                        )
                    }
                    None => {
                        let imp = &self.impls.data[impl_id.as_index()];
                        (true, imp.output_tys.clone(), imp.output_effs.clone())
                    }
                };
                if !public {
                    continue;
                }

                #[cfg(debug_assertions)]
                Self::assert_blanket_impl_is_well_formed(
                    &sub_key.input_tys,
                    &declared_output_tys,
                    &declared_output_effs,
                    &sub_key.constraints,
                    sub_key.ty_var_count,
                    sub_key.eff_var_count,
                    input_tys,
                );

                if let Some(module_id) = module {
                    self.private_impl_scope.push(module_id);
                }
                // A closure, so that the scope is restored on every exit, errors included.
                let accepted = (|| {
                    // Match the blanket implementation and resolve its constraints to a fixed point.
                    let mut ty_inf =
                        UnifiedTypeInference::new_with_ty_vars(Self::type_var_capacity_for_types(
                            input_tys
                                .iter()
                                .chain(requested_output_tys.unwrap_or_default()),
                        ));
                    // Reserve the application's effect variables, so that the implementation's
                    // fresh effect variables cannot alias them.
                    for _ in 0..Self::effect_var_capacity(
                        input_tys
                            .iter()
                            .chain(requested_output_tys.unwrap_or_default()),
                        requested_output_effs.unwrap_or_default(),
                    ) {
                        ty_inf.fresh_effect_var();
                    }
                    let erased = by_structure.then(|| {
                        (
                            instantiate_types(&sub_key.input_tys, &mut EffectErasingMapper),
                            instantiate_types(&declared_output_tys, &mut EffectErasingMapper),
                            instantiate_types(&sub_key.constraints, &mut EffectErasingMapper),
                            vec![EffType::empty(); declared_output_effs.len()],
                        )
                    });
                    let (
                        matched_input_tys,
                        matched_output_tys,
                        matched_constraints,
                        matched_output_effs,
                    ) = match &erased {
                        Some((inputs, outputs, constraints, effs)) => {
                            (&inputs[..], &outputs[..], &constraints[..], &effs[..])
                        }
                        None => (
                            &sub_key.input_tys[..],
                            &declared_output_tys[..],
                            &sub_key.constraints[..],
                            &declared_output_effs[..],
                        ),
                    };
                    let blanket_match = Self::match_blanket_impl(
                        self,
                        &mut ty_inf,
                        matched_input_tys,
                        matched_output_tys,
                        matched_output_effs,
                        &output_polarities,
                        sub_key.ty_var_count,
                        sub_key.eff_var_count,
                        matched_constraints,
                        input_tys,
                        requested_output_tys,
                        requested_output_effs,
                        ConstraintAssumptions::all(&[]),
                        fn_span,
                        arena,
                        mode,
                    )?;
                    let BlanketImplMatch::Yes {
                        output_tys,
                        output_effs,
                        runtime_requirements,
                        instantiation,
                    } = blanket_match
                    else {
                        self.reject_if_applies_by_structure(
                            (sub_key, &declared_output_tys),
                            input_tys,
                            requested_output_tys,
                            fn_span,
                        )?;
                        return Ok(None);
                    };
                    let candidate = BlanketCandidate {
                        module,
                        impl_id: *impl_id,
                        sub_key,
                        declared_output_tys,
                        declared_output_effs,
                        output_tys,
                        output_effs,
                        runtime_requirements,
                        instantiation,
                    };
                    accept(self, candidate, arena)
                })();
                if module.is_some() {
                    self.private_impl_scope.pop();
                }
                if let Some(result) = accepted? {
                    if fully_determined {
                        search.succeed();
                    }
                    return Ok(Some(result));
                }
            }
        }
        Ok(None)
    }

    /// Accept a blanket candidate for `solve_impl_actual` by materializing its dictionary, or
    /// return `None` when its runtime requirements fail, to go on to the next candidate.
    #[allow(clippy::too_many_arguments)]
    fn materialize_blanket_candidate(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        candidate: BlanketCandidate<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        let value_trait_id = self.std_trait_id(VALUE_TRAIT_NAME);
        let BlanketCandidate {
            module: imp_module_id,
            impl_id,
            sub_key,
            output_tys,
            output_effs,
            runtime_requirements: resolved_runtime_requirements,
            instantiation: blanket_instantiation,
            ..
        } = candidate;
        let imp_constraints = &sub_key.constraints;
        let imp_ty_var_count = sub_key.ty_var_count;
        let imp_eff_var_count = sub_key.eff_var_count;
        let defaulted_output_effect_vars = FxHashSet::default();

        // Non-Value blanket impls can materialize all constraint dictionaries up front.
        if trait_id != value_trait_id {
            let mut runtime_requirements = self.runtime_requirements_from_resolved(
                &resolved_runtime_requirements,
                imp_constraints,
            );
            Self::close_defaulted_requirement_effect_rows(
                &mut runtime_requirements,
                &defaulted_output_effect_vars,
            );
            if !self.validate_runtime_requirements(
                &resolved_runtime_requirements,
                fn_span,
                arena,
                false,
            )? {
                let rejected = self.reject_if_requirements_fail_on_effects(
                    &resolved_runtime_requirements,
                    input_tys,
                    fn_span,
                );
                rejected?;
                return Ok(None);
            }

            // Succeeded? First get the blanket implementation data and compute the output types.
            let impls = if let Some(module_id) = imp_module_id {
                &self.others.get(module_id).unwrap().module().unwrap().impls
            } else {
                #[allow(clippy::needless_borrow)] // clippy has a bug here as of Rust 1.90
                &self.impls
            };
            let imp = &impls.data[impl_id.as_index()];
            // Self evidence belongs to method execution, not to blanket selection.
            // The selected dictionary supplies it through the existing entry mapping.
            let method_requirements = self.blanket_method_requirements(
                &imp.dictionary_value,
                imp.methods.len(),
                &runtime_requirements,
                DictionaryReq::new_trait_impl(
                    trait_id,
                    input_tys.to_vec(),
                    output_tys.clone(),
                    output_effs.clone(),
                ),
            );

            let associated_const_values = {
                let trait_def =
                    trait_def_from_parts(self.current_type_items, self.others, trait_id);
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
            let trait_def = trait_def_from_parts(self.current_type_items, self.others, trait_id);
            let definitions = trait_def.instantiate_for_tys(input_tys, &output_tys, &output_effs);
            let gen_functions = imp.methods.clone(); // clone to avoid borrowing issues
            let mut methods = Vec::with_capacity(gen_functions.len());
            let mut tys = Vec::with_capacity(gen_functions.len());
            for (method_index, (fn_id, def)) in gen_functions.iter().zip(definitions).enumerate() {
                let requirements = &method_requirements[method_index];
                let method_index = TraitMethodIndex::from_index(method_index);
                // Build the concrete function type and hash its signature.
                let fn_ty = Type::function_type(def.ty_scheme.ty.clone());

                // Is the generic function from another module, or do we need to pass constraint dictionaries?
                let id = if requirements.callee.is_empty() && imp_module_id.is_none() {
                    // No, so we can just use the generic function as is.
                    *fn_id
                } else {
                    let function = self.materialize_blanket_method_thunk(
                        *fn_id,
                        imp_module_id,
                        &def,
                        imp_ty_var_count,
                        imp_eff_var_count,
                        &blanket_instantiation,
                        requirements,
                        fn_span,
                    )?;
                    let name = Ustr::from(&format!(
                        "{}-thunk",
                        self.qualified_name_env().disambiguated_impl_method_name(
                            trait_id,
                            trait_def,
                            method_index,
                            input_tys,
                            &output_tys,
                            &output_effs,
                            sub_key.ty_var_count,
                            sub_key.eff_var_count,
                            &sub_key.constraints,
                        )
                    ));
                    let id = self.fn_collector.next_id();
                    self.fn_collector
                        .push_with_visibility(name, function, Visibility::Module);
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
            let associated_const_names = self.impl_associated_const_names(
                trait_id,
                input_tys,
                &output_tys,
                &output_effs,
                sub_key.ty_var_count,
                sub_key.eff_var_count,
                &sub_key.constraints,
            );
            let associated_const_getters =
                TraitImpls::bundle_pending_trivial_associated_const_getters(
                    &associated_const_values,
                    &associated_const_tys,
                    &mut self.fn_collector,
                    |index| associated_const_names[index],
                );
            let dictionary_ty = TraitImpls::dictionary_ty(tys, associated_const_tys);
            let dictionary_value = blanket_dictionary(
                trait_id,
                input_tys,
                &methods,
                &associated_const_getters,
                &method_requirements,
            );
            let imp = TraitImpl::new(
                trait_id,
                output_tys.clone(),
                output_effs.clone(),
                methods,
                dictionary_value,
                dictionary_ty,
                false,
                None,
            )
            .with_associated_const_values(associated_const_values)
            .with_associated_const_getters(associated_const_getters);
            // A generated dictionary denotes its full application, outputs included: it is
            // indexed by its request and by the outputs it has, so that a later request
            // naming either finds it, and never serves another application.
            let local_impl_id = self.impls.add_anonymous_dictionary_struct(imp);
            let requested_key = application_key(
                trait_id,
                input_tys,
                requested_output_tys,
                requested_output_effs,
            );
            let resulting_key =
                application_key(trait_id, input_tys, Some(&output_tys), Some(&output_effs));
            for key in [requested_key, resulting_key] {
                Rc::make_mut(&mut self.impls.application_key_to_id).insert(key, local_impl_id);
            }

            return Ok(Some(
                self.impl_id(self.current_type_items.module.id, local_impl_id),
            ));
        }

        // Value blanket impls may be recursive, so reserve the concrete impl before
        // materializing any deferred constraint dictionaries.
        let imp = if let Some(module_id) = imp_module_id {
            &self
                .others
                .get(module_id)
                .unwrap()
                .module()
                .unwrap()
                .impls
                .data[impl_id.as_index()]
        } else {
            &self.impls.data[impl_id.as_index()]
        };
        let imp_associated_const_values = imp.associated_const_values.clone();
        let gen_functions = imp.methods.clone();
        let source_dictionary = imp.dictionary_value.clone();
        let associated_const_values = {
            let trait_def = trait_def_from_parts(self.current_type_items, self.others, trait_id);
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
        let mut runtime_requirements = self
            .runtime_requirements_from_resolved(&resolved_runtime_requirements, imp_constraints);
        Self::close_defaulted_requirement_effect_rows(
            &mut runtime_requirements,
            &defaulted_output_effect_vars,
        );
        let method_requirements = self.blanket_method_requirements(
            &source_dictionary,
            gen_functions.len(),
            &runtime_requirements,
            DictionaryReq::new_trait_impl(
                trait_id,
                input_tys.to_vec(),
                output_tys.clone(),
                output_effs.clone(),
            ),
        );
        if !self.validate_runtime_requirements(
            &resolved_runtime_requirements,
            fn_span,
            arena,
            true,
        )? {
            self.rollback_derived_impl_state(materialization_snapshot);
            let rejected = self.reject_if_requirements_fail_on_effects(
                &resolved_runtime_requirements,
                input_tys,
                fn_span,
            );
            rejected?;
            return Ok(None);
        }

        // Then, for every function in the blanket implementation, if needed create a thunk function
        // importing it and closing over the constraint dictionaries.
        let definitions = trait_def_from_parts(self.current_type_items, self.others, trait_id)
            .instantiate_for_tys(input_tys, &output_tys, &output_effs);
        let functions = gen_functions
            .iter()
            .zip(definitions)
            .zip(&method_requirements)
            .map(|((fn_id, def), requirements)| {
                self.materialize_blanket_method_thunk(
                    *fn_id,
                    imp_module_id,
                    &def,
                    imp_ty_var_count,
                    imp_eff_var_count,
                    &blanket_instantiation,
                    requirements,
                    fn_span,
                )
            })
            .collect::<Result<Vec<_>, InternalCompilationError>>()?;
        let methods = self.impls.data[local_impl_id.as_index()].methods.clone();
        assert_eq!(methods.len(), functions.len());
        for (id, function) in methods.iter().copied().zip(functions) {
            self.fn_collector.replace(id, function);
        }
        let associated_const_getters = self.impls.data[local_impl_id.as_index()]
            .associated_const_getters
            .clone();
        Rc::make_mut(&mut self.impls.data)[local_impl_id.as_index()].dictionary_value =
            blanket_dictionary(
                trait_id,
                input_tys,
                &methods,
                &associated_const_getters,
                &method_requirements,
            );

        Ok(Some(
            self.impl_id(self.current_type_items.module.id, local_impl_id),
        ))
    }

    pub(crate) fn resolve_application_symbolically(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: &[Type],
        requested_output_effs: &[EffType],
        fn_span: Location,
    ) -> Result<Option<SymbolicApplication>, InternalCompilationError> {
        // Without effect variables, the prerequisites of a `Value` impl cannot constrain the
        // caller: dictionary construction checks them exactly.
        if trait_id == self.std_trait_id(REPR_TRAIT_NAME)
            || (trait_id == self.std_trait_id(VALUE_TRAIT_NAME)
                && input_tys.iter().all(|ty| ty.inner_effect_vars().is_empty()))
        {
            return Ok(None);
        }
        let snapshot = self.snapshot_derived_impl_state();
        let result = self.resolve_application_symbolically_inner(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            fn_span,
        );
        self.rollback_derived_impl_state(snapshot);
        result
    }

    fn resolve_application_symbolically_inner(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: &[Type],
        requested_output_effs: &[EffType],
        fn_span: Location,
    ) -> Result<Option<SymbolicApplication>, InternalCompilationError> {
        let type_var_base =
            Self::type_var_capacity_for_types(input_tys.iter().chain(requested_output_tys));
        let effect_var_base = Self::effect_var_capacity(
            input_tys.iter().chain(requested_output_tys),
            requested_output_effs,
        );
        let mut arena = NodeArena::default();
        let mut search = CandidateSearch::new(&self.impls.pending);
        // `Value` is selected by structure, as inference does: a nested prerequisite need only
        // hold by structure, its effects become obligations through the instantiated head. Other
        // traits are selected as `solve_impl_actual` does.
        let by_structure = trait_id == self.std_trait_id(VALUE_TRAIT_NAME);
        let (selection_input_tys, mode) = if by_structure {
            (
                instantiate_types(input_tys, &mut EffectErasingMapper),
                BlanketConstraintMode::Structural,
            )
        } else {
            (
                input_tys.to_vec(),
                BlanketConstraintMode::RequireAllResolved,
            )
        };
        let previous = mem::replace(&mut self.selecting_by_structure, by_structure);
        let selected = self.select_blanket_candidate(
            trait_id,
            &selection_input_tys,
            Some(requested_output_tys),
            Some(requested_output_effs),
            mode,
            &mut search,
            fn_span,
            &mut arena,
            |_, candidate, _| {
                Ok(Some(Self::instantiate_symbolic_head(
                    &candidate,
                    input_tys,
                    type_var_base,
                    effect_var_base,
                    fn_span,
                )))
            },
        );
        self.selecting_by_structure = previous;
        selected?.transpose()
    }

    /// Instantiate the head of a selected blanket candidate alone, keeping its constraints as
    /// obligations in terms of the application's variables.
    fn instantiate_symbolic_head(
        candidate: &BlanketCandidate<'_>,
        input_tys: &[Type],
        type_var_base: u32,
        effect_var_base: u32,
        fn_span: Location,
    ) -> Result<SymbolicApplication, InternalCompilationError> {
        let sub_key = candidate.sub_key;
        let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(type_var_base);
        for _ in 0..effect_var_base {
            ty_inf.fresh_effect_var();
        }
        let inst_subst = (
            ty_inf.fresh_type_var_subst(sub_key.ty_var_count),
            ty_inf.fresh_effect_var_subst(sub_key.eff_var_count),
        );
        let mut mapper = BitmapInstantiationMapper::new(&inst_subst);
        let imp_input_tys = instantiate_types(&sub_key.input_tys, &mut mapper);
        let output_tys = instantiate_types(&candidate.declared_output_tys, &mut mapper);
        let output_effs = candidate
            .declared_output_effs
            .iter()
            .map(|eff| mapper.map_effect_type(eff))
            .collect::<Vec<_>>();
        let constraints = sub_key
            .constraints
            .iter()
            // Selection checked the constraints; they matter here only for the outputs
            // they determine, which keep the variables of the application.
            .filter(|constraint| match constraint {
                PubTypeConstraint::HaveTrait {
                    output_tys,
                    output_effs,
                    ..
                } => !output_tys.is_empty() || !output_effs.is_empty(),
                PubTypeConstraint::VariantPayloadLayout { .. } => false,
                _ => true,
            })
            .map(|constraint| constraint.map(&mut mapper))
            .collect::<Vec<_>>();
        for (imp_input_ty, input_ty) in imp_input_tys.iter().zip(input_tys) {
            ty_inf.unify_same_type_with_sub_effects(*imp_input_ty, fn_span, *input_ty, fn_span)?;
        }
        // A prerequisite over the application's effects still has to hold for them: the
        // scratch match above let it choose them.
        let effect_prerequisites = sub_key
            .constraints
            .iter()
            .filter(|constraint| {
                matches!(constraint,
                    PubTypeConstraint::HaveTrait { output_tys, output_effs, .. }
                    if output_tys.is_empty() && output_effs.is_empty())
            })
            .map(|constraint| constraint.map(&mut mapper))
            .filter(|constraint| {
                !ty_inf
                    .substitute_in_constraint(constraint)
                    .inner_effect_vars()
                    .is_empty()
            })
            .collect::<Vec<_>>();
        let constraints = constraints
            .into_iter()
            .chain(effect_prerequisites)
            .collect::<Vec<_>>();
        Ok(SymbolicApplication {
            input_tys: imp_input_tys,
            output_tys: ty_inf.substitute_in_types(&output_tys),
            output_effs: ty_inf.substitute_in_effect_types(&output_effs),
            obligations: constraints
                .iter()
                .map(|constraint| ty_inf.substitute_in_constraint(constraint))
                .collect(),
            private_impl_scope: candidate.module,
            type_var_base,
            effect_var_base,
        })
    }

    pub fn solve_application_outputs(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: &[Type],
        requested_output_effs: &[EffType],
        fn_span: Location,
        _arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        self.solve_application_outputs_without_materializing(
            trait_id,
            input_tys,
            Some(requested_output_tys),
            Some(requested_output_effs),
            fn_span,
        )
    }

    /// Return a cached answer for a fully concrete, unconstrained output query.
    ///
    /// The cache contains only semantic outputs, never an implementation identity or generated
    /// artifact. Private visibility is part of the key.
    fn cached_unmaterialized_outputs(
        &self,
        trait_id: TraitId,
        input_tys: &[Type],
    ) -> Option<&TraitOutputCacheEntry> {
        if !input_tys.iter().all(|ty| ty.is_constant()) {
            return None;
        }
        let private_impl_module = self.private_impl_scope.last().copied();
        self.unmaterialized_output_cache
            .get(&trait_id)?
            .iter()
            .find(|entry| {
                entry.input_tys == input_tys
                    && entry.private_impl_module == private_impl_module
                    && entry.privileged_impl_module == self.privileged_impl_module
            })
    }

    fn outputs_are_cacheable(output_tys: &[Type], output_effs: &[EffType]) -> bool {
        output_tys.iter().all(|ty| ty.is_constant())
            && output_effs.iter().all(|eff| !eff.has_variables())
    }

    fn cache_unmaterialized_outputs(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) {
        if !input_tys.iter().all(|ty| ty.is_constant())
            || !Self::outputs_are_cacheable(output_tys, output_effs)
        {
            return;
        }
        let private_impl_module = self.private_impl_scope.last().copied();
        let entries = self
            .unmaterialized_output_cache
            .entry(trait_id)
            .or_default();
        if let Some(entry) = entries.iter().find(|entry| {
            entry.input_tys == input_tys
                && entry.private_impl_module == private_impl_module
                && entry.privileged_impl_module == self.privileged_impl_module
        }) {
            debug_assert_eq!(entry.output_tys, output_tys);
            debug_assert_eq!(entry.output_effs, output_effs);
            return;
        }
        entries.push(TraitOutputCacheEntry {
            input_tys: input_tys.to_vec(),
            private_impl_module,
            privileged_impl_module: self.privileged_impl_module,
            output_tys: output_tys.to_vec(),
            output_effs: output_effs.to_vec(),
        });
    }

    /// Resolve a trait application's associated outputs without committing its runtime artifacts.
    ///
    /// Type inference and defaulting ask whether an application exists and what outputs it
    /// determines while types and effects are still provisional. The materializing solver remains
    /// the single source of trait-selection semantics, but everything it derives for this query is
    /// transactional: method bodies, associated-const getters, dictionaries, and their cache keys
    /// are rolled back after the outputs have been copied. Final HIR elaboration calls
    /// [`solve_impl`](Self::solve_impl) and is therefore the only phase that retains those runtime
    /// artifacts.
    ///
    /// A scratch HIR arena is deliberate. Some trait derivers synthesize a body while determining
    /// whether they apply; a query must not leave those unused nodes in the expression being
    /// inferred either.
    ///
    /// Fully concrete, unconstrained queries can reuse their associated outputs within this
    /// solver. Constrained output applications can select different answers and are never cached.
    fn solve_application_outputs_without_materializing(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        fn_span: Location,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        let unconstrained_output_query =
            requested_output_tys.is_none() && requested_output_effs.is_none();
        // Outputs found by structure come from erased candidates: they must stay out of the cache.
        if unconstrained_output_query
            && !self.selecting_by_structure
            && let Some(cached) = self.cached_unmaterialized_outputs(trait_id, input_tys)
        {
            return Ok((cached.output_tys.clone(), cached.output_effs.clone()));
        }

        let snapshot = self.snapshot_derived_impl_state();
        let mut scratch_arena = NodeArena::default();
        let result = self
            .solve_impl_application(
                trait_id,
                input_tys,
                requested_output_tys,
                requested_output_effs,
                fn_span,
                &mut scratch_arena,
            )
            .map(|impl_id| {
                let imp = self.get_impl_data_by_id(impl_id);
                (imp.output_tys.clone(), imp.output_effs.clone())
            });
        self.rollback_derived_impl_state(snapshot);
        if unconstrained_output_query
            && !self.selecting_by_structure
            && let Ok((output_tys, output_effs)) = &result
        {
            self.cache_unmaterialized_outputs(trait_id, input_tys, output_tys, output_effs);
        }
        result
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

    /// Resolve the zero-argument runtime getter for an associated constant.
    pub fn solve_associated_const_getter(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        associated_const_index: TraitAssociatedConstIndex,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<FunctionId, InternalCompilationError> {
        assert!(
            associated_const_index.as_index() < self.trait_def(trait_id).associated_const_count(),
            "associated const index {} out of bounds for trait {}",
            associated_const_index,
            self.trait_def(trait_id).name
        );
        let impl_id = self.solve_impl(trait_id, input_tys, fn_span, arena)?;
        let getter = self
            .get_impl_data_by_id(impl_id)
            .associated_const_getter(associated_const_index)
            .unwrap_or_else(|| {
                panic!(
                    "implementation of trait {} is missing associated const getter #{}",
                    self.trait_def(trait_id).name,
                    associated_const_index
                )
            });
        Ok(FunctionId::new(impl_id.module, getter))
    }

    /// Get a specific trait implementation data by its id.
    pub fn get_impl_data_by_id(&self, impl_id: TraitImplId) -> &TraitImpl {
        if impl_id.module == self.current_type_items.module.id
            && let Some(imp) = self.impls.data.get(impl_id.impl_id.as_index())
        {
            return imp;
        }
        &self
            .others
            .get(impl_id.module)
            .unwrap_or_else(|| panic!("module #{} not found", impl_id.module))
            .module()
            .unwrap()
            .impls
            .data[impl_id.impl_id.as_index()]
    }

    /// Get a specific function from a given module.
    /// If necessary, the value dependencies are updated.
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
        let function_id = module.get_local_function_id(function_name).ok_or_else(|| {
            internal_compilation_error!(Internal {
                error: format!("Function {function_name} not found in module {module_path}"),
                span: use_site
            })
        })?;
        Ok(self.function_id(module_id, function_id))
    }

    /// Look up an existing named function without rebuilding a function-only index.
    pub(crate) fn current_function(&self, name: Ustr) -> Option<LocalFunctionId> {
        let (_, def) = self.current_def_table.get_by_name(&name)?;
        if let Some(id) = def.kind.as_function() {
            return Some(*id);
        }
        // Helper lookup historically selected the last named function even if
        // a later non-function shadowed it. Preserve that behavior only for an
        // indexed name; ordinary misses must not scan the definition table.
        self.current_def_table
            .iter()
            .filter_map(|(def, entry_name)| {
                (*entry_name == Some(name))
                    .then(|| def.kind.as_function().copied())
                    .flatten()
            })
            .last()
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
        //     return Ok(self.function_id(self.current_type_items.module.id, local_id));
        // }
        if let Some(local_id) = self.current_function(function_name) {
            return Ok(self.function_id(self.current_type_items.module.id, local_id));
        }
        self.get_function(use_site, module_path, function_name)
    }

    /// Get a specific subscript member from a given module.
    /// If necessary, the value dependencies are updated.
    pub fn get_subscript_member(
        &mut self,
        use_site: Location,
        module_path: &module::Path,
        subscript_name: Ustr,
        mut_member: bool,
    ) -> Result<FunctionId, InternalCompilationError> {
        let module_not_found_error = || {
            internal_compilation_error!(Internal {
                error: format!(
                    "Module {module_path} not found when looking for subscript {subscript_name}"
                ),
                span: use_site
            })
        };
        let (module_id, entry) = self
            .others
            .get_by_name(module_path)
            .ok_or_else(module_not_found_error)?;
        let module = entry.module().ok_or_else(module_not_found_error)?;
        let subscript = module.get_subscript(subscript_name).ok_or_else(|| {
            internal_compilation_error!(Internal {
                error: format!("Subscript {subscript_name} not found in module {module_path}"),
                span: use_site
            })
        })?;
        let member = if mut_member {
            subscript.mut_member.as_ref()
        } else {
            subscript.ref_member.as_ref()
        };
        let Some(member) = member else {
            let member_name = if mut_member { "mut" } else { "ref" };
            return Err(internal_compilation_error!(Internal {
                error: format!(
                    "Subscript {subscript_name} in module {module_path} has no {member_name} member"
                ),
                span: use_site
            }));
        };
        Ok(self.function_id(module_id, member.function))
    }

    fn function_id(&mut self, module_id: ModuleId, function_id: LocalFunctionId) -> FunctionId {
        if module_id != self.current_type_items.module.id {
            self.deps.insert(module_id);
        }
        FunctionId::new(module_id, function_id)
    }

    fn impl_id(&mut self, module_id: ModuleId, impl_id: LocalImplId) -> TraitImplId {
        if module_id != self.current_type_items.module.id {
            self.deps.insert(module_id);
        }
        TraitImplId::new(module_id, impl_id)
    }
}

impl TraitOutputQuery for TraitSolver<'_> {
    fn output_effect_polarities_query(&mut self, trait_id: TraitId) -> Vec<EffectPolarity> {
        self.output_effect_polarities(trait_id)
    }

    fn unify_non_trait_constraint_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        constraint: &PubTypeConstraint,
        assumptions: ConstraintAssumptions<'_>,
        arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        ty_inf.unify_pub_constraint(constraint, assumptions, |_| false, self, arena)
    }

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
            self,
        )
    }

    fn solve_outputs_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_effs: Option<&[EffType]>,
        fn_span: Location,
        _arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        self.solve_application_outputs_without_materializing(
            trait_id,
            input_tys,
            None,
            output_effs,
            fn_span,
        )
    }

    fn solve_outputs_by_structure_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        let selecting_by_structure = mem::replace(&mut self.selecting_by_structure, true);
        let result = self.solve_application_outputs_without_materializing(
            trait_id, input_tys, None, None, fn_span,
        );
        self.selecting_by_structure = selecting_by_structure;
        result.map(|(output_tys, _)| output_tys)
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
            true,
            fn_span,
            arena,
        )
    }
}

impl<'a> Drop for TraitSolver<'a> {
    fn drop(&mut self) {
        if !self.fn_collector.new_elements.is_empty() {
            log::warn!(
                "TraitSolver dropped without committing the created functions. Call .finish().commit() to store them in the module."
            );
        }
    }
}

impl TypePropertyEnv for TraitSolver<'_> {
    fn has_trivial_copy_impl(&self, ty: Type) -> bool {
        let key = trivial_copy_impl_key(self.std_trait_id(TRIVIAL_COPY_TRAIT_NAME), ty);
        self.has_canonical_trait_impl(&key)
    }

    fn type_def(&self, id: TypeDefId) -> &TypeDef {
        TraitSolver::type_def(self, id)
    }
}

#[cfg(test)]
mod tests {
    use std::{fmt, slice::from_ref};

    use super::*;
    use crate::{
        CompilerSession,
        ast::ImplAstIndex,
        eval::{EvalCtx, EvalResult, ValOrMut},
        hir::function::{ArgConvention, Callable, Function},
        module::{BlanketTraitImplSubKey, ELocalDecl, Path},
        std::{core_traits_names::VALUE_TRAIT_NAME, math::int_type, new_module_using_std},
        types::{
            effects::{PrimitiveEffect, effect},
            r#type::FnType,
        },
    };

    #[test]
    fn borrowed_function_lookup_preserves_named_function_selection() {
        use crate::module::{Def, DefKind};

        fn check(module: &mut Module, modules: &Modules) {
            // Reference the previous eager map, including its treatment of
            // duplicate names, non-functions and anonymous entries.
            let expected: FxHashMap<_, _> = module
                .def_table
                .iter()
                .filter_map(|(def, name)| Some(((*name)?, *def.kind.as_function()?)))
                .collect();
            let solver = trait_solver_from_module!(module, modules);
            let mut probe = TraitSolverProbe::from_solver(&solver);
            for name in [ustr::ustr("f"), ustr::ustr("other"), ustr::ustr("missing")] {
                assert_eq!(solver.current_function(name), expected.get(&name).copied());
                assert_eq!(
                    probe.with_solver(|nested| nested.current_function(name)),
                    expected.get(&name).copied()
                );
            }
            drop(probe);
            // Finishing releases the definition-table borrow before commit mutates it.
            let mut pending = FxHashMap::default();
            assert!(
                solver
                    .finish()
                    .commit(&mut module.functions, &mut module.def_table, &mut pending)
                    .is_empty()
            );
        }

        let modules = Modules::default();
        let mut module = Module::new(ModuleId::new(0), Path::single_str("$function_lookup"));
        let name = ustr::ustr("f");
        let function = |id| {
            Def::new(
                DefKind::Function(LocalFunctionId::new(id)),
                Visibility::Module,
            )
        };
        check(&mut module, &modules);
        module.def_table.insert(name, function(0));
        module.def_table.insert_anonymous(function(1));
        module.def_table.insert(
            ustr::ustr("other"),
            Def::public(DefKind::BareNativeTypeAlias),
        );
        check(&mut module, &modules);
        module.def_table.insert(name, function(2));
        check(&mut module, &modules);
        module
            .def_table
            .insert(name, Def::public(DefKind::BareNativeTypeAlias));
        check(&mut module, &modules);
    }

    fn impl_storage_fixture() -> (Module, ConcreteTraitImplKey) {
        // No semantic query uses these entries: they exercise storage and visibility.
        let module_id = ModuleId::new(0);
        let mut module = Module::new(module_id, Path::single_str("$impl_storage"));
        let trait_id = TraitId::new(module_id, LocalTraitId::new(0));
        let key = ConcreteTraitImplKey::new(trait_id, vec![Type::unit()]);
        let imp = TraitImpl::new(
            trait_id,
            vec![Type::unit()],
            vec![],
            vec![],
            TraitDictionary::new(&[], &[]),
            Type::unit(),
            true,
            None,
        );
        module.impls.add_concrete_struct(key.clone(), imp);
        (module, key)
    }

    #[test]
    fn impl_probes_share_tables_and_isolate_nested_writes() {
        let (mut module, key) = impl_storage_fixture();
        let modules = Modules::default();
        {
            let mut borrowed = TraitSolverProbe::from_module(&module, &modules);
            borrowed.with_solver(|scratch| {
                assert!(Rc::ptr_eq(&scratch.impls.data, &module.impls.data));
                assert!(Rc::ptr_eq(
                    &scratch.impls.concrete_key_to_id,
                    &module.impls.concrete_key_to_id
                ));
            });
        }
        let solver = trait_solver_from_module!(module, &modules);
        let mut probe = TraitSolverProbe::from_solver(&solver);
        assert!(Rc::ptr_eq(&probe.impls.data, &solver.impls.data));
        assert!(Rc::ptr_eq(
            &probe.impls.concrete_key_to_id,
            &solver.impls.concrete_key_to_id
        ));
        probe.with_solver(|inner| {
            // A no-op rollback must not detach the dictionaries.
            let snapshot = inner.snapshot_derived_impl_state();
            inner.rollback_derived_impl_state(snapshot);
            assert!(Rc::ptr_eq(&inner.impls.data, &solver.impls.data));
            let mut nested = TraitSolverProbe::from_solver(inner);
            nested.with_solver(|nested| {
                let mut private = nested.impls.data[0].clone();
                private.public = false;
                let private_key = ConcreteTraitImplKey::new(key.trait_id, vec![Type::never()]);
                let id = nested
                    .impls
                    .add_concrete_struct(private_key.clone(), private);
                Rc::make_mut(&mut nested.impls.data)[0].output_tys = vec![Type::never()];
                assert_eq!(inner.impls.data[0].output_tys, vec![Type::unit()]);
                assert!(!inner.impls.concrete_key_to_id.contains_key(&private_key));
                let filtered = TraitSolverProbe::from_solver(nested);
                assert!(Rc::ptr_eq(&filtered.impls.data, &nested.impls.data));
                assert!(!Rc::ptr_eq(
                    &filtered.impls.concrete_key_to_id,
                    &nested.impls.concrete_key_to_id
                ));
                assert!(filtered.impls.concrete_key_to_id.contains_key(&key));
                assert!(!filtered.impls.concrete_key_to_id.contains_key(&private_key));
                assert_eq!(nested.impls.concrete_key_to_id[&private_key], id);
                assert!(!filtered.impls.data[id.as_index()].public);
            });
            assert!(Rc::ptr_eq(&inner.impls.data, &solver.impls.data));
        });
        assert_eq!(solver.impls.data.len(), 1);
        assert_eq!(solver.impls.data[0].output_tys, vec![Type::unit()]);
    }

    #[test]
    fn impl_snapshot_rollback_restores_all_indexes_with_live_probes() {
        let (mut module, key) = impl_storage_fixture();
        let modules = Modules::default();
        let mut solver = trait_solver_from_module!(module, &modules);
        let outer = solver.snapshot_derived_impl_state();
        let observer = TraitSolverProbe::from_solver(&solver);
        let imp = solver.impls.data[0].clone();
        let private_key = ConcreteTraitImplKey::new(key.trait_id, vec![Type::never()]);
        let id = solver
            .impls
            .add_concrete_struct(private_key.clone(), imp.clone());
        let blanket_key = module::BlanketTraitImplKey::new(
            key.trait_id,
            BlanketTraitImplSubKey {
                input_tys: vec![Type::variable_id(0)],
                ty_var_count: 1,
                eff_var_count: 0,
                constraints: vec![],
            },
        );
        solver.impls.add_blanket_struct(blanket_key, imp.clone());
        Rc::make_mut(&mut solver.impls.generated_value_key_to_id).insert(vec![Type::never()], id);
        Rc::make_mut(&mut solver.impls.application_key_to_id).insert(private_key.clone(), id);
        solver
            .fn_collector
            .reserve_with_visibility(ustr::ustr("outer"), Visibility::Module);
        let inner = solver.snapshot_derived_impl_state();
        solver.impls.add_anonymous_dictionary_struct(imp);
        solver
            .fn_collector
            .reserve_with_visibility(ustr::ustr("inner"), Visibility::Module);
        let retained = TraitSolverProbe::from_solver(&solver);
        solver.rollback_derived_impl_state(inner);
        assert_eq!(solver.impls.data.len(), 3);
        assert_eq!(solver.fn_collector.new_elements.len(), 1);
        assert_eq!(solver.impls.application_key_to_id[&private_key], id);
        assert_eq!(retained.impls.data.len(), 4);
        solver.rollback_derived_impl_state(outer);
        assert!(Rc::ptr_eq(
            &solver.impls.concrete_key_to_id,
            &observer.impls.concrete_key_to_id
        ));
        assert!(Rc::ptr_eq(
            &solver.impls.blanket_key_to_id,
            &observer.impls.blanket_key_to_id
        ));
        assert!(Rc::ptr_eq(
            &solver.impls.generated_value_key_to_id,
            &observer.impls.generated_value_key_to_id
        ));
        assert!(Rc::ptr_eq(
            &solver.impls.application_key_to_id,
            &observer.impls.application_key_to_id
        ));
        assert_eq!(solver.impls.data.len(), 1);
        assert!(solver.fn_collector.new_elements.is_empty());
        assert_eq!(observer.impls.data.len(), 1);
        assert_eq!(retained.impls.data.len(), 4);
        assert_eq!(retained.impls.application_key_to_id[&private_key], id);
        // The next insertion reuses the rolled-back local ID.
        let imp = solver.impls.data[0].clone();
        assert_eq!(solver.impls.add_concrete_struct(private_key, imp), id);
    }

    #[test]
    fn improvement_head_filter_never_discards_a_successful_same_type_match() {
        use crate::{
            module::LocalTypeDefId,
            std::{array_type::array_type, logic::bool_type},
            types::r#type::{
                FnArgType, SubscriptMemberType, SubscriptResultConvention, store_types,
            },
        };
        let span = Location::new_synthesized();
        let var = Type::variable_id;
        let named = |index, parameter| {
            Type::named(
                TypeDefId::new(ModuleId::new(u32::MAX - 1), LocalTypeDefId::new(index)),
                vec![parameter],
            )
        };
        let callback = |args: Vec<Type>, ret, effects| {
            Type::function_type(FnType::new_by_val(args, ret, effects))
        };
        let recursive = store_types(&[TypeKind::Variant(vec![
            (ustr::ustr("End"), Type::unit()),
            (ustr::ustr("Next"), Type::new_local(0)),
        ])])[0];
        let subscript = Type::subscript_type(SubscriptType {
            args: vec![FnArgType::new_by_val(var(0))],
            ret: var(1),
            ref_member: Some(SubscriptMemberType::new(
                EffType::empty(),
                SubscriptResultConvention::AddressorPlace,
            )),
            mut_member: None,
        });
        let types = vec![
            var(0),
            var(1),
            Type::never(),
            int_type(),
            bool_type(),
            array_type(int_type()),
            array_type(var(0)),
            Type::unit(),
            Type::tuple([var(0)]),
            Type::tuple([int_type()]),
            Type::tuple([int_type(), bool_type()]),
            Type::record(vec![(ustr::ustr("x"), var(0))]),
            Type::variant(vec![(ustr::ustr("Some"), var(0))]),
            recursive,
            callback(vec![], Type::never(), EffType::empty()),
            callback(vec![], int_type(), effect(PrimitiveEffect::Read)),
            callback(vec![var(0)], var(1), EffType::empty()),
            callback(vec![int_type(), int_type()], int_type(), EffType::empty()),
            Type::function_type(FnType::new_mut_resolved(
                [(int_type(), true)],
                int_type(),
                EffType::empty(),
            )),
            named(0, int_type()),
            named(0, var(0)),
            named(1, int_type()),
            subscript,
        ];
        let mut pruned = 0;
        for &candidate in &types {
            for &input in &types {
                let keep = input_head_may_match(candidate, input);
                pruned += usize::from(!keep);
                let mut inference = UnifiedTypeInference::new_with_ty_vars(2);
                let accepted = inference
                    .unify_same_type_with_sub_effects(candidate, span, input, span)
                    .is_ok();
                assert!(
                    !accepted || keep,
                    "discarded a compatible pair: {candidate:?}, {input:?}"
                );
            }
        }
        assert!(pruned > types.len());
        // Never is a subtype of int, but cannot match an int impl head by equality.
        assert!(!input_head_may_match(Type::never(), int_type()));
        // Candidate variables have their own namespace; their numeric IDs must
        // not be looked up in the application's inference table.
        assert!(input_head_may_match(var(0), int_type()));
        assert!(input_head_may_match(int_type(), var(0)));
        // Matching heads are only permission to probe: nested incompatibilities
        // and independently quantified effects still need the real comparator.
        assert!(input_head_may_match(
            named(0, int_type()),
            named(0, bool_type())
        ));
    }

    #[test]
    fn pending_impls_block_negative_answers_only() {
        use crate::{
            module::{PendingImpl, PendingImpls},
            std::{array_type::array_type, logic::bool_type},
        };
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let modules = session.raw_modules();
        let module_id = modules.next_id();
        let mut module = new_module_using_std(module_id, Path::single_str("$pending_test"));
        let default_trait = trait_solver_from_module!(module, modules).std_trait_id("Default");
        let pair = |first| Type::tuple([first, int_type()]);
        let mut arena = NodeArena::default();
        let mut solver = trait_solver_from_module!(module, modules);
        assert!(
            solver
                .solve_outputs(default_trait, &[pair(int_type())], span, &mut arena)
                .is_ok()
        );
        drop(solver);

        let set_pending = |module: &mut Module, input_tys| {
            let pending = Rc::new(PendingImpls::new(vec![PendingImpl {
                index: ImplAstIndex::new(7),
                trait_id: default_trait,
                input_tys,
            }]));
            module.impls.pending = pending.clone();
            pending
        };
        let pending = set_pending(&mut module, Some(vec![pair(Type::variable_id(0))]));
        let mut solver = trait_solver_from_module!(module, modules);
        // A visible impl proves this answer whatever is pending.
        assert!(
            solver
                .solve_outputs(default_trait, &[array_type(int_type())], span, &mut arena)
                .is_ok()
        );
        assert!(pending.blockers().is_empty());
        // The pending impl may provide this application, so it is not derived.
        assert!(
            solver
                .solve_outputs(default_trait, &[pair(int_type())], span, &mut arena)
                .is_err()
        );
        assert_eq!(pending.blockers(), vec![ImplAstIndex::new(7)]);
        drop(solver);

        // Probes share the pending impls of the module they read.
        let pending = set_pending(&mut module, Some(vec![pair(bool_type())]));
        let mut probe = TraitSolverProbe::from_module(&module, modules);
        let mut arena = NodeArena::default();
        assert!(probe.with_solver(|solver| {
            solver
                .solve_outputs(default_trait, &[pair(bool_type())], span, &mut arena)
                .is_err()
        }));
        assert_eq!(pending.blockers(), vec![ImplAstIndex::new(7)]);
        drop(probe);

        // An absent concrete impl that the pending impl may fill is blocked.
        let pending = set_pending(&mut module, Some(vec![pair(bool_type())]));
        let solver = trait_solver_from_module!(module, modules);
        assert!(!solver.has_concrete_impl(&ConcreteTraitImplKey::new(
            default_trait,
            vec![pair(bool_type())]
        )));
        assert_eq!(pending.blockers(), vec![ImplAstIndex::new(7)]);
        drop(solver);

        // A headerless pending impl is another candidate for improvement: the single visible
        // candidate, `impl<A> Slice for <Self = [A] |-> Output = [A]>`, no longer determines the
        // output.
        let slice_trait = trait_solver_from_module!(module, modules).std_trait_id("Slice");
        let improves = |module: &mut Module| {
            let mut solver = trait_solver_from_module!(module, modules);
            let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(0);
            let element = Type::variable(ty_inf.fresh_type_var());
            let output = Type::variable(ty_inf.fresh_type_var());
            solver
                .try_improve_trait_application(
                    &mut ty_inf,
                    slice_trait,
                    &[array_type(element)],
                    Some(&[output]),
                    Some(&[]),
                    ConstraintAssumptions::all(&[]),
                    span,
                    &mut NodeArena::default(),
                )
                .unwrap();
            drop(solver);
            ty_inf.substitute_in_type(output) == array_type(ty_inf.substitute_in_type(element))
        };
        module.impls.pending = Rc::default();
        assert!(improves(&mut module));
        let pending = Rc::new(PendingImpls::new(vec![PendingImpl {
            index: ImplAstIndex::new(7),
            trait_id: slice_trait,
            input_tys: None,
        }]));
        module.impls.pending = pending.clone();
        assert!(!improves(&mut module));
        assert_eq!(pending.blockers(), vec![ImplAstIndex::new(7)]);
    }

    /// Type-solver fixture with an unresolved effect, not an executable host entry.
    #[derive(Clone)]
    struct UnexecutedEffectMethod;

    impl Callable for UnexecutedEffectMethod {
        fn call(&self, _: Vec<ValOrMut>, _: &mut EvalCtx) -> EvalResult {
            unreachable!("the effect-cache test only queries method types")
        }
        fn runtime_argument_passing(&self) -> Option<&[ArgConvention]> {
            Some(&[ArgConvention::Let])
        }
        fn format_ind(
            &self,
            f: &mut fmt::Formatter,
            _: &[ELocalDecl],
            _: &ModuleEnv,
            _: usize,
            _: usize,
        ) -> fmt::Result {
            f.write_str("UnexecutedEffectMethod")
        }
    }

    #[test]
    fn open_generated_value_dictionaries_ignore_caller_local_variable_numbers() {
        let session = CompilerSession::new();
        let modules = session.raw_modules();
        let module_id = modules.next_id();
        let mut module = new_module_using_std(module_id, Path::single_str("$open_dictionary_test"));
        let current_def_table = &module.def_table;
        let current_type_items = CurrentTypeItems::new(
            module::ModuleIdentity {
                id: module_id,
                path: &module.path,
            },
            &module.type_aliases,
            module.type_defs.as_slice(),
            module.traits.as_slice(),
            &module.projection_subscripts,
        );
        let value_trait_id = modules
            .get(STD_MODULE_ID)
            .unwrap()
            .module()
            .unwrap()
            .get_trait_id_str(VALUE_TRAIT_NAME)
            .unwrap();
        let method_count = modules
            .get(STD_MODULE_ID)
            .unwrap()
            .module()
            .unwrap()
            .trait_def(value_trait_id)
            .methods
            .len();
        let methods = (0..method_count)
            .map(LocalFunctionId::from_index)
            .collect::<Vec<_>>();
        let mut deps = FxHashSet::default();
        let mut solver = TraitSolver::new(
            current_type_items,
            &mut module.impls,
            current_def_table,
            &mut deps,
            CurrentProjectionSubscriptTypes::empty(),
            PendingFunctionCollector::new(method_count),
            modules,
        );
        let open_type = |variable| {
            Type::tuple([Type::function_type(FnType::new_by_val(
                [int_type()],
                Type::variable_id(variable),
                EffType::empty(),
            ))])
        };
        let first = solver
            .materialize_generated_value_impl_from_methods(
                value_trait_id,
                &[open_type(3)],
                Location::new_synthesized(),
                methods.clone(),
            )
            .unwrap()
            .0;
        let second = solver
            .materialize_generated_value_impl_from_methods(
                value_trait_id,
                &[open_type(19)],
                Location::new_synthesized(),
                methods,
            )
            .unwrap()
            .0;

        assert_eq!(
            first, second,
            "alpha-equivalent callers must reuse one module-owned dictionary definition"
        );
    }

    #[test]
    fn unmaterialized_output_cache_does_not_reuse_constrained_effects() {
        let session = CompilerSession::new();
        let modules = session.raw_modules();
        let module_id = modules.next_id();
        let mut module = Module::new(module_id, Path::single_str("$trait_solver_test"));
        let trait_id = TraitId::new(
            module_id,
            module.add_trait(
                Trait::new_with_self_input_type(
                    "UnconstrainedEffect",
                    "Test trait with an application-selected associated effect.",
                    ["Output"],
                    [(
                        "run",
                        CallableDefinition::new_infer_quantifiers(
                            FnType::new_by_val(
                                [Type::variable_id(0)],
                                Type::variable_id(1),
                                EffType::single_variable_id(0),
                            ),
                            ["value"],
                            "Returns its value.",
                        ),
                    )],
                )
                .with_output_effects(["E"]),
            ),
        );
        module.add_blanket_impl_with_effects_no_locals(
            trait_id,
            BlanketTraitImplSubKey {
                input_tys: vec![int_type()],
                ty_var_count: 0,
                eff_var_count: 1,
                constraints: vec![],
            },
            [int_type()],
            [EffType::single_variable_id(0)],
            [],
            // This solver fixture has unresolved effects and is never executed.
            [Box::new(UnexecutedEffectMethod) as Function],
        );

        let current_def_table = &module.def_table;
        let function_count = module.functions.len();
        let current_type_items = CurrentTypeItems::new(
            module::ModuleIdentity {
                id: module_id,
                path: &module.path,
            },
            &module.type_aliases,
            module.type_defs.as_slice(),
            module.traits.as_slice(),
            &module.projection_subscripts,
        );
        let mut deps = FxHashSet::default();
        let mut solver = TraitSolver::new(
            current_type_items,
            &mut module.impls,
            current_def_table,
            &mut deps,
            CurrentProjectionSubscriptTypes::empty(),
            PendingFunctionCollector::new(function_count),
            modules,
        );
        let mut arena = NodeArena::default();
        let read = effect(PrimitiveEffect::Read);

        let (_, output_effs) = solver
            .solve_application_outputs(
                trait_id,
                &[int_type()],
                &[int_type()],
                from_ref(&read),
                Location::new_synthesized(),
                &mut arena,
            )
            .unwrap();
        // The implementation's own effect takes its least solution, which the request includes.
        assert_eq!(output_effs, vec![EffType::empty()]);

        let (_, output_effs) = solver
            .solve_outputs(
                trait_id,
                &[int_type()],
                Location::new_synthesized(),
                &mut arena,
            )
            .unwrap();
        assert_eq!(output_effs, vec![EffType::empty()]);
        let cached = solver
            .cached_unmaterialized_outputs(trait_id, &[int_type()])
            .expect("the unconstrained query must populate the output cache");
        assert_eq!(cached.output_effs, vec![EffType::empty()]);
    }
}
