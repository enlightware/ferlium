use std::borrow::Borrow;

use derive_new::new;
use ena::unify::InPlaceUnificationTable;
use smallvec::{SmallVec, smallvec};
use ustr::{Ustr, ustr};

use super::substitution::InstSubst;
use crate::{
    FxHashMap, FxHashSet,
    ast::{
        self, DExprArena, DExprId, Desugared, ExprKind, Pattern, PatternConstraintKind,
        PatternKind, PatternVar, PropertyAccess, RecordField, RecordFields, UnnamedArg, UstrSpan,
    },
    compiler::error::{
        DuplicatedFieldContext, InternalCompilationError, InvalidLoopControlKind,
        InvalidSubscriptDefinitionKind, InvalidSubscriptUseKind, InvalidYieldKind, LoopControlKind,
        SubscriptDefinitionSubject, UnsafeFeature, UnsupportedSubscriptFeatureKind,
        WhatIsNotAProductType, WhichProductTypeIsNot,
    },
    containers::{SVec2, b, continuous_hashmap_to_vec},
    format::FormatWith,
    hir::{
        self, CallArgument, FieldAccess as HirFieldAccess, LoopId, NodeArena, NodeId, NodeKind,
        Project as HirProject, StoreLocal, Variant as HirVariant,
        addressor_place_base_argument_index,
        function::{
            CallableDefinition, PendingArgPassing, PendingValueArgPassing, ResolvedArgPassing,
            ResolvedValueArgPassing, unresolved_arg_passing_for_args,
        },
        node_is_place_reference, node_is_stable_place_reference,
        node_is_stable_storage_place_reference, place_resolution_may_create_temp,
        value::LiteralValue,
    },
    internal_compilation_error,
    module::{
        DeferredLocalStorage, FunctionId, LocalAssignmentMode, LocalDecl, LocalDeclId, ModuleEnv,
        ModuleFunctionSpans, PendingFunctionBody, PendingLocalClone, PendingLocalDrop,
        PendingModuleFunction, PendingTakeLocalValueMode, ProjectionIndex, ProjectionKey,
        ResolvedLocalDrop, SubscriptId, SubscriptMember, SubscriptMemberKind, TraitId,
        TypeDefLookupResult, YieldProvenance, id::Id,
    },
    parser::location::Location,
    std::{
        STD_MODULE_ID,
        core_traits_names::{REPR_TRAIT_NAME, TRIVIAL_COPY_TRAIT_NAME, VALUE_TRAIT_NAME},
        math::int_type,
        value::{VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX, is_value_trait},
    },
    types::{
        effects::{
            EffType, Effect, EffectVar, EffectsInstSubst, PrimitiveEffect, effect, no_effects,
        },
        mutability::{MutType, MutVar, MutVarKey},
        r#trait::{Trait, TraitMethodIndex},
        trait_solver::{TraitSolver, TraitSolverProbe},
        r#type::{
            CallImplType, CallResultConvention, FnArgType, FnType, SubscriptMemberType,
            SubscriptResultConvention, SubscriptType, TyVarKey, Type, TypeInstSubst, TypeKind,
            TypeVar,
        },
        type_like::TypeLike,
        type_mapper::{BitmapInstantiationMapper, TypeMapper},
        type_scheme::{ProjectionRequirementKind, PubTypeConstraint, TypeScheme},
        typing_env::{LoopFrame, TypingEnv},
    },
};

fn value_trait_id(env: &TypingEnv<'_>) -> crate::module::TraitId {
    env.module_env.expect_std_trait_id(VALUE_TRAIT_NAME)
}

fn repr_trait_id(env: &TypingEnv<'_>) -> crate::module::TraitId {
    env.module_env.expect_std_trait_id(REPR_TRAIT_NAME)
}

fn split_inferred_trait_associated_const_path(path: &ast::Path) -> Option<(ast::Path, UstrSpan)> {
    let (associated_const, trait_segments) = path.segments.split_last()?;
    if trait_segments.is_empty() {
        return None;
    }
    Some((ast::Path::new(trait_segments.to_vec()), *associated_const))
}

use super::{
    constraints::{MutConstraint, TypeConstraint},
    effect_solver::EffectSolver,
    unify::UnifiedTypeInference,
};

/// Returns whether a trait method may only be called by compiler-generated HIR.
fn is_compiler_callable_only_method(
    trait_id: crate::module::TraitId,
    trait_def: &Trait,
    method_index: TraitMethodIndex,
) -> bool {
    is_value_trait(trait_id, trait_def)
        && matches!(
            method_index,
            VALUE_CLONE_METHOD_INDEX | VALUE_DROP_METHOD_INDEX
        )
}

fn compiler_only_trait_method_use_error(
    trait_id: crate::module::TraitId,
    trait_def: &Trait,
    method_index: TraitMethodIndex,
    span: Location,
) -> InternalCompilationError {
    internal_compilation_error!(CompilerOnlyTraitMethodUse {
        trait_ref: trait_id,
        method_name: trait_def.method(method_index).0,
        span,
    })
}

fn loop_control_error(
    control: LoopControlKind,
    kind: InvalidLoopControlKind,
    span: Location,
) -> InternalCompilationError {
    internal_compilation_error!(InvalidLoopControl {
        control,
        kind,
        span,
    })
}

/// The type inference status, containing the unification table and the constraints
#[derive(Default, Debug)]
pub struct TypeInference {
    pub(super) ty_unification_table: InPlaceUnificationTable<TyVarKey>,
    pub(super) ty_constraints: Vec<TypeConstraint>,
    pub(super) mut_unification_table: InPlaceUnificationTable<MutVarKey>,
    pub(super) mut_constraints: Vec<MutConstraint>,
    pub(super) ty_coverage_constraints: Vec<(Location, Type, Vec<LiteralValue>)>,
    pub(super) effects: EffectSolver,
    /// Memoised results of `TrivialCopy` solver probes keyed by the queried concrete type.
    trivial_copy_cache: FxHashMap<Type, bool>,
    projection_subscript_miss_cache: FxHashSet<ProjectionKey>,
    next_loop_id: LoopId,
    /// Suspension tally for the access-chain arguments currently driven around one static call.
    /// Addressor-place drivers nest freely; yielded drivers count only when their outermost
    /// accessor stays suspended around the call. Materialized sub-expressions do not count.
    call_arg_suspension: Option<CallArgSuspensionState>,
}

/// Running tally of driven arguments left suspended around one static call.
#[derive(Default, Debug, Clone, Copy)]
struct CallArgSuspensionState {
    /// Number of driven arguments whose outermost accessor is suspended around the call.
    suspended: usize,
    /// Whether any of those suspended arguments is a mutable consumer.
    saw_mut: bool,
}

struct PreparedPlace {
    prefix: Vec<NodeId>,
    place: NodeId,
}

struct PreparedCallArguments {
    arguments: Vec<CallArgument>,
    temp_stores: Vec<NodeId>,
}

struct StaticCallFromCheckedArgs {
    callee: CheckedStaticCallee,
    inst_fn_ty: FnType,
    result_convention: CallResultConvention,
    inst_data: hir::FnInstData,
    args_node_ids: Vec<NodeId>,
    abi_arg_tys: Vec<FnArgType>,
    visible_arg_passing: Option<Vec<ResolvedArgPassing>>,
    result_mut_ty: MutType,
}

#[derive(Clone)]
enum CheckedStaticCallee {
    Function {
        function: FunctionId,
        function_path: Option<ast::Path>,
        function_span: Location,
        argument_names: Vec<Ustr>,
    },
    TraitMethod {
        trait_id: TraitId,
        method_index: TraitMethodIndex,
        method_path: ast::Path,
        method_span: Location,
        arguments_unnamed: UnnamedArg,
        input_tys: Vec<Type>,
    },
}

struct BuiltStaticCall {
    node: NodeKind,
    ty: Type,
    mut_ty: MutType,
    effects: EffType,
}

#[derive(Clone)]
struct PreparedStaticCallTarget {
    callee: CheckedStaticCallee,
    inst_fn_ty: FnType,
    result_convention: CallResultConvention,
    inst_data: hir::FnInstData,
    abi_arg_tys: Vec<FnArgType>,
    visible_arg_passing: Option<Vec<ResolvedArgPassing>>,
    result_mut_ty: MutType,
    have_trait_constraint: Option<PubTypeConstraint>,
}

#[derive(Clone)]
struct DrivenAccessChainArg {
    index: usize,
    access_chain: AccessChain,
    mode: SubscriptMemberKind,
}

#[derive(Clone, Copy)]
struct PreparedDrivenArg {
    index: usize,
    node: NodeId,
    ty: Type,
    mode: SubscriptMemberKind,
}

#[derive(Clone, Copy)]
struct NamedSubscriptReceiverOverride {
    node: NodeId,
    ty: Type,
    mut_ty: MutType,
}

#[derive(Clone, Debug)]
enum AccessChainStep {
    Field {
        name: UstrSpan,
        base_span: Location,
        expr_span: Location,
    },
    Index {
        index: DExprId,
        array_span: Location,
        expr_span: Location,
    },
    NamedSubscript {
        data: ast::NamedSubscriptData<Desugared>,
    },
    Project {
        index: (usize, Location),
        base_span: Location,
        expr_span: Location,
    },
}

#[derive(Clone, Debug)]
struct AccessChain {
    root: DExprId,
    steps: Vec<AccessChainStep>,
}

struct AccessChainPlan {
    chain: AccessChain,
    contains_named_subscript: bool,
}

type WithYieldedBodyBuilder<'a> = Box<
    dyn FnOnce(
            &mut TypeInference,
            &mut TypingEnv,
            NodeId,
            Type,
        ) -> Result<(NodeId, Type), InternalCompilationError>
        + 'a,
>;

/// Inferred accessor call data for a named subscript projection.
struct NamedSubscriptCall {
    node: NodeId,
    ty: Type,
    effects: EffType,
    provenance: YieldProvenance,
}

/// Prepared named subscript accessor, or the pre-yield divergence that prevents one.
enum PreparedNamedSubscriptAccessor {
    /// The accessor call was emitted and can be driven by `WithYielded`.
    Ready(NamedSubscriptCall),
    /// Accessor argument evaluation diverges before any yielded place can exist.
    DivergedBeforeYield(NodeId),
}

impl TypeInference {
    pub fn new_empty() -> Self {
        Self::default()
    }

    // TODO: improve error reporting by storing the span of the expression triggering the fresh variable creation
    pub fn fresh_type_var(&mut self) -> TypeVar {
        self.ty_unification_table.new_key(None)
    }

    pub fn fresh_type_var_ty(&mut self) -> Type {
        Type::variable(self.fresh_type_var())
    }

    pub fn fresh_type_var_tys(&mut self, count: usize) -> Vec<Type> {
        (0..count).map(|_| self.fresh_type_var_ty()).collect()
    }

    fn fresh_loop_id(&mut self) -> LoopId {
        let label = self.next_loop_id;
        self.next_loop_id = LoopId::from_index(label.as_index() + 1);
        label
    }

    fn resolve_loop_frame(
        loop_frames: &[LoopFrame],
        source_label: Option<UstrSpan>,
        span: Location,
        control: LoopControlKind,
    ) -> Result<usize, InternalCompilationError> {
        match source_label {
            Some(label) => loop_frames
                .iter()
                .rposition(|frame| {
                    frame
                        .source_label
                        .is_some_and(|frame_label| frame_label.0 == label.0)
                })
                .ok_or_else(|| {
                    loop_control_error(
                        control,
                        InvalidLoopControlKind::UnknownLabel { label: label.0 },
                        label.1,
                    )
                }),
            None => loop_frames.len().checked_sub(1).ok_or_else(|| {
                loop_control_error(control, InvalidLoopControlKind::OutsideLoop, span)
            }),
        }
    }

    /// Add the instantiated trait and parent constraints implied by a trait expression.
    fn add_instantiated_trait_assumptions(
        &mut self,
        env: &TypingEnv<'_>,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
        span: Location,
    ) {
        let trait_def = env.module_env.trait_def(trait_id);
        let inst_subst = trait_def.param_subst_for(input_tys, output_tys, output_effs);
        let mut mapper = BitmapInstantiationMapper::new(&inst_subst);
        for constraint in trait_def
            .parent_constraints
            .iter()
            .chain(trait_def.constraints.iter())
        {
            let mut constraint = constraint.map(&mut mapper);
            constraint.instantiate_location(span);
            let parent = constraint.as_have_trait().map(
                |(trait_id, input_tys, output_tys, output_effs, _)| {
                    (
                        *trait_id,
                        input_tys.to_vec(),
                        output_tys.to_vec(),
                        output_effs.to_vec(),
                    )
                },
            );
            self.add_pub_constraint(constraint);
            if let Some((
                parent_trait_id,
                parent_input_tys,
                parent_output_tys,
                parent_output_effs,
            )) = parent
            {
                self.add_instantiated_trait_assumptions(
                    env,
                    parent_trait_id,
                    &parent_input_tys,
                    &parent_output_tys,
                    &parent_output_effs,
                    span,
                );
            }
        }
    }

    /// Infer a `Trait::CONST` or `Trait::<T>::CONST` expression.
    fn infer_trait_associated_const(
        &mut self,
        env: &mut TypingEnv,
        trait_id: TraitId,
        associated_const_name: UstrSpan,
        explicit_input_tys: Option<&[crate::ast::TypeSpan<Desugared>]>,
        expr_span: Location,
    ) -> Result<(NodeKind, Type, MutType, EffType), InternalCompilationError> {
        let trait_def = env.module_env.trait_def(trait_id);
        let Some(associated_const_index) =
            trait_def.associated_const_index(associated_const_name.0)
        else {
            return Err(internal_compilation_error!(InvalidVariantConstructor {
                span: associated_const_name.1,
            }));
        };
        let input_tys = if let Some(input_tys) = explicit_input_tys {
            if input_tys.len() != trait_def.input_type_count() as usize {
                return Err(internal_compilation_error!(WrongNumberOfArguments {
                    expected: trait_def.input_type_count() as usize,
                    expected_span: associated_const_name.1,
                    got: input_tys.len(),
                    got_span: expr_span,
                }));
            }
            input_tys.iter().map(|(ty, _)| *ty).collect::<Vec<_>>()
        } else {
            self.fresh_type_var_tys(trait_def.input_type_count() as usize)
        };
        let output_tys = self.fresh_type_var_tys(trait_def.output_type_count() as usize);
        let output_effs = (0..trait_def.output_effect_count())
            .map(|_| self.fresh_effect_var_ty())
            .collect::<Vec<_>>();
        self.add_pub_constraint(PubTypeConstraint::new_have_trait(
            trait_id,
            input_tys.clone(),
            output_tys.clone(),
            output_effs.clone(),
            expr_span,
        ));
        self.add_instantiated_trait_assumptions(
            env,
            trait_id,
            &input_tys,
            &output_tys,
            &output_effs,
            expr_span,
        );
        let associated_const_tys = trait_def.instantiate_associated_const_tys_for_tys(
            &input_tys,
            &output_tys,
            &output_effs,
        );
        let ty = associated_const_tys[associated_const_index.as_index()];
        let node = NodeKind::GetTraitAssociatedConst(b(hir::GetTraitAssociatedConst {
            trait_id,
            associated_const_index,
            associated_const_name: associated_const_name.0,
            associated_const_span: associated_const_name.1,
            input_tys,
            output_tys,
            output_effs,
        }));
        Ok((node, ty, MutType::constant(), no_effects()))
    }

    pub fn fresh_mut_var(&mut self) -> MutVar {
        self.mut_unification_table.new_key(None)
    }

    pub fn fresh_mut_var_ty(&mut self) -> MutType {
        MutType::Variable(self.fresh_mut_var())
    }

    pub fn fresh_effect_var(&mut self) -> EffectVar {
        self.effects.fresh_var()
    }

    pub fn fresh_effect_var_ty(&mut self) -> EffType {
        self.effects.fresh_var_ty()
    }

    pub fn fresh_fn_arg(&mut self) -> FnArgType {
        FnArgType::new(self.fresh_type_var_ty(), self.fresh_mut_var_ty())
    }

    pub fn fresh_type_var_subst(&mut self, source: &[TypeVar]) -> TypeInstSubst {
        source
            .iter()
            .map(|&ty_var| (ty_var, self.fresh_type_var_ty()))
            .collect()
    }

    pub fn fresh_effect_var_subst(&mut self, source: &FxHashSet<EffectVar>) -> EffectsInstSubst {
        source
            .iter()
            .map(|&eff_var| (eff_var, self.fresh_effect_var_ty()))
            .collect()
    }

    pub fn add_pub_constraint(&mut self, pub_constraint: PubTypeConstraint) {
        self.ty_constraints
            .push(TypeConstraint::Pub(pub_constraint));
    }

    pub fn add_ty_coverage_constraint(
        &mut self,
        span: Location,
        ty: Type,
        values: Vec<LiteralValue>,
    ) {
        self.ty_coverage_constraints.push((span, ty, values));
    }

    fn instantiate_type_def(
        &mut self,
        type_def_lookup: TypeDefLookupResult,
        use_site: Location,
        module_env: &ModuleEnv<'_>,
    ) -> (crate::module::TypeDefId, Type, Type, Option<Ustr>) {
        let (type_def, tag) = type_def_lookup.lookup_payload();
        let type_def_data = module_env.type_def(type_def);
        let (payload_ty, _inst_data, subst) = type_def_data
            .payload_scheme(tag)
            .instantiate_with_fresh_vars(self, use_site, None, *module_env);
        let params: Vec<_> = type_def_data
            .shape
            .ty_quantifiers
            .iter()
            .map(|quantifier| quantifier.instantiate(&subst.0))
            .collect();
        let effect_params: Vec<_> = type_def_data
            .generic_effect_params
            .iter()
            .enumerate()
            .map(|(index, _)| EffType::single_variable(EffectVar::new(index as u32)))
            .map(|effect| effect.instantiate(&subst.1))
            .collect();
        let named_ty = Type::named_with_effects(type_def, params, effect_params);
        (type_def, payload_ty, named_ty, tag)
    }

    fn infer_abstract(
        &mut self,
        env: &mut TypingEnv,
        args: &[(Ustr, Location)],
        body: DExprId,
        expected_fn_ty: Option<FnType>,
        span: Location,
    ) -> Result<(NodeId, Type, MutType, EffType), InternalCompilationError> {
        use hir::Node as N;
        use hir::NodeKind as K;

        // 1. Collect free variables in the body.
        let mut free_vars = FxHashSet::default();
        let mut bound_vars = vec![FxHashSet::default()];
        for (arg, _) in args {
            bound_vars[0].insert(*arg);
        }
        collect_free_variables(body, env.ast_arena, &mut bound_vars, &mut free_vars);

        // 2. Identify captures from the current environment.
        let mut capture_node_ids = Vec::new();
        let mut capture_tys = Vec::new();
        let mut capture_args = Vec::new(); // inner Ids

        // Sort for deterministic order.
        let mut sorted_free_vars: Vec<_> = free_vars.into_iter().collect();
        sorted_free_vars.sort();

        let mut fn_all_locals = Vec::new();
        for var_name in sorted_free_vars {
            let found = env.get_variable_id(&var_name);
            if let Some(outer_id) = found {
                // It is a local variable in the current environment, capture it.
                let local = &env.all_locals[outer_id.as_index()];
                let capture_id = env.ir_arena.alloc(N::new(
                    K::LoadLocal(hir::LoadLocal { id: outer_id }),
                    local.ty,
                    no_effects(),
                    span,
                ));
                capture_node_ids.push(capture_id);
                capture_tys.push(local.ty);
                let mut inner_local = local.clone();
                inner_local.scope = span; // the local's scope is the whole lambda
                let inner_id = LocalDecl::push_with_next_slot(&mut fn_all_locals, inner_local);
                capture_args.push(inner_id);
            }
        }

        // 3. Determine explicit arguments types and return type.
        // Local ids are inner to the lambda.
        let (explicit_locals, ret_ty) = if let Some(fn_ty) = &expected_fn_ty {
            let explicit_locals = args
                .iter()
                .zip(&fn_ty.args)
                .map(|(name, arg_ty)| {
                    let local = LocalDecl::new(*name, arg_ty.mut_ty, arg_ty.ty, None, span);
                    LocalDecl::push_with_next_slot(&mut fn_all_locals, local)
                })
                .collect::<Vec<_>>();
            (explicit_locals, fn_ty.ret)
        } else {
            let explicit_locals = args
                .iter()
                .map(|name| {
                    let local = LocalDecl::new(
                        *name,
                        self.fresh_mut_var_ty(),
                        self.fresh_type_var_ty(),
                        None,
                        span,
                    );
                    LocalDecl::push_with_next_slot(&mut fn_all_locals, local)
                })
                .collect::<Vec<_>>();
            (explicit_locals, self.fresh_type_var_ty())
        };

        let args_ty: Vec<FnArgType> = explicit_locals
            .iter()
            .map(|id| fn_all_locals[id.as_index()].as_fn_arg_type())
            .collect();

        // 4. Build environment for typing the function's body.
        let runtime_arg_count = capture_args.len() + explicit_locals.len();
        let fn_cur_locals = capture_args.into_iter().chain(explicit_locals).collect();
        let mut fn_arena = NodeArena::default();
        let mut inner_env = TypingEnv::new(
            &mut fn_all_locals,
            fn_cur_locals,
            env.new_deps,
            env.module_env,
            Some((ret_ty, env.ast_arena[body].span)),
            CallResultConvention::Value,
            env.annotation_subst,
            vec![],
            env.fuel_checks_enabled,
            env.lambda_functions,
            env.base_local_function_index,
            env.ast_arena,
            &mut fn_arena,
        );
        inner_env.compilation_capabilities = env.compilation_capabilities;
        inner_env.subscript_member = env.subscript_member;

        // 5. Infer the body's type.
        let mut code_id = self.check_expr(
            &mut inner_env,
            body,
            ret_ty,
            MutType::constant(),
            env.ast_arena[body].span,
        )?;
        if inner_env.ir_arena[code_id].ty != Type::never() {
            code_id =
                self.materialize_owned_value(&mut inner_env, code_id, env.ast_arena[body].span);
        }

        let code = &inner_env.ir_arena[code_id];
        let effects = code.effects.clone();
        drop(inner_env);

        // 6. Store and return the function's type.
        let fn_ty = FnType::new(args_ty, ret_ty, effects);
        let fn_ty_wrapper = Type::function_type(fn_ty.clone());
        let arg_names: Vec<_> = args.iter().map(|(name, _)| *name).collect();
        let ty_scheme = TypeScheme::new_just_type(fn_ty);
        let body_span = env.ast_arena[body].span;
        let spans = ModuleFunctionSpans {
            name: Location::new_synthesized(),
            args: args.iter().map(|(_, span)| (*span, None)).collect(),
            args_span: Location::new(span.start(), body_span.start(), span.source_id()),
            ret_ty: None,
            span,
        };
        let function = PendingModuleFunction::from_body(
            CallableDefinition::new(ty_scheme, arg_names, None),
            PendingFunctionBody::new(fn_arena, code_id),
            runtime_arg_count,
            Some(spans),
            fn_all_locals,
        );
        let function_id = env.collect_lambda_module_function(function);
        let fn_node_id = env.ir_arena.alloc(N::new(
            K::GetFunction(b(hir::GetFunction {
                function: FunctionId::new(env.current_module_id(), function_id),
                function_path: ast::Path::single(ustr("<lambda>"), span),
                function_span: span,
                inst_data: hir::FnInstData::none(),
            })),
            fn_ty_wrapper,
            no_effects(),
            span,
        ));

        let capture_node_ids = self.materialize_owned_values(env, capture_node_ids, span);
        let node_id = if capture_node_ids.is_empty() {
            fn_node_id
        } else {
            let capture_env_ty = Type::tuple(capture_tys);
            let value_trait_id = value_trait_id(env);
            self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                value_trait_id,
                vec![capture_env_ty],
                vec![],
                vec![],
                span,
            ));
            let captures_value_dictionary = env.ir_arena.alloc(N::new(
                K::GetTraitDictionary(b(hir::GetTraitDictionary {
                    trait_id: value_trait_id,
                    input_tys: vec![capture_env_ty],
                    output_tys: vec![],
                    output_effs: vec![],
                })),
                env.module_env
                    .trait_def(value_trait_id)
                    .get_dictionary_type_for_tys(&[capture_env_ty], &[], &[]),
                no_effects(),
                span,
            ));
            let node = K::BuildClosure(b(hir::BuildClosure {
                function: fn_node_id,
                dictionary_captures: Vec::new(),
                captures: capture_node_ids,
                captures_value_dictionary: Some(captures_value_dictionary),
            }));
            env.ir_arena
                .alloc(N::new(node, fn_ty_wrapper, no_effects(), span))
        };

        Ok((node_id, fn_ty_wrapper, MutType::constant(), no_effects()))
    }

    pub fn infer_expr(
        &mut self,
        env: &mut TypingEnv,
        expr_id: DExprId,
    ) -> Result<(NodeId, MutType), InternalCompilationError> {
        use ExprKind::*;
        use hir::Node as N;
        use hir::NodeKind as K;
        let expr = &env.ast_arena[expr_id];
        let expr_span = expr.span;
        let sp = |id: DExprId| env.ast_arena[id].span;
        if Self::is_access_chain_expr(&expr.kind) {
            let plan = self.access_chain_plan_for_expr(env, expr_id);
            if plan.contains_named_subscript {
                return self.infer_access_chain_read(env, plan.chain, expr_span);
            }
        }
        let (node, ty, mut_ty, effects) = match &expr.kind {
            Literal(value, ty) => (
                K::Immediate(value.clone()),
                *ty,
                MutType::constant(),
                no_effects(),
            ),
            FormattedString(_s) => {
                unreachable!("this cannot happen as payload is never")
            }
            Identifier(path) => {
                // Retrieve the index and the type of the variable from the environment, if it exists
                if let [(name, _)] = &path.segments[..]
                    && let Some(id) = env.get_variable_id(name)
                {
                    let local = &env.all_locals[id.as_index()];
                    let node = K::LoadLocal(hir::LoadLocal { id });
                    (node, local.ty, local.mut_ty, no_effects())
                }
                // Retrieve the function from the environment, if it exists
                else if let Some((definition, function, _module_id, _runtime_arg_passing)) = env
                    .get_function(path)?
                    .map(|(definition, function, module_id, runtime_arg_passing)| {
                        (definition.clone(), function, module_id, runtime_arg_passing)
                    })
                {
                    let (fn_ty, inst_data, _subst) = definition
                        .ty_scheme
                        .instantiate_with_fresh_vars(self, expr_span, None, env.module_env);
                    let node = K::GetFunction(b(hir::GetFunction {
                        function,
                        function_path: path.clone(),
                        function_span: expr_span,
                        inst_data,
                    }));
                    (
                        node,
                        Type::function_type(fn_ty),
                        MutType::constant(),
                        no_effects(),
                    )
                }
                // Retrieve the subscript from the environment, if it exists.
                else if let Some((subscript, subscript_id, _module_id)) = env
                    .get_subscript(path)?
                    .map(|(subscript, subscript_id, module_id)| {
                        (subscript.clone(), subscript_id, module_id)
                    })
                {
                    Self::ensure_named_subscript_access_allowed(
                        env,
                        path.segments.last().expect("non-empty subscript path").0,
                        expr_span,
                    )?;
                    let owner = env.subscript_owner_module(subscript_id);
                    let (subscript_ty, inst_data, _subst) = subscript
                        .type_scheme(owner)
                        .expect("named subscript signature should be resolved before use")
                        .instantiate_with_fresh_vars(self, expr_span, None, env.module_env);
                    let node = K::GetSubscript(b(hir::GetSubscript {
                        subscript: subscript_id,
                        subscript_path: path.clone(),
                        inst_data,
                    }));
                    (
                        node,
                        Type::subscript_type(subscript_ty),
                        MutType::constant(),
                        no_effects(),
                    )
                }
                // Retrieve the trait method from the environment, if it exists
                else if let Some((_module_name, trait_descr)) =
                    env.module_env.get_trait_method(path)?
                {
                    let (trait_id, method_index, definition) = trait_descr;
                    let trait_def = env.module_env.trait_def(trait_id);
                    if is_compiler_callable_only_method(trait_id, trait_def, method_index) {
                        return Err(compiler_only_trait_method_use_error(
                            trait_id,
                            trait_def,
                            method_index,
                            expr_span,
                        ));
                    }
                    let trait_ty_var_count = trait_def.type_var_count();
                    let trait_input_type_count = trait_def.input_type_count();
                    let trait_eff_var_count = trait_def.output_effect_count();
                    let trait_constraints = trait_def.constraints.clone();
                    let (inst_fn_ty, inst_data, subst) =
                        definition.ty_scheme.instantiate_with_fresh_vars(
                            self,
                            expr_span,
                            Some((trait_ty_var_count, trait_eff_var_count)),
                            env.module_env,
                        );
                    assert!(
                        inst_data.dicts_req.is_empty(),
                        "Instantiation data for trait method is not supported yet."
                    );
                    let mut mapper = BitmapInstantiationMapper::new(&subst);
                    trait_constraints.iter().for_each(|constraint| {
                        let mut constraint = constraint.map(&mut mapper);
                        constraint.instantiate_location(expr_span);
                        self.add_pub_constraint(constraint);
                    });
                    let output_effs = (0..trait_eff_var_count)
                        .map(|i| subst.1.get(&EffectVar::new(i)).cloned().unwrap())
                        .collect::<Vec<_>>();
                    let mut trait_tys = continuous_hashmap_to_vec(subst.0).unwrap();
                    assert_eq!(trait_tys.len(), trait_ty_var_count as usize);
                    let output_tys = trait_tys.split_off(trait_input_type_count as usize);
                    let input_tys = trait_tys;
                    self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                        trait_id,
                        input_tys.clone(),
                        output_tys.clone(),
                        output_effs.clone(),
                        expr_span,
                    ));
                    let node = K::GetTraitMethod(b(hir::GetTraitMethod {
                        trait_id,
                        method_index,
                        method_path: path.clone(),
                        method_span: expr_span,
                        input_tys,
                        output_tys,
                        output_effs,
                        inst_data,
                    }));
                    (
                        node,
                        Type::function_type(inst_fn_ty),
                        MutType::constant(),
                        no_effects(),
                    )
                }
                // Retrieve the struct constructor, if it exists
                else if let Some(type_def) = env.get_type_def(path)? {
                    // Retrieve the payload type and the tag, if it is an enum.
                    let (type_def, payload_ty, ty, tag) =
                        self.instantiate_type_def(type_def, expr_span, &env.module_env);
                    if payload_ty != Type::unit() {
                        return Err(internal_compilation_error!(IsNotCorrectProductType {
                            which: WhichProductTypeIsNot::Unit,
                            type_def,
                            what: WhatIsNotAProductType::from_tag(tag),
                            instantiation_span: expr_span,
                        }));
                    }
                    let node = if let Some(tag) = tag {
                        let payload = env.ir_arena.alloc(N::new(
                            K::Immediate(LiteralValue::new_native(())),
                            Type::unit(),
                            no_effects(),
                            expr_span,
                        ));
                        K::Variant(HirVariant::new(tag, payload))
                    } else {
                        K::Immediate(LiteralValue::new_native(()))
                    };
                    (node, ty, MutType::constant(), EffType::empty())
                }
                // Retrieve an inferred trait associated const such as `Real::PI`.
                else if let Some((trait_name, associated_const_name)) =
                    split_inferred_trait_associated_const_path(path)
                    && let Some((_, trait_id)) = env.module_env.trait_id_with_module(&trait_name)?
                {
                    self.infer_trait_associated_const(
                        env,
                        trait_id,
                        associated_const_name,
                        None,
                        expr_span,
                    )?
                }
                // Otherwise, the name is neither a known variable or function, assume it to be a variant constructor
                else {
                    // Unresolved structural variants cannot be paths.
                    if path.segments.len() > 1 {
                        return Err(internal_compilation_error!(InvalidVariantConstructor {
                            span: expr_span,
                        }));
                    }
                    // Create a fresh type and add a constraint for that type to include this variant.
                    let variant_ty = self.fresh_type_var_ty();
                    let payload_ty = Type::unit();
                    let tag = path.segments[0].0;
                    self.ty_constraints.push(TypeConstraint::Pub(
                        PubTypeConstraint::new_type_has_variant(
                            variant_ty, expr_span, tag, payload_ty, expr_span,
                        ),
                    ));
                    let payload = env.ir_arena.alloc(N::new(
                        K::Immediate(LiteralValue::new_native(())),
                        Type::unit(),
                        no_effects(),
                        expr_span,
                    ));
                    let node = K::Variant(HirVariant::new(tag, payload));
                    (node, variant_ty, MutType::constant(), no_effects())
                }
            }
            TraitAssociatedConst(data) => {
                let Some((_, trait_id)) = env.module_env.trait_id_with_module(&data.trait_name)?
                else {
                    return Err(internal_compilation_error!(InvalidVariantConstructor {
                        span: expr_span,
                    }));
                };
                self.infer_trait_associated_const(
                    env,
                    trait_id,
                    data.name,
                    Some(&data.input_tys),
                    expr_span,
                )?
            }
            Let(data) => {
                let name = data.pattern.kind.name;
                let mut_val = data.pattern.kind.mut_val;
                let (node_id, initializer_mut_ty) = self.infer_expr(env, data.expr)?;
                let node_ty = env.ir_arena[node_id].ty;
                let initializer_is_scoped_place_value =
                    Self::node_is_scoped_place_value(env.ir_arena, node_id);
                let initializer_is_borrow = node_is_place_reference(env.ir_arena, node_id)
                    || initializer_is_scoped_place_value;
                let initializer_place_needs_temp = initializer_is_scoped_place_value
                    || place_resolution_may_create_temp(env.ir_arena, node_id);
                let initializer_depends_on_addressor_place =
                    place_evaluation_depends_on_addressor_place(env.ir_arena, node_id);
                let initializer_depends_on_projection_place =
                    place_evaluation_depends_on_projection_place(env.ir_arena, node_id);
                let initializer_is_known_immutable = matches!(
                    initializer_mut_ty,
                    MutType::Resolved(mut_ty) if !mut_ty.is_mutable()
                );
                let initializer_is_known_mutable = matches!(
                    initializer_mut_ty,
                    MutType::Resolved(mut_ty) if mut_ty.is_mutable()
                );
                let initializer_is_known_trivial_copy =
                    self.type_has_concrete_trivial_copy_impl(env, node_ty, expr_span);
                let defer_storage = node_ty != Type::never()
                    && initializer_is_borrow
                    && !initializer_place_needs_temp
                    && !mut_val.is_mutable()
                    && !initializer_is_known_immutable
                    && !initializer_is_known_mutable
                    && !initializer_depends_on_projection_place
                    && !initializer_is_known_trivial_copy;
                let needs_owned_snapshot = initializer_place_needs_temp
                    || mut_val.is_mutable()
                    || initializer_is_known_mutable
                    || initializer_is_known_trivial_copy
                    || initializer_depends_on_projection_place
                    || initializer_depends_on_addressor_place;
                let needs_clone = needs_owned_snapshot
                    && node_ty != Type::never()
                    && initializer_is_borrow
                    && !initializer_is_known_trivial_copy;
                if needs_clone && !node_ty.is_function() {
                    self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                        value_trait_id(env),
                        vec![node_ty],
                        vec![],
                        vec![],
                        expr_span,
                    ));
                }
                let owns_storage = node_ty != Type::never()
                    && !defer_storage
                    && (needs_clone || !initializer_is_borrow || initializer_is_known_trivial_copy);
                let mut local = LocalDecl::new(
                    name,
                    MutType::resolved(mut_val),
                    node_ty,
                    data.ty_ascription,
                    expr_span,
                );
                if owns_storage {
                    local.set_owned_storage(self.unresolved_or_skipped_drop_for_value(
                        env,
                        node_id,
                        node_ty,
                        mut_val.is_mutable(),
                        expr_span,
                    ));
                }
                if defer_storage {
                    local.set_deferred_storage(DeferredLocalStorage {
                        initializer: node_id,
                        initializer_mut_ty,
                        binding_mutable: mut_val.is_mutable(),
                    });
                }
                if needs_clone && !initializer_place_needs_temp {
                    local.clone = Some(PendingLocalClone::Unknown);
                }
                let value_id =
                    if node_ty != Type::never() && initializer_is_borrow && needs_owned_snapshot {
                        self.materialize_owned_value(env, node_id, expr_span)
                    } else {
                        node_id
                    };
                let node_effects = env.ir_arena[value_id].effects.clone();
                let id = env.push_local(local);
                let node = K::StoreLocal(StoreLocal {
                    value: value_id,
                    id,
                });
                let ty = if node_ty == Type::never() {
                    Type::never()
                } else {
                    Type::unit()
                };
                (node, ty, MutType::constant(), node_effects)
            }
            PatternConstraint(data) => {
                let (node_id, mut_type) = self.infer_expr(env, data.expr)?;
                match &data.constraint {
                    PatternConstraintKind::ExactTuple(element_count) => {
                        let expected_ty = if *element_count == 0 {
                            Type::unit()
                        } else {
                            Type::tuple(self.fresh_type_var_tys(*element_count))
                        };
                        self.add_same_type_with_sub_effects_constraint(
                            env.ir_arena[node_id].ty,
                            sp(data.expr),
                            expected_ty,
                            data.span,
                        );
                    }
                    PatternConstraintKind::NamedType(type_def) => {
                        let (_type_def, _payload_ty, named_ty, _tag) = self.instantiate_type_def(
                            TypeDefLookupResult::Struct(*type_def),
                            data.span,
                            &env.module_env,
                        );
                        self.add_same_type_with_sub_effects_constraint(
                            env.ir_arena[node_id].ty,
                            sp(data.expr),
                            named_ty,
                            data.span,
                        );
                    }
                }
                return Ok((node_id, mut_type));
            }
            Return(expr) => {
                let (outer_ty, outer_span) = match env.expected_return_ty {
                    Some(ret_ty) => ret_ty,
                    None => {
                        return Err(internal_compilation_error!(ReturnOutsideFunction {
                            span: expr_span,
                        }));
                    }
                };
                let node_id = if env.expected_return_convention.returns_place() {
                    self.infer_expr_as_place_return(env, *expr)?
                } else {
                    self.infer_expr_drop_mut(env, *expr)?
                };
                let ty = env.ir_arena[node_id].ty;
                self.add_same_type_with_sub_effects_constraint(ty, sp(*expr), outer_ty, outer_span);
                let effects = env.ir_arena[node_id].effects.clone();
                let return_value = if env.expected_return_convention.returns_place() {
                    if ty != Type::never() && !node_is_place_reference(env.ir_arena, node_id) {
                        return Err(internal_compilation_error!(InvalidSubscriptDefinition {
                            subject: env.subscript_member.map_or(
                                SubscriptDefinitionSubject::AddressorFunction(env.function_name),
                                |subscript_member| {
                                    SubscriptDefinitionSubject::SubscriptMember(
                                        subscript_member.name,
                                    )
                                },
                            ),
                            kind: InvalidSubscriptDefinitionKind::AddressorReturnMustBePlace,
                            span: sp(*expr),
                        }));
                    }
                    node_id
                } else {
                    // Return cleanup is represented by the lexical `Block.cleanup` scopes that the
                    // transfer exits. Function-entry locals are not wrapped in an extra cleanup
                    // scope here; the current calling convention passes non-trivial owned inputs by
                    // reference and only owns trivial-copy inputs at the function boundary.
                    self.prepare_value_for_exit(env, node_id, 0, expr_span)
                };
                let node = K::Return(return_value);
                (node, Type::never(), MutType::constant(), effects)
            }
            Yield(expr) => {
                if !env.loop_frames.is_empty() {
                    return Err(internal_compilation_error!(UnsupportedSubscriptFeature {
                        kind: UnsupportedSubscriptFeatureKind::YieldInsideLoop,
                        span: expr_span,
                    }));
                }
                let Some(yield_context) = &env.yield_context else {
                    return Err(internal_compilation_error!(InvalidYield {
                        kind: InvalidYieldKind::OutsideSubscriptMember,
                        span: expr_span,
                    }));
                };
                let expected_ty = yield_context.expected_ty;
                let expected_span = yield_context.expected_span;
                let requires_mutable_place = yield_context.requires_mutable_place;
                let (node_id, mut_ty) = self.infer_expr(env, *expr)?;
                let ty = env.ir_arena[node_id].ty;
                let operand_span = env.ir_arena[node_id].span;
                if ty != Type::never() && !node_is_place_reference(env.ir_arena, node_id) {
                    return Err(internal_compilation_error!(InvalidYield {
                        kind: InvalidYieldKind::NotAPlace,
                        span: operand_span,
                    }));
                }
                self.add_same_type_with_sub_effects_constraint(
                    ty,
                    operand_span,
                    expected_ty,
                    expected_span,
                );
                if requires_mutable_place {
                    self.add_mut_be_at_least_constraint(
                        mut_ty,
                        operand_span,
                        MutType::mutable(),
                        expr_span,
                    );
                }
                let effects = env.ir_arena[node_id].effects.clone();
                let node = env.ir_arena.alloc(hir::Node::new(
                    K::Yield(node_id),
                    Type::never(),
                    effects.clone(),
                    expr_span,
                ));
                env.yield_context
                    .as_mut()
                    .expect("yield context disappeared")
                    .yielded_nodes
                    .push(node);
                return Ok((node, MutType::constant()));
            }
            Abstract(data) => {
                let (node_id, _ty, mut_ty, _effects) =
                    self.infer_abstract(env, &data.args, data.body, None, expr_span)?;
                return Ok((node_id, mut_ty));
            }
            Apply(data) => {
                // Do we have a global function or variant?
                if let Identifier(path) = &env.ast_arena[data.func].kind {
                    let is_variable = match &path.segments[..] {
                        [(name, _)] => env.has_variable_name(*name),
                        _ => false,
                    };
                    if !is_variable {
                        let (node, ty, mut_ty, effects) = self.infer_static_apply(
                            env,
                            path,
                            sp(data.func),
                            &data.args,
                            expr_span,
                            data.unnamed_arg,
                        )?;
                        let node_id = env.ir_arena.alloc(N::new(node, ty, effects, expr_span));
                        return Ok((node_id, mut_ty));
                    }
                }
                // No, we emit code to evaluate function.
                // Evaluate left-to-right: function first, then arguments.
                let func_node_id = self.infer_expr_drop_mut(env, data.func)?;
                let func_effects = env.ir_arena[func_node_id].effects.clone();
                if env.ir_arena[func_node_id].ty == Type::never() {
                    let effects = self.make_dependent_effect([&func_effects]);
                    self.diverging_prefix_result(env, [func_node_id], effects)
                } else {
                    // Infer the type and mutability of the arguments and collect their code and constraints
                    let (mut args_nodes, args_tys, args_effects, args_diverge) =
                        self.infer_exprs_ret_arg_ty_until_never(env, &data.args)?;
                    if args_diverge {
                        let nodes =
                            self.value_evaluation_prefix_nodes(env.ir_arena, func_node_id)
                                .into_iter()
                                .chain(self.value_evaluation_prefix_nodes_for_many(
                                    env.ir_arena,
                                    args_nodes,
                                ))
                                .collect::<Vec<_>>();
                        let effects = self.make_dependent_effect([&func_effects, &args_effects]);
                        self.diverging_prefix_result(env, nodes, effects)
                    } else {
                        // Allocate a fresh variable for the return type and effects of the function
                        let ret_ty = self.fresh_type_var_ty();
                        let call_effects = self.fresh_effect_var_ty();
                        let abi_args = match &*env.ir_arena[func_node_id].ty.data() {
                            TypeKind::Function(fn_ty) => Some(fn_ty.args.clone()),
                            _ => None,
                        };
                        // Build the function type
                        let app_ty = FnType::new(args_tys.clone(), ret_ty, call_effects.clone());
                        let func_ty = Type::function_type(app_ty.clone());
                        self.add_sub_type_constraint(
                            env.ir_arena[func_node_id].ty,
                            sp(data.func),
                            func_ty,
                            expr_span,
                        );
                        // Unify effects
                        let combined_effects = self.make_dependent_effect([
                            &func_effects,
                            &args_effects,
                            &call_effects,
                        ]);
                        // Non-place function values and borrowed arguments are stored in
                        // explicit temps so the call ABI can pass stable places.
                        let temp_start_index = env.cur_locals.len();
                        let mut temp_stores = Vec::new();
                        let function = if node_is_place_reference(env.ir_arena, func_node_id) {
                            let prepared =
                                self.prepare_place_for_consumer(env, func_node_id, expr_span);
                            temp_stores.extend(prepared.prefix);
                            prepared.place
                        } else {
                            let (store, load) = self.store_owned_temp(
                                env,
                                func_node_id,
                                env.ir_arena[func_node_id].ty,
                                expr_span,
                                ustr("$function"),
                            );
                            temp_stores.push(store);
                            load
                        };
                        let abi_arg_tys = abi_args
                            .as_deref()
                            .filter(|abi_args| abi_args.len() == args_tys.len())
                            .unwrap_or(&args_tys);
                        let prepared_arguments = self.prepare_call_arguments(
                            env,
                            &mut args_nodes,
                            &args_tys,
                            abi_arg_tys,
                            expr_span,
                            None,
                        );
                        temp_stores.extend(prepared_arguments.temp_stores);
                        // Store and return the result
                        let call = K::Apply(b(hir::Application {
                            function,
                            arguments: prepared_arguments.arguments,
                            ty: CallImplType::value(app_ty),
                        }));
                        let call =
                            hir::Node::new(call, ret_ty, combined_effects.clone(), expr_span);
                        let node = self.wrap_call_with_temp_drops(
                            env,
                            temp_start_index,
                            temp_stores,
                            call,
                        );
                        (node, ret_ty, MutType::constant(), combined_effects)
                    }
                }
            }
            NamedSubscript(_) => {
                unreachable!("named subscript reads are handled by access-chain interception")
            }
            Block(exprs) => {
                assert!(!exprs.is_empty());
                let env_size = env.cur_locals.len();
                let local_decl_count = env.all_locals.len();
                let (mut nodes, types, effects, diverges) =
                    self.infer_exprs_drop_mut_until_never(env, exprs)?;
                // Statements before the block result are discarded and must run their drop glue.
                // This holds even when the block diverges: a `return` (or other never-typed tail)
                // abandons the preceding temporaries, whose `Value::drop` would otherwise be
                // skipped on the early-exit path (the diverging node is the last one and is left
                // untouched). Only the block *result* handling below is gated on `!diverges`.
                let last_index = nodes.len().saturating_sub(1);
                for node in nodes.iter_mut().take(last_index) {
                    let contains_yield = env.yield_context.as_ref().is_some_and(|ctx| {
                        node_contains_any_yield(env.ir_arena, *node, &ctx.yielded_nodes)
                    });
                    if contains_yield {
                        continue;
                    };
                    *node = self.discard_unused_value(env, *node, expr_span);
                }
                if !diverges {
                    let _taken_local = nodes.last_mut().and_then(|last| {
                        let (taken_node, taken_local) =
                            self.take_local_value_result(env, *last, local_decl_count, expr_span);
                        if taken_local.is_some() {
                            *last = taken_node;
                        } else {
                            *last = self.materialize_owned_value(env, *last, expr_span);
                        }
                        taken_local
                    });
                }
                // Adjust the lexical scope of the variables declared in the block to end at the end of the block.
                Self::extend_local_scopes_to_span_end(env, env_size, expr_span);
                let ty = types.last().copied().unwrap_or(Type::unit());
                let node = self.close_block_scope(env, env_size, nodes);
                (node, ty, MutType::constant(), effects)
            }
            Assign(data) => {
                if Self::is_access_chain_expr(&env.ast_arena[data.place].kind) {
                    let place = self.access_chain_for_expr(env, data.place);
                    return self.infer_access_chain_assign(
                        env,
                        place,
                        data.sign_span,
                        data.value,
                        expr_span,
                    );
                }
                if let Some(pp_data) = env.ast_arena[data.place].kind.as_property_path() {
                    let fn_path = property_to_fn_path(
                        &pp_data.path,
                        &pp_data.name,
                        PropertyAccess::Set,
                        expr_span,
                        env,
                    )?;
                    let (node, ty, mut_ty, effects) = self.infer_static_apply(
                        env,
                        &fn_path,
                        sp(data.place),
                        &[data.value],
                        expr_span,
                        UnnamedArg::All,
                    )?;
                    let node_id = env.ir_arena.alloc(N::new(node, ty, effects, expr_span));
                    return Ok((node_id, mut_ty));
                }
                let (place_id, place_mut) = self.infer_expr(env, data.place)?;
                let place_span = env.ir_arena[place_id].span;
                let place_effects = env.ir_arena[place_id].effects.clone();
                if env.ir_arena[place_id].ty == Type::never() {
                    let effects = self.make_dependent_effect([&place_effects]);
                    self.diverging_prefix_result(env, [place_id], effects)
                } else {
                    self.add_mut_be_at_least_constraint(
                        place_mut,
                        place_span,
                        MutType::mutable(),
                        data.sign_span,
                    );
                    let value_id = self.infer_expr_drop_mut(env, data.value)?;
                    let value_ty = env.ir_arena[value_id].ty;
                    let value_span = env.ir_arena[value_id].span;
                    let place_ty = env.ir_arena[place_id].ty;
                    self.add_sub_type_constraint(value_ty, value_span, place_ty, place_span);
                    let value_effects = env.ir_arena[value_id].effects.clone();
                    if value_ty == Type::never() {
                        let mut nodes = self.place_evaluation_prefix_nodes(env.ir_arena, place_id);
                        nodes.push(value_id);
                        let effects = self.make_dependent_effect([&place_effects, &value_effects]);
                        self.diverging_prefix_result(env, nodes, effects)
                    } else {
                        let temp_start_index = env.cur_locals.len();
                        let prepared_place =
                            self.prepare_place_for_consumer(env, place_id, expr_span);
                        let place_id = prepared_place.place;
                        let value_id = self.materialize_owned_value(env, value_id, expr_span);
                        let initializes_storage =
                            assignment_initializes_storage(env.ir_arena, place_id, env);
                        let drop = if initializes_storage {
                            None
                        } else {
                            if self.type_needs_semantic_drop(env, place_ty, expr_span)
                                && !place_ty.is_function()
                            {
                                self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                                    value_trait_id(env),
                                    vec![place_ty],
                                    vec![],
                                    vec![],
                                    expr_span,
                                ));
                            }
                            Some(PendingLocalDrop::Unknown)
                        };
                        let combined_effects =
                            self.make_dependent_effect([&value_effects, &place_effects]);
                        let node = K::Assign(hir::Assignment {
                            place: place_id,
                            value: value_id,
                            drop,
                        });
                        let node = self.wrap_unit_with_temp_drops(
                            env,
                            temp_start_index,
                            prepared_place.prefix,
                            hir::Node::new(node, Type::unit(), combined_effects.clone(), expr_span),
                        );
                        (node, Type::unit(), MutType::constant(), combined_effects)
                    }
                }
            }
            AssignOp(data) => {
                if Self::is_access_chain_expr(&env.ast_arena[data.place].kind) {
                    let place = self.access_chain_for_expr(env, data.place);
                    return self.infer_access_chain_assign_op(
                        env,
                        place,
                        data.sign_span,
                        &data.op_path,
                        data.value,
                        expr_span,
                    );
                }
                let (place_id, place_mut) = self.infer_expr(env, data.place)?;
                let place_span = env.ir_arena[place_id].span;
                let place_effects = env.ir_arena[place_id].effects.clone();
                if env.ir_arena[place_id].ty == Type::never() {
                    let effects = self.make_dependent_effect([&place_effects]);
                    self.diverging_prefix_result(env, [place_id], effects)
                } else {
                    self.add_mut_be_at_least_constraint(
                        place_mut,
                        place_span,
                        MutType::mutable(),
                        data.sign_span,
                    );
                    let (value_node, value_ty, _value_mut_ty, value_effects) = self
                        .infer_static_apply(
                            env,
                            &data.op_path,
                            data.sign_span,
                            &[data.place, data.value],
                            expr_span,
                            UnnamedArg::All,
                        )?;
                    let value_id =
                        env.ir_arena
                            .alloc(N::new(value_node, value_ty, value_effects, expr_span));
                    let value_ty = env.ir_arena[value_id].ty;
                    let value_span = env.ir_arena[value_id].span;
                    let place_ty = env.ir_arena[place_id].ty;
                    self.add_sub_type_constraint(value_ty, value_span, place_ty, place_span);
                    let value_effects = env.ir_arena[value_id].effects.clone();
                    if value_ty == Type::never() {
                        let mut nodes = self.place_evaluation_prefix_nodes(env.ir_arena, place_id);
                        nodes.push(value_id);
                        let effects = self.make_dependent_effect([&place_effects, &value_effects]);
                        self.diverging_prefix_result(env, nodes, effects)
                    } else {
                        let temp_start_index = env.cur_locals.len();
                        let prepared_place =
                            self.prepare_place_for_consumer(env, place_id, expr_span);
                        let place_id = prepared_place.place;
                        let value_id = self.materialize_owned_value(env, value_id, expr_span);
                        let initializes_storage =
                            assignment_initializes_storage(env.ir_arena, place_id, env);
                        let drop = if initializes_storage {
                            None
                        } else {
                            if self.type_needs_semantic_drop(env, place_ty, expr_span)
                                && !place_ty.is_function()
                            {
                                self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                                    value_trait_id(env),
                                    vec![place_ty],
                                    vec![],
                                    vec![],
                                    expr_span,
                                ));
                            }
                            Some(PendingLocalDrop::Unknown)
                        };
                        let combined_effects =
                            self.make_dependent_effect([&value_effects, &place_effects]);
                        let node = K::Assign(hir::Assignment {
                            place: place_id,
                            value: value_id,
                            drop,
                        });
                        let node = self.wrap_unit_with_temp_drops(
                            env,
                            temp_start_index,
                            prepared_place.prefix,
                            hir::Node::new(node, Type::unit(), combined_effects.clone(), expr_span),
                        );
                        (node, Type::unit(), MutType::constant(), combined_effects)
                    }
                }
            }
            Tuple(exprs) => {
                let (nodes, types, effects, diverges) =
                    self.infer_exprs_drop_mut_until_never(env, exprs)?;
                if diverges {
                    self.diverging_prefix_result(env, nodes, effects)
                } else {
                    let nodes = self.materialize_owned_values(env, nodes, expr_span);
                    let ty = Type::tuple(types);
                    let node = K::Tuple(b(SVec2::from_vec(nodes)));
                    (node, ty, MutType::constant(), effects)
                }
            }
            Project(data) => {
                // Generates the following constraints:
                // Project(tuple_expr: T, index) -> V
                //     where T: Coercible<Target = U>, TupleHasField(U, V, index)
                let (tuple_node_id, tuple_mut) = self.infer_expr(env, data.expr)?;
                let effects = env.ir_arena[tuple_node_id].effects.clone();
                // Note: tuple_node.ty is T
                let tuple_node_ty = env.ir_arena[tuple_node_id].ty;
                if tuple_node_ty == Type::never() {
                    self.diverging_prefix_result(env, [tuple_node_id], effects)
                } else {
                    let tuple_ty = self.fresh_type_var_ty(); // U
                    let (index, index_span) = data.index;
                    self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                        repr_trait_id(env),
                        vec![tuple_node_ty],
                        vec![tuple_ty],
                        vec![],
                        index_span,
                    ));
                    let element_ty = self.fresh_type_var_ty(); // V
                    self.add_pub_constraint(PubTypeConstraint::new_tuple_at_index_is(
                        tuple_ty,
                        sp(data.expr),
                        index,
                        index_span,
                        element_ty,
                    ));
                    let node = K::Project(HirProject::new(
                        tuple_node_id,
                        ProjectionIndex::from_index(index),
                    ));
                    (node, element_ty, tuple_mut, effects)
                }
            }
            Record(fields) => {
                // Check that all fields are unique and collect their expressions and names.
                let fields = Self::check_and_sort_record_fields(
                    fields,
                    expr_span,
                    DuplicatedFieldContext::Record,
                )?;
                // Infer the types of the nodes.
                let (node, ty, effects) = self.infer_record(env, &fields)?;
                (node, ty, MutType::constant(), effects)
            }
            StructLiteral(data) => {
                // Check that all fields are unique and collect their expressions and names.
                let fields = Self::check_and_sort_record_fields(
                    &data.fields,
                    expr_span,
                    DuplicatedFieldContext::Struct,
                )?;
                // First check if the path is a known type definition.
                if let Some(type_def) = env.get_type_def(&data.path)? {
                    // Then resolve the layout of the struct.
                    let (type_def, payload_ty, ty, tag) =
                        self.instantiate_type_def(type_def, expr_span, &env.module_env);
                    // Check that it is a record.
                    if !payload_ty.data().is_record() {
                        return Err(internal_compilation_error!(IsNotCorrectProductType {
                            which: WhichProductTypeIsNot::Record,
                            type_def,
                            what: WhatIsNotAProductType::from_tag(tag),
                            instantiation_span: expr_span,
                        }));
                    }
                    // Validate the fields towards the record layout.
                    let layout = payload_ty.data().clone().into_record().unwrap();
                    let layout_size = layout.len();
                    let layout_iter = layout.iter();
                    let fields_size = fields.len();
                    let field_iter = fields.iter();
                    for (layout_field, field) in layout_iter.zip(field_iter) {
                        let layout_field_name = layout_field.0;
                        let (field_name, field_span) = &field.0;
                        if &layout_field_name < field_name {
                            // Missing record entry
                            return Err(internal_compilation_error!(MissingStructField {
                                type_def,
                                field_name: layout_field.0,
                                instantiation_span: expr_span,
                            }));
                        } else if &layout_field_name > field_name {
                            // Extra record entry
                            return Err(internal_compilation_error!(InvalidStructField {
                                type_def,
                                field_name: *field_name,
                                field_span: *field_span,
                                instantiation_span: expr_span,
                            }));
                        }
                    }
                    if layout_size > fields_size {
                        // Layout still has entries: Missing record entry
                        let layout_field = layout[fields_size];
                        return Err(internal_compilation_error!(MissingStructField {
                            type_def,
                            field_name: layout_field.0,
                            instantiation_span: expr_span,
                        }));
                    } else if layout_size < fields_size {
                        // Record still has entries: Extra record entry
                        let field = fields[layout_size];
                        return Err(internal_compilation_error!(InvalidStructField {
                            type_def,
                            field_name: field.0.0,
                            field_span: field.0.1,
                            instantiation_span: expr_span,
                        }));
                    }
                    // Here we know that we have the right fields, validate the types.
                    let expected_tys = layout
                        .iter()
                        .map(|(_, ty)| FnArgType::new(*ty, MutType::constant()))
                        .collect::<Vec<_>>();
                    let exprs = fields.iter().map(|(_, expr)| *expr).collect::<Vec<_>>();
                    let (nodes, effects, diverges) =
                        self.check_exprs_until_never(env, &exprs, &expected_tys, expr_span)?;
                    if diverges {
                        self.diverging_prefix_result(env, nodes, effects)
                    } else {
                        let nodes = self.materialize_owned_values(env, nodes, expr_span);
                        let node = if let Some(tag) = tag {
                            let record_node_id = env.ir_arena.alloc(N::new(
                                K::Record(b(SVec2::from_vec(nodes))),
                                payload_ty,
                                effects.clone(),
                                expr_span,
                            ));
                            K::Variant(HirVariant::new(tag, record_node_id))
                        } else {
                            K::Record(b(SVec2::from_vec(nodes)))
                        };
                        (node, ty, MutType::constant(), effects)
                    }
                } else {
                    // Structural variants cannot be paths
                    if data.path.segments.len() > 1 {
                        return Err(internal_compilation_error!(InvalidVariantConstructor {
                            span: data.path.segments[0].1,
                        }));
                    }
                    // If it is not a known type def, assume it to be a variant constructor.
                    let (record_node, record_ty, effects) = self.infer_record(env, &fields)?;
                    let record_span =
                        Location::fuse(fields.iter().map(|(n, _)| n.1)).unwrap_or(expr_span);
                    let payload_node_id = env.ir_arena.alloc(N::new(
                        record_node,
                        record_ty,
                        effects.clone(),
                        record_span,
                    ));
                    // Create a fresh type and add a constraint for that type to include this variant.
                    let tag = data.path.segments[0].0;
                    let variant_ty = self.fresh_type_var_ty();
                    let payload_span = env.ir_arena[payload_node_id].span;
                    self.ty_constraints.push(TypeConstraint::Pub(
                        PubTypeConstraint::new_type_has_variant(
                            variant_ty,
                            expr_span,
                            tag,
                            record_ty,
                            payload_span,
                        ),
                    ));
                    let node = K::Variant(HirVariant::new(tag, payload_node_id));
                    (node, variant_ty, MutType::constant(), effects)
                }
            }
            FieldAccess(data) => {
                let place = AccessChain {
                    root: data.expr,
                    steps: vec![AccessChainStep::Field {
                        name: data.name,
                        base_span: sp(data.expr),
                        expr_span,
                    }],
                };
                return self.infer_access_chain_read(env, place, expr_span);
            }
            Array(exprs) => {
                if exprs.is_empty() {
                    // The element type is a fresh type variable
                    let element_ty = self.fresh_type_var_ty();
                    // Build an empty array node and return it
                    let node = K::Array(b(SVec2::from_vec(Vec::new())));
                    (
                        node,
                        env.array_type(element_ty),
                        MutType::constant(),
                        no_effects(),
                    )
                } else {
                    let (nodes, types, effects, diverges) =
                        self.infer_exprs_drop_mut_until_never(env, exprs)?;
                    if diverges {
                        self.diverging_prefix_result(env, nodes, effects)
                    } else {
                        let nodes = self.materialize_owned_values(env, nodes, expr_span);
                        // The element type is the first element's type
                        // All elements must be of the first element's type
                        let element_ty = types[0];
                        // Infer the type of the elements and collect their code and constraints
                        for (ty, expr) in types.into_iter().skip(1).zip(exprs.iter().skip(1)) {
                            self.add_sub_type_constraint(ty, sp(*expr), element_ty, sp(exprs[0]));
                        }
                        // Build the array node and return it
                        let element_nodes = SVec2::from_vec(nodes);
                        let ty = env.array_type(element_ty);
                        let node = K::Array(b(element_nodes));
                        (node, ty, MutType::constant(), effects)
                    }
                }
            }
            SetLiteral(_) | MapLiteral(_) => {
                unreachable!("collection literals should be desugared before type inference")
            }
            Index(data) => {
                let (array_node_id, array_expr_mut) = self.infer_expr(env, data.array)?;
                let (node, _mut_ty) = self.infer_index_node_from_array_node(
                    env,
                    array_node_id,
                    array_expr_mut,
                    sp(data.array),
                    data.index,
                    expr_span,
                )?;
                let node_id = env.ir_arena.alloc(node);
                let value_id = self.materialize_owned_value(env, node_id, expr_span);
                return Ok((value_id, MutType::constant()));
            }
            EffectsUnsafe(expr) => {
                if env.current_module_id() != STD_MODULE_ID {
                    return Err(
                        InternalCompilationError::new_unsafe_feature_use_not_allowed(
                            UnsafeFeature::EffectsUnsafe,
                            expr_span,
                        ),
                    );
                }

                let (inner_node_id, inner_mut_ty) = self.infer_expr(env, *expr)?;
                return Ok((
                    self.strip_effects_from_node(env, inner_node_id, expr_span),
                    inner_mut_ty,
                ));
            }
            Match(data) => {
                let (node, ty, mut_ty, effects) = self.infer_match(
                    env,
                    expr_span,
                    data.cond_expr,
                    &data.alternatives,
                    &data.default,
                )?;
                (node, ty, mut_ty, effects)
            }
            ForLoop(_for_loop) => {
                unreachable!("this cannot happen as payload is never")
            }
            Loop(data) => {
                let label = self.fresh_loop_id();
                let result_ty = self.fresh_type_var();
                let local_scope_start = env.cur_locals.len();
                env.loop_frames.push(LoopFrame::new(
                    label,
                    data.label,
                    result_ty,
                    local_scope_start,
                    false,
                ));
                let mut body_id = self.check_expr(
                    env,
                    data.body,
                    Type::unit(),
                    MutType::constant(),
                    sp(data.body),
                )?;
                let loop_frame = env.loop_frames.pop().unwrap();
                if env.fuel_checks_enabled {
                    let check_id = env.ir_arena.alloc(N::new(
                        K::CheckFuel,
                        Type::unit(),
                        effect(PrimitiveEffect::Fallible),
                        expr_span,
                    ));
                    let body_effects = env.ir_arena[body_id].effects.clone();
                    let effects = self
                        .make_dependent_effect([&env.ir_arena[check_id].effects, &body_effects]);
                    body_id = env.ir_arena.alloc(N::new(
                        Self::block(vec![check_id, body_id], Vec::new()),
                        Type::unit(),
                        effects,
                        expr_span,
                    ));
                }
                let effects = env.ir_arena[body_id].effects.clone();
                let ty = if loop_frame.saw_break {
                    Type::variable(loop_frame.result_ty)
                } else {
                    Type::never()
                };
                (
                    K::Loop(hir::Loop {
                        label,
                        body: body_id,
                    }),
                    ty,
                    MutType::constant(),
                    effects,
                )
            }
            Break(data) => {
                let loop_frame_index = Self::resolve_loop_frame(
                    &env.loop_frames,
                    data.label,
                    expr_span,
                    LoopControlKind::Break,
                )?;
                let loop_frame = &mut env.loop_frames[loop_frame_index];
                let label = loop_frame.label;
                let result_ty = loop_frame.result_ty;
                let local_scope_start = loop_frame.local_scope_start;
                loop_frame.saw_break = true;
                let value = if let Some(value) = data.value {
                    let value = self.check_expr(
                        env,
                        value,
                        Type::variable(result_ty),
                        MutType::constant(),
                        sp(value),
                    )?;
                    self.prepare_value_for_exit(env, value, local_scope_start, expr_span)
                } else {
                    let value = env.ir_arena.alloc(N::new(
                        K::Immediate(LiteralValue::new_native(())),
                        Type::unit(),
                        no_effects(),
                        expr_span,
                    ));
                    self.add_same_type_with_sub_effects_constraint(
                        Type::variable(result_ty),
                        expr_span,
                        Type::unit(),
                        expr_span,
                    );
                    value
                };
                let effects = env.ir_arena[value].effects.clone();
                (
                    K::Break(hir::Break { label, value }),
                    Type::never(),
                    MutType::constant(),
                    effects,
                )
            }
            Continue(data) => {
                let loop_frame_index = Self::resolve_loop_frame(
                    &env.loop_frames,
                    data.label,
                    expr_span,
                    LoopControlKind::Continue,
                )?;
                let label = env.loop_frames[loop_frame_index].label;
                (
                    K::Continue(hir::Continue { label }),
                    Type::never(),
                    MutType::constant(),
                    no_effects(),
                )
            }
            PropertyPath(data) => {
                let fn_path = property_to_fn_path(
                    &data.path,
                    &data.name,
                    PropertyAccess::Get,
                    expr_span,
                    env,
                )?;
                self.infer_static_apply(
                    env,
                    &fn_path,
                    expr_span,
                    &[] as &[DExprId],
                    expr_span,
                    UnnamedArg::All,
                )?
            }
            TypeAscription(data) => {
                let (node_id, mut_type) = self.infer_expr(env, data.expr)?;
                let ty = data
                    .ty
                    .map(&mut AnnotationTypeMapper::new(self, env.annotation_subst));
                self.add_same_type_with_sub_effects_constraint(
                    env.ir_arena[node_id].ty,
                    sp(data.expr),
                    ty,
                    data.span,
                );
                return Ok((node_id, mut_type));
            }
            Error => {
                panic!("attempted to infer type for error node");
            }
        };
        Ok((
            env.ir_arena
                .alloc(N::new(node, ty, effects.clone(), expr_span)),
            mut_ty,
        ))
    }

    fn infer_expr_drop_mut(
        &mut self,
        env: &mut TypingEnv,
        expr: DExprId,
    ) -> Result<NodeId, InternalCompilationError> {
        Ok(self.infer_expr(env, expr)?.0)
    }

    fn infer_expr_as_place_return(
        &mut self,
        env: &mut TypingEnv,
        expr: DExprId,
    ) -> Result<NodeId, InternalCompilationError> {
        let expr_span = env.ast_arena[expr].span;
        if Self::is_access_chain_expr(&env.ast_arena[expr].kind) {
            let chain = self.access_chain_for_expr(env, expr);
            let mode = if env
                .subscript_member
                .is_some_and(|subscript_member| subscript_member.requires_mutable_place)
            {
                SubscriptMemberKind::Mut
            } else {
                SubscriptMemberKind::Ref
            };
            return self
                .infer_access_chain_with_body(
                    env,
                    chain,
                    mode,
                    expr_span,
                    |_, _, place, place_ty| Ok((place, place_ty)),
                )
                .map(|(node, _)| node);
        }
        match env.ast_arena[expr].kind.clone() {
            ExprKind::EffectsUnsafe(inner) => {
                if env.current_module_id() != STD_MODULE_ID {
                    return Err(
                        InternalCompilationError::new_unsafe_feature_use_not_allowed(
                            UnsafeFeature::EffectsUnsafe,
                            expr_span,
                        ),
                    );
                }

                let inner_node_id = self.infer_expr_as_place_return(env, inner)?;
                Ok(self.strip_effects_from_node(env, inner_node_id, expr_span))
            }
            ExprKind::Block(exprs) => {
                assert!(!exprs.is_empty());
                let env_size = env.cur_locals.len();
                let tail_expr = *exprs.last().expect("non-empty block should have a tail");
                let mut nodes = Vec::with_capacity(exprs.len());
                for expr in &exprs[..exprs.len() - 1] {
                    let node = self.infer_expr_drop_mut(env, *expr)?;
                    let diverges = env.ir_arena[node].ty == Type::never();
                    let node = if diverges {
                        node
                    } else {
                        self.discard_unused_value(env, node, expr_span)
                    };
                    nodes.push(node);
                    if diverges {
                        break;
                    }
                }
                if nodes
                    .last()
                    .is_none_or(|node| env.ir_arena[*node].ty != Type::never())
                {
                    nodes.push(self.infer_expr_as_place_return(env, tail_expr)?);
                }

                Self::extend_local_scopes_to_span_end(env, env_size, expr_span);
                let ty = nodes
                    .last()
                    .map_or(Type::unit(), |node| env.ir_arena[*node].ty);
                let effects = self.make_dependent_effect(
                    nodes
                        .iter()
                        .map(|node| env.ir_arena[*node].effects.clone())
                        .collect::<Vec<_>>(),
                );
                let kind = self.close_block_scope(env, env_size, nodes);
                Ok(env
                    .ir_arena
                    .alloc(hir::Node::new(kind, ty, effects, expr_span)))
            }
            _ => self.infer_expr_drop_mut(env, expr),
        }
    }

    fn direct_local_place_return_root(arena: &NodeArena, node_id: NodeId) -> Option<LocalDeclId> {
        match &arena[node_id].kind {
            NodeKind::LoadLocal(load) => Some(load.id),
            NodeKind::Block(block) => block
                .body
                .last()
                .and_then(|tail| Self::direct_local_place_return_root(arena, *tail)),
            _ => None,
        }
    }

    pub(crate) fn check_implicit_addressor_return_expr(
        &mut self,
        env: &mut TypingEnv,
        expr: DExprId,
        expected_ty: Type,
        expected_span: Location,
    ) -> Result<NodeId, InternalCompilationError> {
        let expr_span = env.ast_arena[expr].span;
        let node_id = self.infer_expr_as_place_return(env, expr)?;
        let ty = env.ir_arena[node_id].ty;
        self.add_same_type_with_sub_effects_constraint(ty, expr_span, expected_ty, expected_span);
        if ty == Type::never() {
            return Ok(node_id);
        }
        if !node_is_place_reference(env.ir_arena, node_id) {
            return Err(internal_compilation_error!(InvalidSubscriptDefinition {
                subject: env.subscript_member.map_or(
                    SubscriptDefinitionSubject::AddressorFunction(env.function_name),
                    |subscript_member| {
                        SubscriptDefinitionSubject::SubscriptMember(subscript_member.name)
                    },
                ),
                kind: InvalidSubscriptDefinitionKind::AddressorReturnMustBePlace,
                span: expr_span,
            }));
        }
        // Implicit addressor members may infer the base receiver as `&mut` when
        // returning it directly as a place. Roots in other parameters are still
        // rejected by the addressor-root check instead of inferred here.
        if let Some(local_id) = Self::direct_local_place_return_root(env.ir_arena, node_id)
            && env.cur_locals.first().is_some_and(|base| *base == local_id)
        {
            let local = &env.all_locals[local_id.as_index()];
            if local.mut_ty.is_variable() {
                self.add_mut_be_at_least_constraint(
                    local.mut_ty,
                    env.ir_arena[node_id].span,
                    MutType::mutable(),
                    expr_span,
                );
            }
        }
        let effects = env.ir_arena[node_id].effects.clone();
        Ok(env.ir_arena.alloc(hir::Node::new(
            NodeKind::Return(node_id),
            Type::never(),
            effects,
            expr_span,
        )))
    }

    fn ensure_named_subscript_access_allowed(
        env: &TypingEnv,
        name: Ustr,
        span: Location,
    ) -> Result<(), InternalCompilationError> {
        if !env.compilation_capabilities.allow_experimental {
            return Err(internal_compilation_error!(InvalidSubscriptUse {
                name,
                kind: InvalidSubscriptUseKind::ExperimentalFeatureNotEnabled,
                span,
            }));
        }
        Ok(())
    }

    fn infer_index_from_array_node(
        &mut self,
        env: &mut TypingEnv,
        array_node_id: NodeId,
        array_expr_mut: MutType,
        array_span: Location,
        index: DExprId,
        expr_span: Location,
    ) -> Result<(NodeId, Type, MutType), InternalCompilationError> {
        let (node, mut_ty) = self.infer_index_node_from_array_node(
            env,
            array_node_id,
            array_expr_mut,
            array_span,
            index,
            expr_span,
        )?;
        let ty = node.ty;
        let node_id = env.ir_arena.alloc(node);
        Ok((node_id, ty, mut_ty))
    }

    fn infer_index_node_from_array_node(
        &mut self,
        env: &mut TypingEnv,
        array_node_id: NodeId,
        array_expr_mut: MutType,
        array_span: Location,
        index: DExprId,
        expr_span: Location,
    ) -> Result<(hir::Node, MutType), InternalCompilationError> {
        let element_ty = self.fresh_type_var_ty();
        let array_ty = env.array_type(element_ty);
        let array_effects = env.ir_arena[array_node_id].effects.clone();
        if env.ir_arena[array_node_id].ty == Type::never() {
            let effects = self.make_dependent_effect([&array_effects]);
            let node = hir::Node::new(
                Self::block(vec![array_node_id], Vec::new()),
                Type::never(),
                effects,
                expr_span,
            );
            return Ok((node, MutType::constant()));
        }

        self.add_sub_type_constraint(
            env.ir_arena[array_node_id].ty,
            array_span,
            array_ty,
            array_span,
        );
        let index_node_id = self.check_expr(
            env,
            index,
            int_type(),
            MutType::constant(),
            env.ast_arena[index].span,
        )?;
        let index_effects = env.ir_arena[index_node_id].effects.clone();
        if env.ir_arena[index_node_id].ty == Type::never() {
            let mut nodes = self.place_evaluation_prefix_nodes(env.ir_arena, array_node_id);
            nodes.push(index_node_id);
            let effects = self.make_dependent_effect([&array_effects, &index_effects]);
            let node = hir::Node::new(
                Self::block(nodes, Vec::new()),
                Type::never(),
                effects,
                expr_span,
            );
            return Ok((node, MutType::constant()));
        }

        let (path, (definition, function, _module_id, runtime_arg_passing)) = {
            let (
                path,
                (_subscript, member, (definition, function, module_id, runtime_arg_passing)),
            ) = env.get_std_subscript_member(ustr("array_index"), false, expr_span)?;
            // `array_index` is currently declared as one shared `ref mut`
            // member, so selecting the ref slot still yields the mutable
            // addressor place when the array expression itself is mutable.
            let _provenance = member.provenance;
            debug_assert_eq!(_provenance, YieldProvenance::AddressorPlace);
            (
                path,
                (definition.clone(), function, module_id, runtime_arg_passing),
            )
        };
        let (inst_fn_ty, inst_data, _subst) =
            definition
                .ty_scheme
                .instantiate_with_fresh_vars(self, expr_span, None, env.module_env);
        self.add_same_type_with_sub_effects_constraint(
            inst_fn_ty.ret,
            expr_span,
            element_ty,
            expr_span,
        );
        let combined_effects = self.make_dependent_effect([
            &effect(PrimitiveEffect::Fallible),
            &array_effects,
            &index_effects,
            &inst_fn_ty.effects,
        ]);
        let mut argument_values = vec![array_node_id, index_node_id];
        let visible_arg_passing = visible_arg_passing_from_runtime(
            runtime_arg_passing.as_deref(),
            &inst_data,
            argument_values.len(),
        );
        let temp_start_index = env.cur_locals.len();
        let prepared_arguments = self.prepare_call_arguments(
            env,
            &mut argument_values,
            &inst_fn_ty.args,
            &definition.ty_scheme.ty.args,
            expr_span,
            visible_arg_passing,
        );
        let call = NodeKind::StaticApply(b(hir::StaticApplication {
            function,
            function_path: Some(path),
            function_span: expr_span,
            extra_arguments: Vec::new(),
            arguments: prepared_arguments.arguments,
            argument_names: vec![ustr("array"), ustr("index")],
            ty: CallImplType::new(inst_fn_ty, definition.result_convention),
            inst_data,
        }));
        let call = hir::Node::new(call, element_ty, combined_effects.clone(), expr_span);
        let node = self.wrap_call_with_temp_drops(
            env,
            temp_start_index,
            prepared_arguments.temp_stores,
            call,
        );
        Ok((
            hir::Node::new(node, element_ty, combined_effects, expr_span),
            array_expr_mut,
        ))
    }

    fn named_subscript_member(
        &self,
        env: &TypingEnv,
        data: &ast::NamedSubscriptData<Desugared>,
        mode: SubscriptMemberKind,
    ) -> Result<SubscriptMember, InternalCompilationError> {
        let Some(subscript) = env.module_env.current.get_subscript(data.name.0) else {
            return Err(internal_compilation_error!(InvalidSubscriptUse {
                name: data.name.0,
                kind: InvalidSubscriptUseKind::UnknownSubscript,
                span: data.name.1,
            }));
        };
        let member = match mode {
            SubscriptMemberKind::Ref => subscript.ref_member.as_ref(),
            SubscriptMemberKind::Mut => subscript.mut_member.as_ref(),
        };
        member
            .cloned()
            .ok_or_else(|| Self::missing_subscript_member_error(data.name, mode))
    }

    fn missing_subscript_member_error(
        name: UstrSpan,
        mode: SubscriptMemberKind,
    ) -> InternalCompilationError {
        internal_compilation_error!(InvalidSubscriptUse {
            name: name.0,
            kind: InvalidSubscriptUseKind::MissingMember(mode),
            span: name.1,
        })
    }

    fn select_subscript_member_type(
        subscript_ty: &SubscriptType,
        mode: SubscriptMemberKind,
        name: UstrSpan,
    ) -> Result<&SubscriptMemberType, InternalCompilationError> {
        let member = match mode {
            SubscriptMemberKind::Ref => subscript_ty.ref_member.as_ref(),
            SubscriptMemberKind::Mut => subscript_ty.mut_member.as_ref(),
        };
        member.ok_or_else(|| Self::missing_subscript_member_error(name, mode))
    }

    fn named_subscript_args(data: &ast::NamedSubscriptData<Desugared>) -> Vec<DExprId> {
        std::iter::once(data.receiver)
            .chain(data.args.iter().copied())
            .collect()
    }

    fn find_explicit_projection_subscript(
        &mut self,
        env: &mut TypingEnv,
        key: ProjectionKey,
        track_dependency: bool,
    ) -> Option<SubscriptId> {
        if self.projection_subscript_miss_cache.contains(&key) {
            return None;
        }
        let subscript = env.module_env.projection_subscript(key);
        let Some(subscript) = subscript else {
            self.projection_subscript_miss_cache.insert(key);
            return None;
        };
        if track_dependency && subscript.module != env.current_module_id() {
            env.new_deps.insert(subscript.module);
        }
        Some(subscript)
    }

    fn explicit_projection_subscript(
        &mut self,
        env: &mut TypingEnv,
        receiver_ty: Type,
        field: Ustr,
    ) -> Option<SubscriptId> {
        let key = ProjectionKey::nominal_for_receiver_ty(receiver_ty, field)?;
        if env
            .subscript_member
            .and_then(|subscript_member| subscript_member.projection_key)
            == Some(key)
        {
            return None;
        }
        self.find_explicit_projection_subscript(env, key, true)
    }

    fn is_access_chain_expr(expr: &ExprKind<Desugared>) -> bool {
        matches!(
            expr,
            ExprKind::FieldAccess(_)
                | ExprKind::Index(_)
                | ExprKind::NamedSubscript(_)
                | ExprKind::Project(_)
        )
    }

    /// Whether an access-chain argument must be driven even before its final passing is known.
    /// Named subscripts force driving; explicit `.field` projections wait for resolved passing.
    fn access_chain_plan_may_need_projection_driver(plan: &AccessChainPlan) -> bool {
        plan.contains_named_subscript
    }

    fn access_chain_root_is_stable_place(env: &TypingEnv, chain: &AccessChain) -> bool {
        let ExprKind::Identifier(path) = &env.ast_arena[chain.root].kind else {
            return false;
        };
        let [(name, _)] = &path.segments[..] else {
            return false;
        };
        env.get_variable_id(name).is_some()
    }

    fn access_chain_for_expr(&self, env: &TypingEnv, expr: DExprId) -> AccessChain {
        self.access_chain_plan_for_expr(env, expr).chain
    }

    fn access_chain_plan_for_expr(&self, env: &TypingEnv, expr: DExprId) -> AccessChainPlan {
        let mut steps = Vec::new();
        let mut contains_named_subscript = false;
        let root =
            self.collect_access_chain_steps(env, expr, &mut steps, &mut contains_named_subscript);
        let chain = AccessChain { root, steps };
        AccessChainPlan {
            chain,
            contains_named_subscript,
        }
    }

    fn collect_access_chain_steps(
        &self,
        env: &TypingEnv,
        expr: DExprId,
        steps: &mut Vec<AccessChainStep>,
        contains_named_subscript: &mut bool,
    ) -> DExprId {
        match &env.ast_arena[expr].kind {
            ExprKind::FieldAccess(data) => {
                let root = self.collect_access_chain_steps(
                    env,
                    data.expr,
                    steps,
                    contains_named_subscript,
                );
                steps.push(AccessChainStep::Field {
                    name: data.name,
                    base_span: env.ast_arena[data.expr].span,
                    expr_span: env.ast_arena[expr].span,
                });
                root
            }
            ExprKind::Index(data) => {
                let root = self.collect_access_chain_steps(
                    env,
                    data.array,
                    steps,
                    contains_named_subscript,
                );
                steps.push(AccessChainStep::Index {
                    index: data.index,
                    array_span: env.ast_arena[data.array].span,
                    expr_span: env.ast_arena[expr].span,
                });
                root
            }
            ExprKind::NamedSubscript(data) => {
                let root = self.collect_access_chain_steps(
                    env,
                    data.receiver,
                    steps,
                    contains_named_subscript,
                );
                *contains_named_subscript = true;
                steps.push(AccessChainStep::NamedSubscript {
                    data: (**data).clone(),
                });
                root
            }
            ExprKind::Project(data) => {
                let root = self.collect_access_chain_steps(
                    env,
                    data.expr,
                    steps,
                    contains_named_subscript,
                );
                steps.push(AccessChainStep::Project {
                    index: data.index,
                    base_span: env.ast_arena[data.expr].span,
                    expr_span: env.ast_arena[expr].span,
                });
                root
            }
            _ => expr,
        }
    }

    fn infer_named_subscript_accessor_call(
        &mut self,
        env: &mut TypingEnv,
        data: &ast::NamedSubscriptData<Desugared>,
        mode: SubscriptMemberKind,
        expr_span: Location,
        receiver_override: Option<NamedSubscriptReceiverOverride>,
    ) -> Result<PreparedNamedSubscriptAccessor, InternalCompilationError> {
        if let Some(prepared) =
            self.infer_subscript_value_accessor_call(env, data, mode, expr_span, receiver_override)?
        {
            return Ok(prepared);
        }
        Self::ensure_named_subscript_access_allowed(env, data.name.0, expr_span)?;
        let member = self.named_subscript_member(env, data, mode)?;
        let function_data = env
            .module_env
            .current
            .get_function_by_id(member.function)
            .expect("subscript member function should exist");
        let definition = function_data.definition.clone();
        let runtime_arg_passing = function_data
            .code
            .runtime_argument_passing()
            .map(<[_]>::to_vec);
        let args = Self::named_subscript_args(data);
        if definition.ty_scheme.ty.args.len() != args.len() {
            return Err(internal_compilation_error!(WrongNumberOfArguments {
                expected: definition.ty_scheme.ty.args.len(),
                expected_span: data.name.1,
                got: args.len(),
                got_span: Location::fuse(args.iter().map(|arg| env.ast_arena[*arg].span))
                    .unwrap_or(expr_span),
            }));
        }

        let (inst_fn_ty, inst_data, _subst) = definition.ty_scheme.instantiate_with_fresh_vars(
            self,
            data.name.1,
            None,
            env.module_env,
        );
        let member_effects = inst_fn_ty.effects.clone();
        let (mut args_node_ids, args_effects, args_diverge) = self
            .check_named_subscript_args_until_never(
                env,
                &args,
                &inst_fn_ty.args,
                receiver_override,
                data.name.1,
            )?;
        if args_diverge {
            let nodes = self.value_evaluation_prefix_nodes_for_many(env.ir_arena, args_node_ids);
            let effects = self.make_dependent_effect([&args_effects, &member_effects]);
            return Ok(PreparedNamedSubscriptAccessor::DivergedBeforeYield(
                self.alloc_diverging_prefix_node(env, nodes, effects, expr_span),
            ));
        }

        let ret_ty = inst_fn_ty.ret;
        let combined_effects = self.make_dependent_effect([&args_effects, &member_effects]);
        let visible_arg_passing = visible_arg_passing_from_runtime(
            runtime_arg_passing.as_deref(),
            &inst_data,
            args_node_ids.len(),
        );
        let temp_start_index = env.cur_locals.len();
        let prepared_arguments = self.prepare_call_arguments(
            env,
            &mut args_node_ids,
            &inst_fn_ty.args,
            &definition.ty_scheme.ty.args,
            expr_span,
            visible_arg_passing,
        );
        let call = NodeKind::StaticApply(b(hir::StaticApplication {
            function: FunctionId::new(env.current_module_id(), member.function),
            function_path: None,
            function_span: data.name.1,
            extra_arguments: Vec::new(),
            arguments: prepared_arguments.arguments,
            argument_names: definition.arg_names.clone(),
            ty: CallImplType::new(inst_fn_ty, definition.result_convention),
            inst_data,
        }));
        let call = hir::Node::new(call, ret_ty, combined_effects.clone(), expr_span);
        let node = self.wrap_call_with_temp_drops(
            env,
            temp_start_index,
            prepared_arguments.temp_stores,
            call,
        );
        let node = env.ir_arena.alloc(hir::Node::new(
            node,
            ret_ty,
            combined_effects.clone(),
            expr_span,
        ));
        Ok(PreparedNamedSubscriptAccessor::Ready(NamedSubscriptCall {
            node,
            ty: ret_ty,
            effects: combined_effects,
            provenance: member.provenance,
        }))
    }

    fn infer_subscript_value_accessor_call(
        &mut self,
        env: &mut TypingEnv,
        data: &ast::NamedSubscriptData<Desugared>,
        mode: SubscriptMemberKind,
        expr_span: Location,
        receiver_override: Option<NamedSubscriptReceiverOverride>,
    ) -> Result<Option<PreparedNamedSubscriptAccessor>, InternalCompilationError> {
        // Keep this path aligned with `infer_named_subscript_accessor_call`:
        // both prepare the same receiver-first accessor shape, but this one
        // starts from a first-class subscript value instead of a statically
        // resolved member function.
        let Some(local_id) = env.get_variable_id(data.name.0.as_ref()) else {
            return Ok(None);
        };
        Self::ensure_named_subscript_access_allowed(env, data.name.0, expr_span)?;

        let local = &env.all_locals[local_id.as_index()];
        let subscript_node = env.ir_arena.alloc(hir::Node::new(
            NodeKind::LoadLocal(hir::LoadLocal { id: local_id }),
            local.ty,
            no_effects(),
            data.name.1,
        ));
        let args = Self::named_subscript_args(data);
        let subscript_ty_data = local.ty.data().clone();
        let (subscript_ty, member_effects, result_convention, provenance) = match subscript_ty_data
        {
            TypeKind::Subscript(subscript_ty) => {
                let subscript_ty = (*subscript_ty).clone();
                let member_ty = Self::select_subscript_member_type(&subscript_ty, mode, data.name)?;
                let member_effects = member_ty.effects.clone();
                let result_convention =
                    CallResultConvention::Subscript(member_ty.result_convention);
                let provenance = match member_ty.result_convention {
                    SubscriptResultConvention::YieldedOnce => YieldProvenance::YieldedOnce,
                    SubscriptResultConvention::AddressorPlace => YieldProvenance::AddressorPlace,
                };
                (subscript_ty, member_effects, result_convention, provenance)
            }
            TypeKind::Variable(_) => {
                // A non-owning local here is an abstract capability parameter
                // whose type can still be inferred as `SubscriptType`. An owned
                // local, such as `let cell = 0`, must stay an ordinary value and
                // produce the usual "value is not a subscript" diagnostic.
                if local.may_own_storage() {
                    return Err(internal_compilation_error!(InvalidSubscriptUse {
                        name: data.name.0,
                        kind: InvalidSubscriptUseKind::ValueIsNotSubscript,
                        span: data.name.1,
                    }));
                }
                let member_effects = self.fresh_effect_var_ty();
                let subscript_ty = self.abstract_yielded_subscript_type(
                    env,
                    mode,
                    &args,
                    member_effects.clone(),
                    receiver_override.as_ref().map(|receiver| receiver.mut_ty),
                );
                self.add_sub_type_constraint(
                    local.ty,
                    data.name.1,
                    Type::subscript_type(subscript_ty.clone()),
                    data.name.1,
                );
                (
                    subscript_ty,
                    member_effects,
                    CallResultConvention::YIELDED_ONCE,
                    YieldProvenance::YieldedOnce,
                )
            }
            _ => {
                return Err(internal_compilation_error!(InvalidSubscriptUse {
                    name: data.name.0,
                    kind: InvalidSubscriptUseKind::ValueIsNotSubscript,
                    span: data.name.1,
                }));
            }
        };
        let inst_fn_ty = FnType::new(
            subscript_ty.args.clone(),
            subscript_ty.ret,
            member_effects.clone(),
        );
        if inst_fn_ty.args.len() != args.len() {
            return Err(internal_compilation_error!(WrongNumberOfArguments {
                expected: inst_fn_ty.args.len(),
                expected_span: data.name.1,
                got: args.len(),
                got_span: Location::fuse(args.iter().map(|arg| env.ast_arena[*arg].span))
                    .unwrap_or(expr_span),
            }));
        }

        let (args_node_ids, args_effects, args_diverge) = self
            .check_named_subscript_args_until_never(
                env,
                &args,
                &inst_fn_ty.args,
                receiver_override,
                data.name.1,
            )?;
        let subscript_effects = env.ir_arena[subscript_node].effects.clone();
        if args_diverge {
            let nodes = self
                .value_evaluation_prefix_nodes(env.ir_arena, subscript_node)
                .into_iter()
                .chain(self.value_evaluation_prefix_nodes_for_many(env.ir_arena, args_node_ids))
                .collect::<Vec<_>>();
            let effects =
                self.make_dependent_effect([&subscript_effects, &args_effects, &member_effects]);
            return Ok(Some(PreparedNamedSubscriptAccessor::DivergedBeforeYield(
                self.alloc_diverging_prefix_node(env, nodes, effects, expr_span),
            )));
        }

        let combined_effects =
            self.make_dependent_effect([&subscript_effects, &args_effects, &member_effects]);
        let call = self.build_subscript_apply_call(
            env,
            subscript_node,
            ustr("$subscript"),
            args_node_ids,
            inst_fn_ty,
            result_convention,
            mode,
            combined_effects,
            expr_span,
            provenance,
        );
        Ok(Some(PreparedNamedSubscriptAccessor::Ready(call)))
    }

    #[allow(clippy::too_many_arguments)]
    fn build_subscript_apply_call(
        &mut self,
        env: &mut TypingEnv,
        subscript_node: NodeId,
        subscript_temp_name: Ustr,
        mut args_node_ids: Vec<NodeId>,
        inst_fn_ty: FnType,
        result_convention: CallResultConvention,
        mode: SubscriptMemberKind,
        combined_effects: EffType,
        expr_span: Location,
        provenance: YieldProvenance,
    ) -> NamedSubscriptCall {
        let ret_ty = inst_fn_ty.ret;
        let temp_start_index = env.cur_locals.len();
        let mut temp_stores = Vec::new();
        let subscript = if node_is_place_reference(env.ir_arena, subscript_node) {
            let prepared = self.prepare_place_for_consumer(env, subscript_node, expr_span);
            temp_stores.extend(prepared.prefix);
            prepared.place
        } else {
            let (store, load) = self.store_owned_temp(
                env,
                subscript_node,
                env.ir_arena[subscript_node].ty,
                expr_span,
                subscript_temp_name,
            );
            temp_stores.push(store);
            load
        };
        let prepared_arguments = self.prepare_call_arguments(
            env,
            &mut args_node_ids,
            &inst_fn_ty.args,
            &inst_fn_ty.args,
            expr_span,
            None,
        );
        temp_stores.extend(prepared_arguments.temp_stores);
        let call = NodeKind::SubscriptApply(b(hir::SubscriptApplication {
            subscript,
            mut_member: matches!(mode, SubscriptMemberKind::Mut),
            arguments: prepared_arguments.arguments,
            ty: CallImplType::new(inst_fn_ty, result_convention),
        }));
        let call = hir::Node::new(call, ret_ty, combined_effects.clone(), expr_span);
        let node = self.wrap_call_with_temp_drops(env, temp_start_index, temp_stores, call);
        let node = env.ir_arena.alloc(hir::Node::new(
            node,
            ret_ty,
            combined_effects.clone(),
            expr_span,
        ));
        NamedSubscriptCall {
            node,
            ty: ret_ty,
            effects: combined_effects,
            provenance,
        }
    }

    fn infer_projection_subscript_accessor_call(
        &mut self,
        env: &mut TypingEnv,
        subscript_id: SubscriptId,
        field: UstrSpan,
        mode: SubscriptMemberKind,
        expr_span: Location,
        receiver: NamedSubscriptReceiverOverride,
    ) -> Result<PreparedNamedSubscriptAccessor, InternalCompilationError> {
        let (subscript_ty, inst_data, provenance) = {
            let owner = env.subscript_owner_module(subscript_id);
            let subscript = owner
                .get_subscript_by_id(subscript_id.subscript)
                .expect("projection subscript id should resolve");
            let selected_member = match mode {
                SubscriptMemberKind::Ref => subscript.ref_member.as_ref(),
                SubscriptMemberKind::Mut => subscript.mut_member.as_ref(),
            }
            .ok_or_else(|| Self::missing_subscript_member_error(field, mode))?;
            let (subscript_ty, inst_data, _subst) = subscript
                .type_scheme(owner)
                .expect("projection subscript signature should be resolved before use")
                .instantiate_with_fresh_vars(self, field.1, None, env.module_env);
            (subscript_ty, inst_data, selected_member.provenance)
        };
        if subscript_ty.args.len() != 1 {
            return Err(internal_compilation_error!(WrongNumberOfArguments {
                expected: subscript_ty.args.len(),
                expected_span: field.1,
                got: 1,
                got_span: env.ir_arena[receiver.node].span,
            }));
        }
        let member_ty = Self::select_subscript_member_type(&subscript_ty, mode, field)?;

        let arg_ty = subscript_ty.args[0];
        self.add_sub_type_constraint(
            receiver.ty,
            env.ir_arena[receiver.node].span,
            arg_ty.ty,
            field.1,
        );
        self.add_mut_be_at_least_constraint(
            receiver.mut_ty,
            env.ir_arena[receiver.node].span,
            arg_ty.mut_ty,
            field.1,
        );
        if matches!(mode, SubscriptMemberKind::Mut) {
            self.add_mut_be_at_least_constraint(
                receiver.mut_ty,
                env.ir_arena[receiver.node].span,
                MutType::mutable(),
                field.1,
            );
        }

        let subscript_node = env.ir_arena.alloc(hir::Node::new(
            NodeKind::GetSubscript(b(hir::GetSubscript {
                subscript: subscript_id,
                subscript_path: ast::Path::new(vec![field]),
                inst_data,
            })),
            Type::subscript_type(subscript_ty.clone()),
            no_effects(),
            field.1,
        ));
        let args_node_ids = vec![receiver.node];
        let mut inst_fn_args = subscript_ty.args.clone();
        if matches!(mode, SubscriptMemberKind::Mut) {
            inst_fn_args[0].mut_ty = MutType::mutable();
        }
        let inst_fn_ty = FnType::new(inst_fn_args, subscript_ty.ret, member_ty.effects.clone());
        let subscript_effects = env.ir_arena[subscript_node].effects.clone();
        let receiver_effects = env.ir_arena[receiver.node].effects.clone();
        let combined_effects =
            self.make_dependent_effect([&subscript_effects, &receiver_effects, &member_ty.effects]);
        let result_convention = CallResultConvention::Subscript(member_ty.result_convention);
        let call = self.build_subscript_apply_call(
            env,
            subscript_node,
            ustr("$projection_subscript"),
            args_node_ids,
            inst_fn_ty,
            result_convention,
            mode,
            combined_effects,
            expr_span,
            provenance,
        );
        Ok(PreparedNamedSubscriptAccessor::Ready(call))
    }

    fn check_named_subscript_args_until_never(
        &mut self,
        env: &mut TypingEnv,
        args: &[DExprId],
        arg_tys: &[FnArgType],
        receiver_override: Option<NamedSubscriptReceiverOverride>,
        expected_span: Location,
    ) -> Result<(Vec<NodeId>, EffType, bool), InternalCompilationError> {
        let Some(receiver) = receiver_override else {
            return self.check_exprs_until_never(env, args, arg_tys, expected_span);
        };

        let mut node_ids = Vec::with_capacity(args.len());
        let mut effects = Vec::with_capacity(args.len());
        let mut diverges = false;
        for (index, (arg, arg_ty)) in args.iter().zip(arg_tys).enumerate() {
            let node_id = if index == 0 {
                self.add_sub_type_constraint(
                    receiver.ty,
                    env.ir_arena[receiver.node].span,
                    arg_ty.ty,
                    expected_span,
                );
                self.add_mut_be_at_least_constraint(
                    receiver.mut_ty,
                    env.ir_arena[receiver.node].span,
                    arg_ty.mut_ty,
                    expected_span,
                );
                receiver.node
            } else {
                self.check_expr(env, *arg, arg_ty.ty, arg_ty.mut_ty, expected_span)?
            };
            let ty = env.ir_arena[node_id].ty;
            effects.push(env.ir_arena[node_id].effects.clone());
            node_ids.push(node_id);
            if ty == Type::never() {
                diverges = true;
                break;
            }
        }
        let combined_effects = self.make_dependent_effect(&effects);
        Ok((node_ids, combined_effects, diverges))
    }

    fn abstract_yielded_subscript_type(
        &mut self,
        env: &TypingEnv,
        mode: SubscriptMemberKind,
        args: &[DExprId],
        member_effects: EffType,
        receiver_mut_ty: Option<MutType>,
    ) -> SubscriptType {
        let member =
            SubscriptMemberType::new(member_effects, SubscriptResultConvention::YieldedOnce);
        let (ref_member, mut_member) = match mode {
            SubscriptMemberKind::Ref => (Some(member), None),
            SubscriptMemberKind::Mut => (None, Some(member)),
        };
        SubscriptType::new(
            args.iter()
                .enumerate()
                .map(|(index, arg)| {
                    if index == 0
                        && let Some(mut_ty) = receiver_mut_ty
                    {
                        FnArgType::new(self.fresh_type_var_ty(), mut_ty)
                    } else {
                        FnArgType::new(
                            self.fresh_type_var_ty(),
                            self.abstract_subscript_arg_mut_ty(env, *arg),
                        )
                    }
                })
                .collect(),
            self.fresh_type_var_ty(),
            ref_member,
            mut_member,
        )
    }

    fn abstract_subscript_arg_mut_ty(&mut self, env: &TypingEnv, arg: DExprId) -> MutType {
        // Phase 2: allow possibly-mutable bindings here by threading their mutability
        // variable into the inferred `SubscriptType` argument mode. That requires
        // preventing ordinary value-expression checking from prematurely solving the
        // same variable to constant; a shared call/subscript argument-passing helper is
        // the right place for that broader fix.
        if let ExprKind::Identifier(path) = &env.ast_arena[arg].kind
            && let [(name, _)] = &path.segments[..]
            && let Some(local_id) = env.get_variable_id(name)
        {
            let local_mut_ty = env.all_locals[local_id.as_index()].mut_ty;
            if local_mut_ty.is_mutable() {
                return MutType::mutable();
            }
        }
        self.fresh_mut_var_ty()
    }

    fn alloc_diverging_prefix_node(
        &mut self,
        env: &mut TypingEnv,
        nodes: Vec<NodeId>,
        effects: EffType,
        span: Location,
    ) -> NodeId {
        env.ir_arena.alloc(hir::Node::new(
            Self::block(nodes, Vec::new()),
            Type::never(),
            effects,
            span,
        ))
    }

    fn push_yielded_binding(
        &mut self,
        env: &mut TypingEnv,
        ty: Type,
        span: Location,
    ) -> (usize, LocalDeclId) {
        let env_size = env.cur_locals.len();
        let mut local =
            LocalDecl::new((ustr("$yielded"), span), MutType::mutable(), ty, None, span);
        local.set_non_owning_storage();
        let id = env.push_local(local);
        (env_size, id)
    }

    fn yielded_binding_load(
        &mut self,
        env: &mut TypingEnv,
        binding: LocalDeclId,
        ty: Type,
        span: Location,
    ) -> NodeId {
        env.ir_arena.alloc(hir::Node::new(
            NodeKind::LoadLocal(hir::LoadLocal { id: binding }),
            ty,
            no_effects(),
            span,
        ))
    }

    fn close_yielded_binding_scope(env: &mut TypingEnv, env_size: usize, span: Location) {
        Self::extend_local_scopes_to_span_end(env, env_size, span);
        env.cur_locals.truncate(env_size);
    }

    fn infer_named_subscript_with_yielded_body_with_receiver(
        &mut self,
        env: &mut TypingEnv,
        data: &ast::NamedSubscriptData<Desugared>,
        mode: SubscriptMemberKind,
        expr_span: Location,
        receiver_override: Option<NamedSubscriptReceiverOverride>,
        build_body: WithYieldedBodyBuilder<'_>,
    ) -> Result<(NodeId, MutType), InternalCompilationError> {
        let accessor = match self.infer_named_subscript_accessor_call(
            env,
            data,
            mode,
            expr_span,
            receiver_override,
        )? {
            PreparedNamedSubscriptAccessor::Ready(call) => call,
            PreparedNamedSubscriptAccessor::DivergedBeforeYield(node) => {
                return Ok((node, MutType::constant()));
            }
        };
        self.infer_prepared_accessor_with_body(env, accessor, mode, expr_span, build_body)
    }

    fn infer_prepared_accessor_with_body(
        &mut self,
        env: &mut TypingEnv,
        accessor: NamedSubscriptCall,
        mode: SubscriptMemberKind,
        expr_span: Location,
        build_body: WithYieldedBodyBuilder<'_>,
    ) -> Result<(NodeId, MutType), InternalCompilationError> {
        if accessor.provenance == YieldProvenance::AddressorPlace {
            let (env_size, binding) = self.push_yielded_binding(env, accessor.ty, expr_span);
            let place = self.yielded_binding_load(env, binding, accessor.ty, expr_span);
            let (body, result_ty) = build_body(self, env, place, accessor.ty)?;
            let body_effects = env.ir_arena[body].effects.clone();
            let effects = self.make_dependent_effect([&accessor.effects, &body_effects]);
            let result_mut = if matches!(mode, SubscriptMemberKind::Mut)
                && node_is_place_reference(env.ir_arena, body)
            {
                MutType::mutable()
            } else {
                MutType::constant()
            };
            Self::close_yielded_binding_scope(env, env_size, expr_span);
            let node = NodeKind::WithPlace(hir::WithPlace {
                place: accessor.node,
                binding,
                body,
            });
            let node = env
                .ir_arena
                .alloc(hir::Node::new(node, result_ty, effects, expr_span));
            return Ok((node, result_mut));
        }
        let (env_size, binding) = self.push_yielded_binding(env, accessor.ty, expr_span);
        let place = self.yielded_binding_load(env, binding, accessor.ty, expr_span);
        let (body, result_ty) = build_body(self, env, place, accessor.ty)?;
        let body_effects = env.ir_arena[body].effects.clone();
        let effects = self.make_dependent_effect([&accessor.effects, &body_effects]);
        Self::close_yielded_binding_scope(env, env_size, expr_span);
        let node = NodeKind::WithYielded(hir::WithYielded {
            accessor: accessor.node,
            binding,
            body,
        });
        let node = env
            .ir_arena
            .alloc(hir::Node::new(node, result_ty, effects, expr_span));
        Ok((node, MutType::constant()))
    }

    /// Record one driven argument whose outermost accessor is suspended around the call.
    /// Called once per driver after its node is built; materialized sub-expression accessors must
    /// not call this.
    fn record_driven_suspended_accessor(
        &mut self,
        is_mut: bool,
        span: Location,
    ) -> Result<(), InternalCompilationError> {
        let Some(state) = self.call_arg_suspension.as_mut() else {
            return Ok(());
        };
        if state.suspended >= 1 && (state.saw_mut || is_mut) {
            return Err(internal_compilation_error!(UnsupportedSubscriptFeature {
                kind: UnsupportedSubscriptFeatureKind::MultipleMutableSubscriptArguments,
                span,
            }));
        }
        state.suspended += 1;
        state.saw_mut |= is_mut;
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_projection_subscript_with_yielded_body(
        &mut self,
        env: &mut TypingEnv,
        subscript_id: SubscriptId,
        field: UstrSpan,
        mode: SubscriptMemberKind,
        expr_span: Location,
        receiver: NamedSubscriptReceiverOverride,
        build_body: WithYieldedBodyBuilder<'_>,
    ) -> Result<(NodeId, MutType), InternalCompilationError> {
        let accessor = match self.infer_projection_subscript_accessor_call(
            env,
            subscript_id,
            field,
            mode,
            expr_span,
            receiver,
        )? {
            PreparedNamedSubscriptAccessor::Ready(call) => call,
            PreparedNamedSubscriptAccessor::DivergedBeforeYield(node) => {
                return Ok((node, MutType::constant()));
            }
        };
        self.infer_prepared_accessor_with_body(env, accessor, mode, expr_span, build_body)
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_field_from_record_node(
        &mut self,
        env: &mut TypingEnv,
        record_node_id: NodeId,
        record_node_ty: Type,
        record_mut: MutType,
        mode: SubscriptMemberKind,
        base_span: Location,
        name: UstrSpan,
        expr_span: Location,
    ) -> Result<(NodeId, Type, MutType, bool), InternalCompilationError> {
        let effects = env.ir_arena[record_node_id].effects.clone();
        if record_node_ty == Type::never() {
            let node =
                self.alloc_diverging_prefix_node(env, vec![record_node_id], effects, expr_span);
            return Ok((node, Type::never(), MutType::constant(), false));
        }

        let (field, field_span) = name;
        let field_receiver_ty = {
            let record_data = record_node_ty.data();
            match &*record_data {
                TypeKind::Variable(_) | TypeKind::Record(_) => record_node_ty,
                TypeKind::Named(named) => {
                    let named = named.clone();
                    drop(record_data);
                    if named.def.module != env.current_module_id()
                        && env.module_env.type_def(named.def).has_private_repr()
                    {
                        return Err(internal_compilation_error!(PrivateReprAccess {
                            type_def: named.def,
                            access_span: field_span,
                        }));
                    }
                    env.module_env
                        .type_def(named.def)
                        .instantiated_shape_with_effects(&named.params, &named.effect_params)
                }
                _ => {
                    drop(record_data);
                    let structural_ty = self.fresh_type_var_ty();
                    self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                        repr_trait_id(env),
                        vec![record_node_ty],
                        vec![structural_ty],
                        vec![],
                        field_span,
                    ));
                    structural_ty
                }
            }
        };
        let element_ty = self.fresh_type_var_ty();
        let uses_projection_evidence = matches!(&*field_receiver_ty.data(), TypeKind::Variable(_));
        let mut projection_effects = None;
        if uses_projection_evidence {
            let member_effects = self.fresh_effect_var_ty();
            projection_effects = Some(member_effects.clone());
            let member = SubscriptMemberType::new(
                member_effects.clone(),
                SubscriptResultConvention::YieldedOnce,
            );
            let (ref_member, mut_member) = match mode {
                SubscriptMemberKind::Ref => (Some(member), None),
                SubscriptMemberKind::Mut => (None, Some(member)),
            };
            let subscript_ty = SubscriptType::new(
                vec![FnArgType::new_by_val(field_receiver_ty)],
                element_ty,
                ref_member,
                mut_member,
            );
            self.add_pub_constraint(PubTypeConstraint::new_projection_subscript_is(
                ProjectionRequirementKind::All,
                base_span,
                field,
                field_span,
                subscript_ty,
            ));
        } else {
            self.add_pub_constraint(PubTypeConstraint::new_structural_projection_subscript_is(
                field_receiver_ty,
                base_span,
                field,
                field_span,
                element_ty,
            ));
        }
        let effects = projection_effects
            .as_ref()
            .map(|projection_effects| self.make_dependent_effect([&effects, projection_effects]))
            .unwrap_or(effects);
        let node = env.ir_arena.alloc(hir::Node::new(
            NodeKind::FieldAccess(HirFieldAccess::new(record_node_id, field, mode)),
            element_ty,
            effects,
            expr_span,
        ));
        Ok((node, element_ty, record_mut, uses_projection_evidence))
    }

    fn infer_project_from_tuple_node(
        &mut self,
        env: &mut TypingEnv,
        tuple_node_id: NodeId,
        tuple_mut: MutType,
        base_span: Location,
        index: (usize, Location),
        expr_span: Location,
    ) -> Result<(NodeId, Type, MutType), InternalCompilationError> {
        let effects = env.ir_arena[tuple_node_id].effects.clone();
        let tuple_node_ty = env.ir_arena[tuple_node_id].ty;
        if tuple_node_ty == Type::never() {
            let node =
                self.alloc_diverging_prefix_node(env, vec![tuple_node_id], effects, expr_span);
            return Ok((node, Type::never(), MutType::constant()));
        }

        let tuple_ty = self.fresh_type_var_ty();
        let (index, index_span) = index;
        self.add_pub_constraint(PubTypeConstraint::new_have_trait(
            repr_trait_id(env),
            vec![tuple_node_ty],
            vec![tuple_ty],
            vec![],
            index_span,
        ));
        let element_ty = self.fresh_type_var_ty();
        self.add_pub_constraint(PubTypeConstraint::new_tuple_at_index_is(
            tuple_ty, base_span, index, index_span, element_ty,
        ));
        let node = env.ir_arena.alloc(hir::Node::new(
            NodeKind::Project(HirProject::new(
                tuple_node_id,
                ProjectionIndex::from_index(index),
            )),
            element_ty,
            effects,
            expr_span,
        ));
        Ok((node, element_ty, tuple_mut))
    }

    fn infer_access_chain_with_body(
        &mut self,
        env: &mut TypingEnv,
        place: AccessChain,
        mode: SubscriptMemberKind,
        expr_span: Location,
        build_body: impl FnOnce(
            &mut Self,
            &mut TypingEnv,
            NodeId,
            Type,
        ) -> Result<(NodeId, Type), InternalCompilationError>,
    ) -> Result<(NodeId, MutType), InternalCompilationError> {
        let (root_node, root_mut) = self.infer_expr(env, place.root)?;
        let root_ty = env.ir_arena[root_node].ty;
        self.infer_access_chain_steps_with_body(
            env,
            &place.steps,
            0,
            root_node,
            root_ty,
            root_mut,
            mode,
            expr_span,
            Box::new(build_body),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_access_chain_steps_with_body<'a>(
        &mut self,
        env: &mut TypingEnv,
        steps: &'a [AccessChainStep],
        step_index: usize,
        place_node: NodeId,
        place_ty: Type,
        place_mut: MutType,
        mode: SubscriptMemberKind,
        expr_span: Location,
        build_body: WithYieldedBodyBuilder<'a>,
    ) -> Result<(NodeId, MutType), InternalCompilationError> {
        if step_index == steps.len() {
            if matches!(mode, SubscriptMemberKind::Mut) {
                self.add_mut_be_at_least_constraint(
                    place_mut,
                    env.ir_arena[place_node].span,
                    MutType::mutable(),
                    expr_span,
                );
            }
            let (node, _ty) = build_body(self, env, place_node, place_ty)?;
            let mut_ty = if node == place_node {
                place_mut
            } else {
                MutType::constant()
            };
            return Ok((node, mut_ty));
        }

        match &steps[step_index] {
            AccessChainStep::Field {
                name,
                base_span,
                expr_span: step_span,
            } => {
                if let Some(subscript_id) =
                    self.explicit_projection_subscript(env, place_ty, name.0)
                {
                    return self.infer_projection_subscript_with_yielded_body(
                        env,
                        subscript_id,
                        *name,
                        mode,
                        expr_span,
                        NamedSubscriptReceiverOverride {
                            node: place_node,
                            ty: place_ty,
                            mut_ty: place_mut,
                        },
                        Box::new(move |this, env, place, place_ty| {
                            let (node, _) = this.infer_access_chain_steps_with_body(
                                env,
                                steps,
                                step_index + 1,
                                place,
                                place_ty,
                                MutType::mutable(),
                                mode,
                                expr_span,
                                build_body,
                            )?;
                            Ok((node, env.ir_arena[node].ty))
                        }),
                    );
                }
                let (next_node, next_ty, next_mut, uses_projection_evidence) = self
                    .infer_field_from_record_node(
                        env, place_node, place_ty, place_mut, mode, *base_span, *name, *step_span,
                    )?;
                if uses_projection_evidence {
                    return self.infer_prepared_accessor_with_body(
                        env,
                        NamedSubscriptCall {
                            node: next_node,
                            ty: next_ty,
                            effects: env.ir_arena[next_node].effects.clone(),
                            provenance: YieldProvenance::YieldedOnce,
                        },
                        mode,
                        expr_span,
                        Box::new(move |this, env, place, place_ty| {
                            let (node, _) = this.infer_access_chain_steps_with_body(
                                env,
                                steps,
                                step_index + 1,
                                place,
                                place_ty,
                                MutType::mutable(),
                                mode,
                                expr_span,
                                build_body,
                            )?;
                            Ok((node, env.ir_arena[node].ty))
                        }),
                    );
                }
                self.infer_access_chain_steps_with_body(
                    env,
                    steps,
                    step_index + 1,
                    next_node,
                    next_ty,
                    next_mut,
                    mode,
                    expr_span,
                    build_body,
                )
            }
            AccessChainStep::Index {
                index,
                array_span,
                expr_span: step_span,
            } => {
                let (next_node, next_ty, next_mut) = self.infer_index_from_array_node(
                    env,
                    place_node,
                    place_mut,
                    *array_span,
                    *index,
                    *step_span,
                )?;
                self.infer_access_chain_steps_with_body(
                    env,
                    steps,
                    step_index + 1,
                    next_node,
                    next_ty,
                    next_mut,
                    mode,
                    expr_span,
                    build_body,
                )
            }
            AccessChainStep::Project {
                index,
                base_span,
                expr_span: step_span,
            } => {
                let (next_node, next_ty, next_mut) = self.infer_project_from_tuple_node(
                    env, place_node, place_mut, *base_span, *index, *step_span,
                )?;
                self.infer_access_chain_steps_with_body(
                    env,
                    steps,
                    step_index + 1,
                    next_node,
                    next_ty,
                    next_mut,
                    mode,
                    expr_span,
                    build_body,
                )
            }
            AccessChainStep::NamedSubscript { data } => self
                .infer_named_subscript_with_yielded_body_with_receiver(
                    env,
                    data,
                    mode,
                    expr_span,
                    Some(NamedSubscriptReceiverOverride {
                        node: place_node,
                        ty: place_ty,
                        mut_ty: place_mut,
                    }),
                    Box::new(move |this, env, place, place_ty| {
                        let (node, _) = this.infer_access_chain_steps_with_body(
                            env,
                            steps,
                            step_index + 1,
                            place,
                            place_ty,
                            // The accessor member selection above has already enforced `mode`.
                            // The internal binding must be mutable so subsequent direct
                            // field/index/project steps can describe the consumer's final place.
                            MutType::mutable(),
                            mode,
                            expr_span,
                            build_body,
                        )?;
                        Ok((node, env.ir_arena[node].ty))
                    }),
                ),
        }
    }

    fn infer_access_chain_read(
        &mut self,
        env: &mut TypingEnv,
        place: AccessChain,
        expr_span: Location,
    ) -> Result<(NodeId, MutType), InternalCompilationError> {
        self.infer_access_chain_with_body(
            env,
            place,
            SubscriptMemberKind::Ref,
            expr_span,
            |this, env, place, place_ty| {
                Ok((
                    this.materialize_owned_value(env, place, expr_span),
                    place_ty,
                ))
            },
        )
    }

    fn infer_access_chain_assign(
        &mut self,
        env: &mut TypingEnv,
        place: AccessChain,
        sign_span: Location,
        value: DExprId,
        expr_span: Location,
    ) -> Result<(NodeId, MutType), InternalCompilationError> {
        self.infer_access_chain_with_body(
            env,
            place,
            SubscriptMemberKind::Mut,
            expr_span,
            |this, env, place, place_ty| {
                Ok((
                    this.infer_assign_to_place(env, place, place_ty, value, sign_span, expr_span)?,
                    Type::unit(),
                ))
            },
        )
    }

    fn infer_access_chain_assign_op(
        &mut self,
        env: &mut TypingEnv,
        place: AccessChain,
        sign_span: Location,
        op_path: &ast::Path,
        value: DExprId,
        expr_span: Location,
    ) -> Result<(NodeId, MutType), InternalCompilationError> {
        self.infer_access_chain_with_body(
            env,
            place,
            SubscriptMemberKind::Mut,
            expr_span,
            |this, env, place, place_ty| {
                let value = this.infer_static_apply_with_lhs_place(
                    env, place, place_ty, op_path, sign_span, value, expr_span,
                )?;
                Ok((
                    this.assign_value_node_to_place(env, place, place_ty, value, expr_span),
                    Type::unit(),
                ))
            },
        )
    }

    fn infer_assign_to_place(
        &mut self,
        env: &mut TypingEnv,
        place: NodeId,
        place_ty: Type,
        value: DExprId,
        sign_span: Location,
        expr_span: Location,
    ) -> Result<NodeId, InternalCompilationError> {
        let value_id = self.infer_expr_drop_mut(env, value)?;
        self.add_sub_type_constraint(
            env.ir_arena[value_id].ty,
            env.ir_arena[value_id].span,
            place_ty,
            sign_span,
        );
        Ok(self.assign_value_node_to_place(env, place, place_ty, value_id, expr_span))
    }

    fn assign_value_node_to_place(
        &mut self,
        env: &mut TypingEnv,
        place: NodeId,
        place_ty: Type,
        value: NodeId,
        expr_span: Location,
    ) -> NodeId {
        let value_ty = env.ir_arena[value].ty;
        if value_ty == Type::never() {
            return value;
        }
        let value = self.materialize_owned_value(env, value, expr_span);
        let value_effects = env.ir_arena[value].effects.clone();
        let place_effects = env.ir_arena[place].effects.clone();
        let effects = self.make_dependent_effect([&value_effects, &place_effects]);
        if self.type_needs_semantic_drop(env, place_ty, expr_span) && !place_ty.is_function() {
            self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                value_trait_id(env),
                vec![place_ty],
                vec![],
                vec![],
                expr_span,
            ));
        }
        env.ir_arena.alloc(hir::Node::new(
            NodeKind::Assign(hir::Assignment {
                place,
                value,
                drop: Some(PendingLocalDrop::Unknown),
            }),
            Type::unit(),
            effects,
            expr_span,
        ))
    }

    fn prepare_static_call_target(
        &mut self,
        env: &mut TypingEnv,
        path: &ast::Path,
        path_span: Location,
        arg_count: usize,
        got_span: Location,
        arguments_unnamed: UnnamedArg,
    ) -> Result<Option<PreparedStaticCallTarget>, InternalCompilationError> {
        if let Some((definition, function, _module_id, runtime_arg_passing)) = env
            .get_function(path)?
            .map(|(definition, function, module_id, runtime_arg_passing)| {
                (definition.clone(), function, module_id, runtime_arg_passing)
            })
        {
            if definition.ty_scheme.ty.args.len() != arg_count {
                return Err(internal_compilation_error!(WrongNumberOfArguments {
                    expected: definition.ty_scheme.ty.args.len(),
                    expected_span: path_span,
                    got: arg_count,
                    got_span,
                }));
            }

            let (inst_fn_ty, inst_data, _subst) = definition.ty_scheme.instantiate_with_fresh_vars(
                self,
                path_span,
                None,
                env.module_env,
            );
            let visible_arg_passing = visible_arg_passing_from_runtime(
                runtime_arg_passing.as_deref(),
                &inst_data,
                arg_count,
            )
            .map(<[_]>::to_vec);
            let result_mut_ty = if definition.result_convention.returns_place() {
                MutType::mutable()
            } else {
                MutType::constant()
            };
            return Ok(Some(PreparedStaticCallTarget {
                callee: CheckedStaticCallee::Function {
                    function,
                    function_path: Some(path.clone()),
                    function_span: path_span,
                    argument_names: arguments_unnamed.filter_args(&definition.arg_names),
                },
                abi_arg_tys: definition.ty_scheme.ty.args.clone(),
                inst_fn_ty,
                result_convention: definition.result_convention,
                inst_data,
                visible_arg_passing,
                result_mut_ty,
                have_trait_constraint: None,
            }));
        }

        if let Some((_module_name, trait_descr)) = env.module_env.get_trait_method(path)? {
            let (trait_id, method_index, definition) = trait_descr;
            let trait_def = env.module_env.trait_def(trait_id);
            if is_compiler_callable_only_method(trait_id, trait_def, method_index) {
                return Err(compiler_only_trait_method_use_error(
                    trait_id,
                    trait_def,
                    method_index,
                    path_span,
                ));
            }
            if definition.ty_scheme.ty.args.len() != arg_count {
                return Err(internal_compilation_error!(WrongNumberOfArguments {
                    expected: definition.ty_scheme.ty.args.len(),
                    expected_span: path_span,
                    got: arg_count,
                    got_span,
                }));
            }

            let trait_ty_var_count = trait_def.type_var_count();
            let trait_input_type_count = trait_def.input_type_count();
            let trait_eff_var_count = trait_def.output_effect_count();
            let (inst_fn_ty, inst_data, subst) = definition.ty_scheme.instantiate_with_fresh_vars(
                self,
                path_span,
                Some((trait_ty_var_count, trait_eff_var_count)),
                env.module_env,
            );
            assert!(
                inst_data.dicts_req.is_empty(),
                "Instantiation data for trait method is not supported yet."
            );

            let mut mapper = BitmapInstantiationMapper::new(&subst);
            for constraint in &trait_def.constraints {
                let mut constraint = constraint.map(&mut mapper);
                constraint.instantiate_location(path_span);
                self.add_pub_constraint(constraint);
            }

            let output_effs = (0..trait_eff_var_count)
                .map(|i| subst.1.get(&EffectVar::new(i)).cloned().unwrap())
                .collect::<Vec<_>>();
            let mut trait_tys = continuous_hashmap_to_vec(subst.0).unwrap();
            assert_eq!(trait_tys.len(), trait_ty_var_count as usize);
            let output_tys = trait_tys.split_off(trait_input_type_count as usize);
            let input_tys = trait_tys;
            let have_trait_constraint = PubTypeConstraint::new_have_trait(
                trait_id,
                input_tys.clone(),
                output_tys,
                output_effs,
                path_span,
            );

            return Ok(Some(PreparedStaticCallTarget {
                callee: CheckedStaticCallee::TraitMethod {
                    trait_id,
                    method_index,
                    method_path: path.clone(),
                    method_span: path_span,
                    arguments_unnamed,
                    input_tys,
                },
                abi_arg_tys: inst_fn_ty.args.clone(),
                inst_fn_ty,
                result_convention: definition.result_convention,
                inst_data,
                visible_arg_passing: None,
                result_mut_ty: if definition.result_convention.returns_place() {
                    MutType::mutable()
                } else {
                    MutType::constant()
                },
                have_trait_constraint: Some(have_trait_constraint),
            }));
        }

        Ok(None)
    }

    fn build_static_call_from_checked_args(
        &mut self,
        env: &mut TypingEnv,
        mut call: StaticCallFromCheckedArgs,
        expr_span: Location,
    ) -> BuiltStaticCall {
        let args_effects = self.make_dependent_effect(
            call.args_node_ids
                .iter()
                .map(|node| env.ir_arena[*node].effects.clone())
                .collect::<Vec<_>>(),
        );
        if call
            .args_node_ids
            .iter()
            .any(|node| env.ir_arena[*node].ty == Type::never())
        {
            let nodes =
                self.value_evaluation_prefix_nodes_for_many(env.ir_arena, call.args_node_ids);
            let effects = self.make_dependent_effect([&args_effects, &call.inst_fn_ty.effects]);
            return BuiltStaticCall {
                node: self.diverging_prefix_node(env, nodes),
                ty: Type::never(),
                mut_ty: MutType::constant(),
                effects,
            };
        }

        let ret_ty = call.inst_fn_ty.ret;
        let effects = self.make_dependent_effect([&args_effects, &call.inst_fn_ty.effects]);
        let temp_start_index = env.cur_locals.len();
        let prepared_arguments = self.prepare_call_arguments(
            env,
            &mut call.args_node_ids,
            &call.inst_fn_ty.args,
            &call.abi_arg_tys,
            expr_span,
            call.visible_arg_passing.as_deref(),
        );
        let node = match call.callee {
            CheckedStaticCallee::Function {
                function,
                function_path,
                function_span,
                argument_names,
            } => NodeKind::StaticApply(b(hir::StaticApplication {
                function,
                function_path,
                function_span,
                extra_arguments: Vec::new(),
                arguments: prepared_arguments.arguments,
                argument_names,
                ty: CallImplType::new(call.inst_fn_ty, call.result_convention),
                inst_data: call.inst_data,
            })),
            CheckedStaticCallee::TraitMethod {
                trait_id,
                method_index,
                method_path,
                method_span,
                arguments_unnamed,
                input_tys,
            } => NodeKind::TraitMethodApply(b(hir::TraitMethodApplication {
                trait_id,
                method_index,
                method_path,
                method_span,
                arguments: prepared_arguments.arguments,
                arguments_unnamed,
                ty: CallImplType::new(call.inst_fn_ty, call.result_convention),
                input_tys,
                inst_data: call.inst_data,
            })),
        };
        let call_node = hir::Node::new(node, ret_ty, effects.clone(), expr_span);
        let node = self.wrap_call_with_temp_drops(
            env,
            temp_start_index,
            prepared_arguments.temp_stores,
            call_node,
        );
        BuiltStaticCall {
            node,
            ty: ret_ty,
            mut_ty: call.result_mut_ty,
            effects,
        }
    }

    fn driven_access_chain_static_call_args(
        &mut self,
        env: &mut TypingEnv,
        args: &[DExprId],
        target: &PreparedStaticCallTarget,
    ) -> Result<Vec<DrivenAccessChainArg>, InternalCompilationError> {
        let arg_passing = self.argument_passing_for_args(
            &target.inst_fn_ty.args,
            &target.abi_arg_tys,
            target.visible_arg_passing.as_deref(),
        );
        let mut found: Vec<DrivenAccessChainArg> = Vec::new();
        for (index, (arg, passing)) in args.iter().zip(arg_passing).enumerate() {
            if !Self::is_access_chain_expr(&env.ast_arena[*arg].kind) {
                continue;
            }
            let plan = self.access_chain_plan_for_expr(env, *arg);
            let needs_scoped_projection_driver =
                Self::access_chain_plan_may_need_projection_driver(&plan);
            let visible_runtime_shared_ref = target
                .visible_arg_passing
                .as_ref()
                .and_then(|passing| passing.get(index))
                .is_some_and(|passing| {
                    matches!(
                        passing,
                        ResolvedArgPassing::Value(ResolvedValueArgPassing::SharedRef)
                    )
                });
            let mode = match passing {
                PendingArgPassing::MutableRef => SubscriptMemberKind::Mut,
                PendingArgPassing::Value(PendingValueArgPassing::Resolved(
                    ResolvedValueArgPassing::SharedRef,
                )) => SubscriptMemberKind::Ref,
                PendingArgPassing::Value(PendingValueArgPassing::Unknown)
                    if needs_scoped_projection_driver =>
                {
                    if matches!(target.inst_fn_ty.args[index].mut_ty, MutType::Resolved(mut_val) if !mut_val.is_mutable())
                    {
                        SubscriptMemberKind::Ref
                    } else {
                        SubscriptMemberKind::Mut
                    }
                }
                PendingArgPassing::Value(PendingValueArgPassing::Unknown)
                    if visible_runtime_shared_ref =>
                {
                    SubscriptMemberKind::Ref
                }
                PendingArgPassing::Value(PendingValueArgPassing::Unknown)
                | PendingArgPassing::Value(PendingValueArgPassing::Resolved(
                    ResolvedValueArgPassing::TrivialCopy,
                )) => continue,
            };
            let place = plan.chain;
            if !needs_scoped_projection_driver
                && !Self::access_chain_root_is_stable_place(env, &place)
            {
                continue;
            }
            found.push(DrivenAccessChainArg {
                index,
                access_chain: place,
                mode,
            });
        }
        Ok(found)
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_static_apply_with_driven_access_chain_args(
        &mut self,
        env: &mut TypingEnv,
        target: PreparedStaticCallTarget,
        args: &[DExprId],
        drivers: Vec<DrivenAccessChainArg>,
        path_span: Location,
        expr_span: Location,
    ) -> Result<(NodeKind, Type, MutType, EffType), InternalCompilationError> {
        // Nested calls get their own tally; restore the enclosing call afterwards.
        let saved_suspension = self
            .call_arg_suspension
            .replace(CallArgSuspensionState::default());
        let result = self.infer_static_apply_with_driven_access_chain_args_at(
            env,
            target,
            args,
            &drivers,
            Vec::new(),
            path_span,
            expr_span,
        );
        self.call_arg_suspension = saved_suspension;
        let (node_id, mut_ty) = result?;
        let node = env.ir_arena[node_id].clone();
        Ok((node.kind, node.ty, mut_ty, node.effects))
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_static_apply_with_driven_access_chain_args_at(
        &mut self,
        env: &mut TypingEnv,
        target: PreparedStaticCallTarget,
        args: &[DExprId],
        drivers: &[DrivenAccessChainArg],
        prepared_drivers: Vec<PreparedDrivenArg>,
        path_span: Location,
        expr_span: Location,
    ) -> Result<(NodeId, MutType), InternalCompilationError> {
        let Some((driver, remaining_drivers)) = drivers.split_first() else {
            return self.infer_static_apply_with_prepared_driven_args(
                env,
                target,
                args,
                prepared_drivers,
                path_span,
                expr_span,
            );
        };
        let driver_index = driver.index;
        let driver_mode = driver.mode;
        let access_chain = driver.access_chain.clone();
        let arg_span = env.ast_arena[args[driver_index]].span;
        let (node, mut_ty) = self.infer_access_chain_with_body(
            env,
            access_chain,
            driver_mode,
            expr_span,
            Box::new(
                move |this: &mut TypeInference,
                      env: &mut TypingEnv,
                      place: NodeId,
                      place_ty: Type| {
                    let mut prepared_drivers = prepared_drivers;
                    prepared_drivers.push(PreparedDrivenArg {
                        index: driver_index,
                        node: place,
                        ty: place_ty,
                        mode: driver_mode,
                    });
                    let (node, _) = this.infer_static_apply_with_driven_access_chain_args_at(
                        env,
                        target,
                        args,
                        remaining_drivers,
                        prepared_drivers,
                        path_span,
                        expr_span,
                    )?;
                    Ok((node, env.ir_arena[node].ty))
                },
            ),
        )?;
        // Only an outer `WithYielded` leaves this driver suspended around the call. Yielded
        // accessors inside sub-expressions stay nested in `node` and finish before the call.
        if matches!(env.ir_arena[node].kind, NodeKind::WithYielded(_)) {
            self.record_driven_suspended_accessor(
                driver_mode == SubscriptMemberKind::Mut,
                arg_span,
            )?;
        }
        Ok((node, mut_ty))
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_static_apply_with_prepared_driven_args(
        &mut self,
        env: &mut TypingEnv,
        target: PreparedStaticCallTarget,
        args: &[DExprId],
        prepared_drivers: Vec<PreparedDrivenArg>,
        path_span: Location,
        expr_span: Location,
    ) -> Result<(NodeId, MutType), InternalCompilationError> {
        let mut args_node_ids = Vec::with_capacity(args.len());
        let mut effects = Vec::with_capacity(args.len());
        let mut diverges = false;
        for (index, (arg, arg_ty)) in args.iter().zip(&target.inst_fn_ty.args).enumerate() {
            let node_id = if let Some(prepared) = prepared_drivers
                .iter()
                .find(|prepared| prepared.index == index)
            {
                self.add_sub_type_constraint(prepared.ty, expr_span, arg_ty.ty, path_span);
                if prepared.mode == SubscriptMemberKind::Mut {
                    self.add_mut_be_at_least_constraint(
                        MutType::mutable(),
                        expr_span,
                        arg_ty.mut_ty,
                        path_span,
                    );
                }
                prepared.node
            } else {
                self.check_expr(env, *arg, arg_ty.ty, arg_ty.mut_ty, path_span)?
            };
            let ty = env.ir_arena[node_id].ty;
            effects.push(env.ir_arena[node_id].effects.clone());
            args_node_ids.push(node_id);
            if ty == Type::never() {
                diverges = true;
                break;
            }
        }

        let args_effects = self.make_dependent_effect(&effects);
        if diverges {
            let nodes = self.value_evaluation_prefix_nodes_for_many(env.ir_arena, args_node_ids);
            let node = self.alloc_diverging_prefix_node(env, nodes, args_effects, expr_span);
            return Ok((node, MutType::constant()));
        }

        if let Some(constraint) = target.have_trait_constraint {
            self.add_pub_constraint(constraint);
        }
        let call = self.build_static_call_from_checked_args(
            env,
            StaticCallFromCheckedArgs {
                callee: target.callee,
                abi_arg_tys: target.abi_arg_tys,
                inst_fn_ty: target.inst_fn_ty,
                result_convention: target.result_convention,
                inst_data: target.inst_data,
                args_node_ids,
                visible_arg_passing: target.visible_arg_passing,
                result_mut_ty: target.result_mut_ty,
            },
            expr_span,
        );
        let node = env
            .ir_arena
            .alloc(hir::Node::new(call.node, call.ty, call.effects, expr_span));
        Ok((node, call.mut_ty))
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_static_apply_with_lhs_place(
        &mut self,
        env: &mut TypingEnv,
        lhs_place: NodeId,
        lhs_ty: Type,
        path: &ast::Path,
        path_span: Location,
        rhs: DExprId,
        expr_span: Location,
    ) -> Result<NodeId, InternalCompilationError> {
        let Some(target) =
            self.prepare_static_call_target(env, path, path_span, 2, expr_span, UnnamedArg::All)?
        else {
            return Err(internal_compilation_error!(Unsupported {
                span: path_span,
                reason: format!("unknown compound-assignment operator `{path}`"),
            }));
        };
        let lhs_arg = target.inst_fn_ty.args[0];
        let rhs_arg = target.inst_fn_ty.args[1];
        let args_node_ids = vec![
            lhs_place,
            self.check_expr(env, rhs, rhs_arg.ty, rhs_arg.mut_ty, path_span)?,
        ];
        self.add_sub_type_constraint(lhs_ty, expr_span, lhs_arg.ty, path_span);
        self.add_mut_be_at_least_constraint(
            MutType::mutable(),
            expr_span,
            lhs_arg.mut_ty,
            path_span,
        );
        if let Some(constraint) = target.have_trait_constraint {
            self.add_pub_constraint(constraint);
        }
        let call = self.build_static_call_from_checked_args(
            env,
            StaticCallFromCheckedArgs {
                callee: target.callee,
                abi_arg_tys: target.abi_arg_tys,
                inst_fn_ty: target.inst_fn_ty,
                result_convention: target.result_convention,
                inst_data: target.inst_data,
                args_node_ids,
                visible_arg_passing: target.visible_arg_passing,
                result_mut_ty: MutType::constant(),
            },
            expr_span,
        );
        Ok(env
            .ir_arena
            .alloc(hir::Node::new(call.node, call.ty, call.effects, expr_span)))
    }

    fn store_owned_temp(
        &mut self,
        env: &mut TypingEnv,
        value: NodeId,
        ty: Type,
        span: Location,
        name: Ustr,
    ) -> (NodeId, NodeId) {
        let value_span = env.ir_arena[value].span;
        let mut local = LocalDecl::new(
            (name, Location::new_synthesized()),
            MutType::constant(),
            ty,
            None,
            span,
        );
        local.set_owned_storage(
            self.unresolved_or_skipped_drop_for_value(env, value, ty, false, span),
        );
        let id = env.push_local(local);

        let value_effects = env.ir_arena[value].effects.clone();
        let store = env.ir_arena.alloc(hir::Node::new(
            NodeKind::StoreLocal(hir::StoreLocal { value, id }),
            Type::unit(),
            value_effects,
            span,
        ));
        let load = env.ir_arena.alloc(hir::Node::new(
            NodeKind::LoadLocal(hir::LoadLocal { id }),
            ty,
            no_effects(),
            value_span,
        ));
        (store, load)
    }

    fn prepare_call_arguments(
        &mut self,
        env: &mut TypingEnv,
        args: &mut [NodeId],
        arg_tys: &[FnArgType],
        abi_arg_tys: &[FnArgType],
        span: Location,
        visible_arg_passing_override: Option<&[ResolvedArgPassing]>,
    ) -> PreparedCallArguments {
        let arg_passing =
            self.argument_passing_for_args(arg_tys, abi_arg_tys, visible_arg_passing_override);
        let mut stores = Vec::new();
        for ((arg, arg_ty), passing) in args.iter_mut().zip(arg_tys).zip(&arg_passing) {
            match passing {
                PendingArgPassing::MutableRef => {
                    if node_is_place_reference(env.ir_arena, *arg) {
                        let prepared = self.prepare_place_for_consumer(env, *arg, span);
                        stores.extend(prepared.prefix);
                        *arg = prepared.place;
                    }
                }
                PendingArgPassing::Value(_) => {
                    if Self::node_is_scoped_place_value(env.ir_arena, *arg) {
                        let prepared = self.prepare_scoped_place_value_for_consumer(env, *arg);
                        stores.extend(prepared.prefix);
                        *arg = prepared.place;
                    }
                    if node_is_place_reference(env.ir_arena, *arg)
                        && !node_is_stable_place_reference(env.ir_arena, *arg)
                    {
                        let prepared = self.prepare_place_for_consumer(env, *arg, span);
                        stores.extend(prepared.prefix);
                        *arg = prepared.place;
                    }
                    if self.call_value_argument_needs_shared_ref_temp(
                        env, *arg, arg_ty.ty, *passing, span,
                    ) {
                        let value = self.materialize_owned_value(env, *arg, span);
                        let value_ty = env.ir_arena[value].ty;
                        let (store, load) =
                            self.store_owned_temp(env, value, value_ty, span, ustr("$arg"));
                        stores.push(store);
                        *arg = load;
                    } else {
                        self.add_call_argument_temp_value_constraint(
                            env, *arg, arg_ty.ty, *passing, span,
                        );
                    }
                }
            }
        }
        let arguments = CallArgument::from_value_slice_and_passing(args, arg_passing);
        PreparedCallArguments {
            arguments,
            temp_stores: stores,
        }
    }

    fn argument_passing_for_args(
        &self,
        arg_tys: &[FnArgType],
        abi_arg_tys: &[FnArgType],
        visible_arg_passing_override: Option<&[ResolvedArgPassing]>,
    ) -> Vec<PendingArgPassing> {
        assert_eq!(arg_tys.len(), abi_arg_tys.len());
        if let Some(visible_arg_passing_override) = visible_arg_passing_override {
            assert_eq!(arg_tys.len(), visible_arg_passing_override.len());
            return visible_arg_passing_override
                .iter()
                .copied()
                .map(PendingArgPassing::from_resolved)
                .collect();
        }

        arg_tys
            .iter()
            .zip(abi_arg_tys)
            .map(|(arg_ty, abi_arg_ty)| {
                if abi_arg_ty
                    .mut_ty
                    .as_resolved()
                    .is_some_and(|mut_ty| mut_ty.is_mutable())
                {
                    PendingArgPassing::MutableRef
                } else if !abi_arg_ty.ty.is_constant() {
                    PendingArgPassing::Value(PendingValueArgPassing::Resolved(
                        ResolvedValueArgPassing::SharedRef,
                    ))
                } else {
                    unresolved_arg_passing_for_args(std::slice::from_ref(arg_ty))
                        .into_iter()
                        .next()
                        .unwrap()
                }
            })
            .collect()
    }

    fn call_value_argument_needs_shared_ref_temp(
        &mut self,
        env: &mut TypingEnv,
        arg: NodeId,
        ty: Type,
        passing: PendingArgPassing,
        span: Location,
    ) -> bool {
        let is_stable_place = node_is_stable_storage_place_reference(env.ir_arena, arg);
        if ty == Type::never() || is_stable_place {
            return false;
        }
        match passing {
            PendingArgPassing::MutableRef => false,
            PendingArgPassing::Value(PendingValueArgPassing::Resolved(
                ResolvedValueArgPassing::SharedRef,
            )) => true,
            PendingArgPassing::Value(PendingValueArgPassing::Resolved(
                ResolvedValueArgPassing::TrivialCopy,
            )) => false,
            PendingArgPassing::Value(PendingValueArgPassing::Unknown) => {
                !self.type_has_concrete_trivial_copy_impl(env, ty, span)
            }
        }
    }

    fn add_call_argument_temp_value_constraint(
        &mut self,
        env: &mut TypingEnv,
        arg: NodeId,
        ty: Type,
        passing: PendingArgPassing,
        span: Location,
    ) {
        // A non-place shared-ref argument may need owned temporary storage whose cleanup uses Value::drop.
        if matches!(passing, PendingArgPassing::Value(_))
            && !node_is_stable_place_reference(env.ir_arena, arg)
            && !self.type_has_concrete_trivial_copy_impl(env, ty, span)
            && !ty.is_function()
        {
            self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                value_trait_id(env),
                vec![ty],
                vec![],
                vec![],
                span,
            ));
        }
    }

    fn wrap_call_with_temp_drops(
        &mut self,
        env: &mut TypingEnv,
        temp_start_index: usize,
        mut prefix: Vec<NodeId>,
        call: hir::Node,
    ) -> NodeKind {
        if prefix.is_empty() {
            return call.kind;
        }

        let call = env.ir_arena.alloc(call);
        prefix.push(call);
        let drops = self.cleanup_locals_for_locals(env, temp_start_index);
        env.cur_locals.truncate(temp_start_index);
        self.block_or_cleanup_scope(prefix, drops)
    }

    fn wrap_unit_with_temp_drops(
        &mut self,
        env: &mut TypingEnv,
        temp_start_index: usize,
        mut prefix: Vec<NodeId>,
        node: hir::Node,
    ) -> NodeKind {
        if prefix.is_empty() {
            return node.kind;
        }

        let node = env.ir_arena.alloc(node);
        prefix.push(node);
        let drops = self.cleanup_locals_for_locals(env, temp_start_index);
        env.cur_locals.truncate(temp_start_index);
        self.block_or_cleanup_scope(prefix, drops)
    }

    /// Builds a consumer that reads `value` by shared reference. A non-place `value` needing a
    /// semantic drop is first bound to an owned `name` temporary dropped after the consumer (so it
    /// acquires a `Value` obligation, like a shared-ref call argument); a place or trivially-copyable
    /// `value` is consumed in place. `build_consumer` receives the node to consume — `value` or the
    /// `LoadLocal` of its temporary — and returns its `(kind, type, effects)`.
    pub(crate) fn consume_value_by_shared_ref(
        &mut self,
        env: &mut TypingEnv,
        value: NodeId,
        ty: Type,
        span: Location,
        name: Ustr,
        build_consumer: impl FnOnce(&mut Self, &mut TypingEnv, NodeId) -> (NodeKind, Type, EffType),
    ) -> (NodeKind, Type, EffType) {
        let is_stable_place = node_is_stable_storage_place_reference(env.ir_arena, value);
        if is_stable_place || !self.node_value_needs_semantic_drop(env, value, ty, span) {
            return build_consumer(self, env, value);
        }
        let temp_start = env.cur_locals.len();
        let (store, load) = self.store_owned_temp(env, value, ty, span, name);
        let (kind, consumer_ty, consumer_effects) = build_consumer(self, env, load);
        let consumer = hir::Node::new(kind, consumer_ty, consumer_effects.clone(), span);
        let block = self.wrap_call_with_temp_drops(env, temp_start, vec![store], consumer);
        (block, consumer_ty, consumer_effects)
    }

    #[allow(clippy::too_many_arguments)]
    fn wrap_owned_value_with_temp_drops(
        &mut self,
        env: &mut TypingEnv,
        temp_start_index: usize,
        mut prefix: Vec<NodeId>,
        value: NodeId,
        ty: Type,
        value_effects: EffType,
        span: Location,
    ) -> NodeId {
        if prefix.is_empty() {
            return value;
        }

        let mut effect_deps = prefix
            .iter()
            .map(|node| &env.ir_arena[*node].effects)
            .collect::<Vec<_>>();
        effect_deps.push(&value_effects);
        let effects = self.make_dependent_effect(effect_deps);

        let (store_result, result_load) =
            self.store_owned_temp(env, value, ty, span, ustr("$result"));
        let result_id = match &env.ir_arena[result_load].kind {
            NodeKind::LoadLocal(load) => load.id,
            _ => panic!("store_owned_temp should return a LoadLocal"),
        };
        let result_move = env.ir_arena.alloc(hir::Node::new(
            NodeKind::TakeLocalValue(hir::TakeLocalValue {
                id: result_id,
                mode: PendingTakeLocalValueMode::MoveOwned,
            }),
            ty,
            no_effects(),
            span,
        ));

        prefix.push(store_result);
        prefix.push(result_move);
        let drops = self.cleanup_locals_for_locals(env, temp_start_index);
        env.cur_locals.truncate(temp_start_index);
        let kind = self.block_or_cleanup_scope(prefix, drops);

        env.ir_arena.alloc(hir::Node::new(kind, ty, effects, span))
    }

    fn cleanup_locals_for_locals(
        &mut self,
        env: &mut TypingEnv,
        start_index: usize,
    ) -> Vec<LocalDeclId> {
        env.cur_locals
            .iter()
            .copied()
            .enumerate()
            .skip(start_index)
            .filter(|(_, local_id)| {
                let local = &env.all_locals[local_id.as_index()];
                local.may_own_storage()
            })
            .map(|(_, id)| id)
            .collect()
    }

    fn close_block_scope(
        &mut self,
        env: &mut TypingEnv,
        env_size: usize,
        nodes: Vec<NodeId>,
    ) -> NodeKind {
        let drops = self.cleanup_locals_for_locals(env, env_size);
        env.cur_locals.truncate(env_size);
        self.block_or_cleanup_scope(nodes, drops)
    }

    fn extend_local_scopes_to_span_end(env: &mut TypingEnv, start_index: usize, span: Location) {
        let local_ids = env
            .cur_locals
            .iter()
            .copied()
            .skip(start_index)
            .collect::<Vec<_>>();
        for local_id in local_ids {
            let local = &mut env.all_locals[local_id.as_index()];
            assert_eq!(local.scope.source_id(), span.source_id());
            assert!(local.scope.end() <= span.end());
            local.scope = Location::new(local.scope.start(), span.end(), local.scope.source_id());
        }
    }

    fn strip_effects_from_node(
        &mut self,
        env: &mut TypingEnv,
        node_id: NodeId,
        span: Location,
    ) -> NodeId {
        let kind = env.ir_arena[node_id].kind.clone();
        let ty = env.ir_arena[node_id].ty;
        env.ir_arena
            .alloc(hir::Node::new(kind, ty, no_effects(), span))
    }

    fn block_or_cleanup_scope(
        &mut self,
        nodes: Vec<NodeId>,
        cleanup: Vec<LocalDeclId>,
    ) -> NodeKind {
        Self::block(nodes, cleanup)
    }

    fn block(nodes: Vec<NodeId>, cleanup: Vec<LocalDeclId>) -> NodeKind {
        NodeKind::Block(b(hir::Block {
            body: b(SVec2::from_vec(nodes)),
            cleanup,
        }))
    }

    fn prepare_value_for_exit(
        &mut self,
        env: &mut TypingEnv,
        value: NodeId,
        exit_local_scope_start: usize,
        span: Location,
    ) -> NodeId {
        let (value, taken_local) =
            self.take_local_value_result(env, value, exit_local_scope_start, span);
        if taken_local.is_some() {
            value
        } else {
            self.materialize_owned_value(env, value, span)
        }
    }

    fn take_local_value_result(
        &mut self,
        env: &mut TypingEnv,
        value: NodeId,
        min_local_decl_index: usize,
        span: Location,
    ) -> (NodeId, Option<LocalDeclId>) {
        let id = match &env.ir_arena[value].kind {
            NodeKind::LoadLocal(load) => load.id,
            _ => return (value, None),
        };
        if id.as_index() < min_local_decl_index {
            return (value, None);
        }
        let local = &env.all_locals[id.as_index()];
        if !local.owns_storage() && !local.may_own_storage() {
            return (value, None);
        }
        let ty = env.ir_arena[value].ty;
        let effects = env.ir_arena[value].effects.clone();
        let mode = if local.owns_storage() {
            PendingTakeLocalValueMode::MoveOwned
        } else {
            PendingTakeLocalValueMode::Unknown
        };
        let take_node = env.ir_arena.alloc(hir::Node::new(
            NodeKind::TakeLocalValue(hir::TakeLocalValue { id, mode }),
            ty,
            effects,
            span,
        ));
        (take_node, Some(id))
    }

    pub(crate) fn materialize_owned_value(
        &mut self,
        env: &mut TypingEnv,
        value: NodeId,
        span: Location,
    ) -> NodeId {
        if let NodeKind::WithYielded(mut node) = env.ir_arena[value].kind.clone()
            && node_is_place_reference(env.ir_arena, node.body)
        {
            node.body = self.materialize_owned_value(env, node.body, span);
            let ty = env.ir_arena[value].ty;
            let accessor_effects = env.ir_arena[node.accessor].effects.clone();
            let body_effects = env.ir_arena[node.body].effects.clone();
            let effects = self.make_dependent_effect([&accessor_effects, &body_effects]);
            return env.ir_arena.alloc(hir::Node::new(
                NodeKind::WithYielded(node),
                ty,
                effects,
                span,
            ));
        }

        if !node_is_place_reference(env.ir_arena, value) {
            return value;
        }

        if place_resolution_may_create_temp(env.ir_arena, value) {
            let temp_start_index = env.cur_locals.len();
            let prepared = self.prepare_place_for_consumer(env, value, span);
            let value = self.materialize_owned_stable_place(env, prepared.place, span);
            let ty = env.ir_arena[value].ty;
            let effects = env.ir_arena[value].effects.clone();
            return self.wrap_owned_value_with_temp_drops(
                env,
                temp_start_index,
                prepared.prefix,
                value,
                ty,
                effects,
                span,
            );
        }

        self.materialize_owned_stable_place(env, value, span)
    }

    fn node_is_scoped_place_value(arena: &NodeArena, node_id: NodeId) -> bool {
        match &arena[node_id].kind {
            NodeKind::WithYielded(node) => node_is_place_reference(arena, node.body),
            NodeKind::Block(block) => block
                .tail_node()
                .is_some_and(|node| Self::node_is_scoped_place_value(arena, node)),
            _ => false,
        }
    }

    fn materialize_owned_stable_place(
        &mut self,
        env: &mut TypingEnv,
        value: NodeId,
        span: Location,
    ) -> NodeId {
        let ty = env.ir_arena[value].ty;
        if !ty.is_function() {
            self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                value_trait_id(env),
                vec![ty],
                vec![],
                vec![],
                span,
            ));
        }
        let effects = env.ir_arena[value].effects.clone();
        env.ir_arena.alloc(hir::Node::new(
            NodeKind::CloneValue(hir::CloneValue {
                source: value,
                clone: PendingLocalClone::Unknown,
            }),
            ty,
            effects,
            span,
        ))
    }

    fn prepare_scoped_place_value_for_consumer(
        &mut self,
        env: &mut TypingEnv,
        place: NodeId,
    ) -> PreparedPlace {
        match &env.ir_arena[place].kind {
            NodeKind::Block(block)
                if block
                    .tail_node()
                    .is_some_and(|tail| Self::node_is_scoped_place_value(env.ir_arena, tail)) =>
            {
                let tail = block.tail_node().expect("checked above");
                let mut prefix = block.body.iter().copied().collect::<Vec<_>>();
                assert_eq!(prefix.pop(), Some(tail));
                for local in block.cleanup.iter().copied() {
                    if !env.cur_locals.contains(&local) {
                        env.cur_locals.push(local);
                    }
                }
                PreparedPlace {
                    prefix,
                    place: tail,
                }
            }
            _ => PreparedPlace {
                prefix: Vec::new(),
                place,
            },
        }
    }

    fn prepare_place_for_consumer(
        &mut self,
        env: &mut TypingEnv,
        place: NodeId,
        span: Location,
    ) -> PreparedPlace {
        match env.ir_arena[place].kind.clone() {
            NodeKind::Project(project) => {
                self.prepare_projection_place(env, place, project.value, span, |value| {
                    NodeKind::Project(HirProject::new(value, project.index))
                })
            }
            NodeKind::FieldAccess(field_access) => {
                self.prepare_projection_place(env, place, field_access.value, span, |value| {
                    NodeKind::FieldAccess(HirFieldAccess::new(
                        value,
                        field_access.field,
                        field_access.access_mode,
                    ))
                })
            }
            NodeKind::StaticApply(mut app) if app.ty.returns_place() => {
                if let Some(base_index) =
                    addressor_place_base_argument_index(env.ir_arena, &app.arguments)
                {
                    let mut prepared = self.prepare_place_base_for_projection(
                        env,
                        app.arguments[base_index].value,
                        span,
                    );
                    app.arguments[base_index].value = prepared.place;
                    prepared.place =
                        self.rebuild_place_node(env, place, NodeKind::StaticApply(app));
                    prepared
                } else {
                    PreparedPlace {
                        prefix: Vec::new(),
                        place,
                    }
                }
            }
            NodeKind::TraitMethodApply(mut app) if app.ty.returns_place() => {
                if let Some(base_index) =
                    addressor_place_base_argument_index(env.ir_arena, &app.arguments)
                {
                    let mut prepared = self.prepare_place_base_for_projection(
                        env,
                        app.arguments[base_index].value,
                        span,
                    );
                    app.arguments[base_index].value = prepared.place;
                    prepared.place =
                        self.rebuild_place_node(env, place, NodeKind::TraitMethodApply(app));
                    prepared
                } else {
                    PreparedPlace {
                        prefix: Vec::new(),
                        place,
                    }
                }
            }
            NodeKind::CallDictionaryMethod(mut call) if call.ty.returns_place() => {
                if let Some(base_index) =
                    addressor_place_base_argument_index(env.ir_arena, &call.arguments)
                {
                    let mut prepared = self.prepare_place_base_for_projection(
                        env,
                        call.arguments[base_index].value,
                        span,
                    );
                    call.arguments[base_index].value = prepared.place;
                    prepared.place =
                        self.rebuild_place_node(env, place, NodeKind::CallDictionaryMethod(call));
                    prepared
                } else {
                    PreparedPlace {
                        prefix: Vec::new(),
                        place,
                    }
                }
            }
            NodeKind::Apply(mut app) if app.ty.returns_place() => {
                if let Some(base_index) =
                    addressor_place_base_argument_index(env.ir_arena, &app.arguments)
                {
                    let mut prepared = self.prepare_place_base_for_projection(
                        env,
                        app.arguments[base_index].value,
                        span,
                    );
                    app.arguments[base_index].value = prepared.place;
                    prepared.place = self.rebuild_place_node(env, place, NodeKind::Apply(app));
                    prepared
                } else {
                    PreparedPlace {
                        prefix: Vec::new(),
                        place,
                    }
                }
            }
            NodeKind::Block(block)
                if block
                    .tail_node()
                    .is_some_and(|tail| node_is_place_reference(env.ir_arena, tail)) =>
            {
                let tail = block.tail_node().expect("checked above");
                let mut prefix = block.body.iter().copied().collect::<Vec<_>>();
                assert_eq!(prefix.pop(), Some(tail));
                for local in block.cleanup {
                    if !env.cur_locals.contains(&local) {
                        env.cur_locals.push(local);
                    }
                }
                PreparedPlace {
                    prefix,
                    place: tail,
                }
            }
            _ => PreparedPlace {
                prefix: Vec::new(),
                place,
            },
        }
    }

    fn prepare_projection_place(
        &mut self,
        env: &mut TypingEnv,
        original: NodeId,
        base: NodeId,
        span: Location,
        make_kind: impl FnOnce(NodeId) -> NodeKind,
    ) -> PreparedPlace {
        let mut prepared = self.prepare_place_base_for_projection(env, base, span);
        prepared.place = self.rebuild_place_node(env, original, make_kind(prepared.place));
        prepared
    }
    fn prepare_place_base_for_projection(
        &mut self,
        env: &mut TypingEnv,
        base: NodeId,
        span: Location,
    ) -> PreparedPlace {
        if node_is_place_reference(env.ir_arena, base) {
            self.prepare_place_for_consumer(env, base, span)
        } else {
            let ty = env.ir_arena[base].ty;
            let (store, load) = self.store_owned_temp(env, base, ty, span, ustr("$place"));
            PreparedPlace {
                prefix: vec![store],
                place: load,
            }
        }
    }

    fn rebuild_place_node(
        &mut self,
        env: &mut TypingEnv,
        original: NodeId,
        kind: NodeKind,
    ) -> NodeId {
        env.ir_arena.alloc(hir::Node::new(
            kind,
            env.ir_arena[original].ty,
            env.ir_arena[original].effects.clone(),
            env.ir_arena[original].span,
        ))
    }

    fn type_needs_semantic_drop(&mut self, env: &mut TypingEnv, ty: Type, span: Location) -> bool {
        !self.type_has_concrete_trivial_copy_impl(env, ty, span)
    }

    /// Resolves the scope-exit drop of an owned binding initialized with `value`.
    ///
    /// An immutable binding holds its initializer for its whole lifetime, so drop necessity is
    /// decided from the initializer value (e.g. a literal needs no drop even when its type is not
    /// trivially copyable). A mutable binding can be reassigned an owned value, so its drop is
    /// resolved from its type alone.
    fn unresolved_or_skipped_drop_for_value(
        &mut self,
        env: &mut TypingEnv,
        value: NodeId,
        ty: Type,
        binding_mutable: bool,
        span: Location,
    ) -> PendingLocalDrop {
        let needs_drop = if binding_mutable {
            self.type_needs_semantic_drop(env, ty, span)
        } else {
            self.node_value_needs_semantic_drop(env, value, ty, span)
        };
        if needs_drop {
            self.add_value_constraint_for_unknown_drop(value_trait_id(env), ty, span);
            PendingLocalDrop::Unknown
        } else {
            PendingLocalDrop::Resolved(ResolvedLocalDrop::Skip)
        }
    }

    pub(crate) fn set_local_owned_storage_from_value(
        &mut self,
        env: &mut TypingEnv,
        local_id: LocalDeclId,
        value: NodeId,
        ty: Type,
        span: Location,
    ) {
        let owns_storage = !node_is_place_reference(env.ir_arena, value);
        let binding_mutable = env.all_locals[local_id.as_index()].mut_ty.is_mutable();
        let drop = owns_storage.then(|| {
            self.unresolved_or_skipped_drop_for_value(env, value, ty, binding_mutable, span)
        });

        let local = &mut env.all_locals[local_id.as_index()];
        if let Some(drop) = drop {
            local.set_owned_storage(drop);
        } else {
            local.set_non_owning_storage();
        }
    }

    fn add_value_constraint_for_unknown_drop(
        &mut self,
        value_trait_id: crate::module::TraitId,
        ty: Type,
        span: Location,
    ) {
        if !ty.is_function() {
            self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                value_trait_id,
                vec![ty],
                vec![],
                vec![],
                span,
            ));
        }
    }

    fn node_value_needs_semantic_drop(
        &mut self,
        env: &mut TypingEnv,
        value: NodeId,
        ty: Type,
        span: Location,
    ) -> bool {
        use NodeKind::*;

        // A named type may have an explicit `Value` impl whose `drop` is not memberwise,
        // so the structural shortcut below does not apply to it.
        if ty.data().is_named() {
            return self.type_needs_semantic_drop(env, ty, span);
        }

        // Pre-extract the children we need to recurse into so we can drop the borrow on the arena before the recursive call.
        // Avoids cloning the whole `NodeKind` just to satisfy the borrow checker.
        let children: SmallVec<[NodeId; 4]> = match &env.ir_arena[value].kind {
            Immediate(_) | GetFunction(_) | GetSubscript(_) | GetTraitMethod(_) => return false,
            Variant(variant) => smallvec![variant.payload],
            Block(block) => block.tail_node().into_iter().collect(),
            Tuple(nodes) | Record(nodes) => nodes.iter().copied().collect(),
            BuildClosure(closure) => closure.captures.iter().copied().collect(),
            BuildSubscriptValue(_) => return false,
            _ => return self.type_needs_semantic_drop(env, ty, span),
        };
        children.iter().any(|node| {
            self.node_value_needs_semantic_drop(env, *node, env.ir_arena[*node].ty, span)
        })
    }

    fn materialize_owned_values(
        &mut self,
        env: &mut TypingEnv,
        values: impl IntoIterator<Item = NodeId>,
        span: Location,
    ) -> Vec<NodeId> {
        values
            .into_iter()
            .map(|value| self.materialize_owned_value(env, value, span))
            .collect()
    }

    fn value_evaluation_prefix_nodes(&self, arena: &NodeArena, node_id: NodeId) -> Vec<NodeId> {
        if node_is_place_reference(arena, node_id) {
            self.place_evaluation_prefix_nodes(arena, node_id)
        } else {
            vec![node_id]
        }
    }

    fn value_evaluation_prefix_nodes_for_many(
        &self,
        arena: &NodeArena,
        node_ids: impl IntoIterator<Item = NodeId>,
    ) -> Vec<NodeId> {
        node_ids
            .into_iter()
            .flat_map(|node_id| self.value_evaluation_prefix_nodes(arena, node_id))
            .collect()
    }

    fn place_evaluation_prefix_nodes(&self, arena: &NodeArena, node_id: NodeId) -> Vec<NodeId> {
        match &arena[node_id].kind {
            NodeKind::LoadLocal(_) => Vec::new(),
            NodeKind::Project(project) => self.place_evaluation_prefix_nodes(arena, project.value),
            NodeKind::FieldAccess(field_access) => {
                self.place_evaluation_prefix_nodes(arena, field_access.value)
            }
            _ => vec![node_id],
        }
    }

    fn discard_unused_value(
        &mut self,
        env: &mut TypingEnv,
        value: NodeId,
        span: Location,
    ) -> NodeId {
        if !node_is_place_reference(env.ir_arena, value) {
            let ty = env.ir_arena[value].ty;
            if self.node_value_needs_semantic_drop(env, value, ty, span) {
                let temp_start_index = env.cur_locals.len();
                let (store, _) = self.store_owned_temp(env, value, ty, span, ustr("$discard"));
                let nodes = vec![store];
                let drops = self.cleanup_locals_for_locals(env, temp_start_index);
                env.cur_locals.truncate(temp_start_index);
                let effects = env.ir_arena[value].effects.clone();
                let kind = self.block_or_cleanup_scope(nodes, drops);
                return env
                    .ir_arena
                    .alloc(hir::Node::new(kind, Type::unit(), effects, span));
            }
            return value;
        }

        if place_evaluation_depends_on_addressor_place(env.ir_arena, value) {
            return value;
        }

        let prefix = self.value_evaluation_prefix_nodes(env.ir_arena, value);
        match prefix.len() {
            0 => env.ir_arena.alloc(hir::Node::new(
                NodeKind::Immediate(LiteralValue::new_native(())),
                Type::unit(),
                no_effects(),
                span,
            )),
            1 => prefix[0],
            _ => {
                let prefix_effects = prefix
                    .iter()
                    .map(|node| &env.ir_arena[*node].effects)
                    .collect::<Vec<_>>();
                let effects = self.make_dependent_effect(prefix_effects);
                env.ir_arena.alloc(hir::Node::new(
                    Self::block(prefix, Vec::new()),
                    Type::unit(),
                    effects,
                    span,
                ))
            }
        }
    }

    pub(crate) fn diverging_prefix_node(
        &mut self,
        env: &mut TypingEnv,
        node_ids: impl IntoIterator<Item = NodeId>,
    ) -> NodeKind {
        // The sequence never completes, so every already-evaluated sub-expression is abandoned.
        // Discard each so owned temporaries run their drop glue before the divergence; the
        // diverging (never-typed) node itself produces no value and is left untouched.
        let nodes = node_ids
            .into_iter()
            .map(|node_id| {
                if env.ir_arena[node_id].ty == Type::never() {
                    node_id
                } else {
                    let span = env.ir_arena[node_id].span;
                    self.discard_unused_value(env, node_id, span)
                }
            })
            .collect();
        Self::block(nodes, Vec::new())
    }

    pub(crate) fn diverging_prefix_result(
        &mut self,
        env: &mut TypingEnv,
        node_ids: impl IntoIterator<Item = NodeId>,
        effects: EffType,
    ) -> (NodeKind, Type, MutType, EffType) {
        (
            self.diverging_prefix_node(env, node_ids),
            Type::never(),
            MutType::constant(),
            effects,
        )
    }

    fn infer_static_apply(
        &mut self,
        env: &mut TypingEnv,
        path: &ast::Path,
        path_span: Location,
        args: &[DExprId],
        expr_span: Location,
        arguments_unnamed: UnnamedArg,
    ) -> Result<(NodeKind, Type, MutType, EffType), InternalCompilationError> {
        use hir::Node as N;
        use hir::NodeKind as K;
        let args_span =
            || Location::fuse(args.iter().map(|arg| env.ast_arena[*arg].span)).unwrap_or(path_span);
        // Get the function and its type from the environment.
        Ok(
            if let Some(target) = self.prepare_static_call_target(
                env,
                path,
                path_span,
                args.len(),
                args_span(),
                arguments_unnamed,
            )? {
                let drivers = self.driven_access_chain_static_call_args(env, args, &target)?;
                if !drivers.is_empty() {
                    return self.infer_static_apply_with_driven_access_chain_args(
                        env, target, args, drivers, path_span, expr_span,
                    );
                }
                let (args_node_ids, args_effects, args_diverge) =
                    self.check_exprs_until_never(env, args, &target.inst_fn_ty.args, path_span)?;
                if args_diverge {
                    let nodes =
                        self.value_evaluation_prefix_nodes_for_many(env.ir_arena, args_node_ids);
                    self.diverging_prefix_result(env, nodes, args_effects)
                } else {
                    if let Some(constraint) = target.have_trait_constraint {
                        self.add_pub_constraint(constraint);
                    }
                    let call = self.build_static_call_from_checked_args(
                        env,
                        StaticCallFromCheckedArgs {
                            callee: target.callee,
                            abi_arg_tys: target.abi_arg_tys,
                            inst_fn_ty: target.inst_fn_ty,
                            result_convention: target.result_convention,
                            inst_data: target.inst_data,
                            args_node_ids,
                            visible_arg_passing: target.visible_arg_passing,
                            result_mut_ty: target.result_mut_ty,
                        },
                        expr_span,
                    );
                    (call.node, call.ty, call.mut_ty, call.effects)
                }
            } else if let Some(type_def) = env.get_type_def(path)? {
                // Retrieve the payload type and the tag, if it is an enum.
                let (type_def, payload_ty, ty, tag) =
                    self.instantiate_type_def(type_def, expr_span, &env.module_env);
                // Compute the arity from the payload type.
                let payload_tys = if payload_ty == Type::unit() {
                    vec![]
                } else {
                    match &*payload_ty.data() {
                        TypeKind::Tuple(tuple) => tuple.clone(),
                        TypeKind::Record(_) => {
                            return Err(internal_compilation_error!(IsNotCorrectProductType {
                                which: WhichProductTypeIsNot::Tuple,
                                type_def,
                                what: WhatIsNotAProductType::from_tag(tag),
                                instantiation_span: expr_span,
                            }));
                        }
                        _ => vec![payload_ty],
                    }
                };
                // Validate the number of arguments.
                let arity = payload_tys.len();
                let arg_count = args.len();
                if arity != arg_count {
                    return Err(internal_compilation_error!(WrongNumberOfArguments {
                        expected: arity,
                        expected_span: path_span,
                        got: arg_count,
                        got_span: args_span(),
                    }));
                }
                // Here we know that we have the right number of arguments, validate the types.
                let expected_tys = payload_tys
                    .iter()
                    .map(|ty| FnArgType::new(*ty, MutType::constant()))
                    .collect::<Vec<_>>();
                let (node_ids, effects, diverges) =
                    self.check_exprs_until_never(env, args, &expected_tys, expr_span)?;
                if diverges {
                    self.diverging_prefix_result(env, node_ids, effects)
                } else {
                    let node_ids = self.materialize_owned_values(env, node_ids, expr_span);
                    let inner_kind = if node_ids.is_empty() {
                        K::Immediate(LiteralValue::new_native(()))
                    } else {
                        K::Tuple(b(SVec2::from_vec(node_ids)))
                    };
                    let node = if let Some(tag) = tag {
                        let inner_node_id = env.ir_arena.alloc(N::new(
                            inner_kind,
                            payload_ty,
                            effects.clone(),
                            expr_span,
                        ));
                        K::Variant(HirVariant::new(tag, inner_node_id))
                    } else {
                        inner_kind
                    };
                    (node, ty, MutType::constant(), effects)
                }
            } else {
                // Structural variants cannot be paths
                if path.segments.len() > 1 {
                    return Err(internal_compilation_error!(InvalidVariantConstructor {
                        span: path_span,
                    }));
                }
                // If it is not a known function or trait or type def, assume it to be a variant constructor.
                let (payload_node_ids, payload_types, effects, diverges) =
                    self.infer_exprs_drop_mut_until_never(env, args)?;
                if diverges {
                    self.diverging_prefix_result(env, payload_node_ids, effects)
                } else {
                    let payload_node_ids =
                        self.materialize_owned_values(env, payload_node_ids, expr_span);
                    let (payload_ty, payload_node_id) = match payload_node_ids.len() {
                        0 => (
                            Type::unit(),
                            env.ir_arena.alloc(N::new(
                                K::Immediate(LiteralValue::new_native(())),
                                Type::unit(),
                                no_effects(),
                                path_span,
                            )),
                        ),
                        _ => {
                            let payload_ty = Type::tuple(payload_types);
                            let payload_span = Location::fuse(
                                payload_node_ids.iter().map(|id| env.ir_arena[*id].span),
                            )
                            .unwrap();
                            let node = K::Tuple(b(SVec2::from_vec(payload_node_ids)));
                            let payload_node_id = env.ir_arena.alloc(N::new(
                                node,
                                payload_ty,
                                effects.clone(),
                                payload_span,
                            ));
                            (payload_ty, payload_node_id)
                        }
                    };
                    // Create a fresh type and add a constraint for that type to include this variant.
                    let tag = path.segments[0].0;
                    let variant_ty = self.fresh_type_var_ty();
                    let payload_span = env.ir_arena[payload_node_id].span;
                    self.ty_constraints.push(TypeConstraint::Pub(
                        PubTypeConstraint::new_type_has_variant(
                            variant_ty,
                            expr_span,
                            tag,
                            payload_ty,
                            payload_span,
                        ),
                    ));
                    let node = K::Variant(HirVariant::new(tag, payload_node_id));
                    (node, variant_ty, MutType::constant(), effects)
                }
            },
        )
    }

    fn infer_exprs_drop_mut_until_never(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[DExprId],
    ) -> Result<(Vec<NodeId>, Vec<Type>, EffType, bool), InternalCompilationError> {
        let mut nodes = Vec::with_capacity(exprs.len());
        let mut tys = Vec::with_capacity(exprs.len());
        let mut effects = Vec::with_capacity(exprs.len());
        let mut diverges = false;
        for expr in exprs {
            let yield_count_before = env
                .yield_context
                .as_ref()
                .map_or(0, |ctx| ctx.yielded_nodes.len());
            let node_id = self.infer_expr_drop_mut(env, *expr)?;
            let ty = env.ir_arena[node_id].ty;
            let expr_effects = env.ir_arena[node_id].effects.clone();
            nodes.push(node_id);
            tys.push(ty);
            effects.push(expr_effects);
            if ty == Type::never() {
                let contains_new_yield = env
                    .yield_context
                    .as_ref()
                    .is_some_and(|ctx| ctx.yielded_nodes.len() > yield_count_before);
                if contains_new_yield {
                    continue;
                }
                diverges = true;
                break;
            }
        }
        let combined_effects = self.make_dependent_effect(&effects);
        Ok((nodes, tys, combined_effects, diverges))
    }

    fn infer_record(
        &mut self,
        env: &mut TypingEnv,
        fields: &[&RecordField<Desugared>],
    ) -> Result<(NodeKind, Type, EffType), InternalCompilationError> {
        let exprs = fields.iter().map(|(_, expr)| *expr).collect::<Vec<_>>();
        let (node_ids, types, effects, diverges) =
            self.infer_exprs_drop_mut_until_never(env, &exprs)?;
        if diverges {
            let payload_node = self.diverging_prefix_node(env, node_ids);
            Ok((payload_node, Type::never(), effects))
        } else {
            let span = Location::fuse(fields.iter().map(|(_, expr)| env.ast_arena[*expr].span))
                .unwrap_or_else(Location::new_synthesized);
            let node_ids = self.materialize_owned_values(env, node_ids, span);
            let payload_ty = fields_to_record_type(fields, types);
            let payload_node = NodeKind::Record(b(SVec2::from_vec(node_ids)));
            Ok((payload_node, payload_ty, effects))
        }
    }

    // fn infer_exprs_drop_mut_zipped(
    //     &mut self,
    //     env: &mut TypingEnv,
    //     exprs: &[DExprId],
    // ) -> Result<(Vec<(hir::Node, Type)>, EffType), InternalCompilationError> {
    //     let mut effects = Vec::with_capacity(exprs.len());
    //     let nodes_and_tys = exprs
    //         .iter()
    //         .map(|arg| {
    //             let node = self.infer_expr_drop_mut(env, *arg)?;
    //             let ty = node.ty;
    //             effects.push(node.effects.clone());
    //             Ok::<(hir::Node, Type), InternalCompilationError>((node, ty))
    //         })
    //         .collect::<Result<Vec<_>, _>>()?;

    //     let combined_effects = self.make_dependent_effect(&effects);
    //     Ok((nodes_and_tys, combined_effects))
    // }

    fn infer_exprs_ret_arg_ty_until_never(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[DExprId],
    ) -> Result<(Vec<NodeId>, Vec<FnArgType>, EffType, bool), InternalCompilationError> {
        let mut node_ids = Vec::with_capacity(exprs.len());
        let mut tys = Vec::with_capacity(exprs.len());
        let mut effects = Vec::with_capacity(exprs.len());
        let mut diverges = false;
        for expr in exprs {
            let (node_id, mut_ty) = self.infer_expr(env, *expr)?;
            let ty = env.ir_arena[node_id].ty;
            let expr_effects = env.ir_arena[node_id].effects.clone();
            node_ids.push(node_id);
            tys.push(FnArgType::new(ty, mut_ty));
            effects.push(expr_effects);
            if ty == Type::never() {
                diverges = true;
                break;
            }
        }
        let combined_effects = self.make_dependent_effect(&effects);
        Ok((node_ids, tys, combined_effects, diverges))
    }

    fn check_and_sort_record_fields(
        fields: &RecordFields<Desugared>,
        constructor_span: Location,
        ctx: DuplicatedFieldContext,
    ) -> Result<Vec<&RecordField<Desugared>>, InternalCompilationError> {
        // Check that all fields are unique.
        let mut names_seen = FxHashMap::default();
        for ((name, span), _) in fields.iter() {
            if let Some(prev_span) = names_seen.insert(name, span) {
                return Err(internal_compilation_error!(DuplicatedField {
                    first_occurrence: *prev_span,
                    second_occurrence: *span,
                    constructor_span,
                    ctx,
                }));
            }
        }
        // Reorder the names, the types and the nodes to have fields sorted by name.
        let mut fields = fields.iter().collect::<Vec<_>>();
        fields.sort_by_key(|(name_a, _)| name_a.0);
        Ok(fields)
    }

    fn check_exprs_until_never(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[DExprId],
        expected_tys: &[FnArgType],
        expected_span: Location,
    ) -> Result<(Vec<NodeId>, EffType, bool), InternalCompilationError> {
        let mut node_ids = Vec::with_capacity(exprs.len());
        let mut effects = Vec::with_capacity(exprs.len());
        let mut diverges = false;
        for (arg, arg_ty) in exprs.iter().zip(expected_tys) {
            let node_id = self.check_expr(env, *arg, arg_ty.ty, arg_ty.mut_ty, expected_span)?;
            let ty = env.ir_arena[node_id].ty;
            let expr_effects = env.ir_arena[node_id].effects.clone();
            node_ids.push(node_id);
            effects.push(expr_effects);
            if ty == Type::never() {
                diverges = true;
                break;
            }
        }
        let combined_effects = self.make_dependent_effect(&effects);
        Ok((node_ids, combined_effects, diverges))
    }

    pub fn check_expr(
        &mut self,
        env: &mut TypingEnv,
        expr_id: DExprId,
        expected_ty: Type,
        expected_mut: MutType,
        expected_span: Location,
    ) -> Result<NodeId, InternalCompilationError> {
        let expr = &env.ast_arena[expr_id];
        let expr_span = expr.span;
        use ExprKind::*;
        use hir::Node as N;
        use hir::NodeKind as K;

        // Literal of correct type, we are good
        if let Literal(value, ty) = &expr.kind {
            if *ty == expected_ty {
                let node = K::Immediate(value.clone());
                return Ok(env
                    .ir_arena
                    .alloc(N::new(node, expected_ty, no_effects(), expr_span)));
            }
        }

        // Functions abstraction
        if let Abstract(data) = &expr.kind {
            let ty_data = expected_ty.data();
            if let TypeKind::Function(fn_ty) = &*ty_data {
                let fn_ty = fn_ty.clone();
                drop(ty_data);
                let (node_id, node_ty, actual_mut, _) =
                    self.infer_abstract(env, &data.args, data.body, Some(*fn_ty), expr_span)?;
                self.add_sub_type_constraint(node_ty, expr_span, expected_ty, expected_span);
                self.add_mut_be_at_least_constraint(
                    actual_mut,
                    expr_span,
                    expected_mut,
                    expected_span,
                );
                return Ok(node_id);
            }
        }

        if Self::is_access_chain_expr(&expr.kind) {
            let chain = self.access_chain_for_expr(env, expr_id);
            let mode = if expected_mut.is_mutable() {
                SubscriptMemberKind::Mut
            } else {
                SubscriptMemberKind::Ref
            };
            let (node_id, actual_mut) = self.infer_access_chain_with_body(
                env,
                chain,
                mode,
                expr_span,
                |_, _, place, place_ty| Ok((place, place_ty)),
            )?;
            let node_ty = env.ir_arena[node_id].ty;
            self.add_sub_type_constraint(node_ty, expr_span, expected_ty, expected_span);
            self.add_mut_be_at_least_constraint(actual_mut, expr_span, expected_mut, expected_span);
            return Ok(node_id);
        }

        // Other cases, infer and add constraints
        let (node_id, actual_mut) = self.infer_expr(env, expr_id)?;
        let node_ty = env.ir_arena[node_id].ty;
        self.add_sub_type_constraint(node_ty, expr_span, expected_ty, expected_span);
        self.add_mut_be_at_least_constraint(actual_mut, expr_span, expected_mut, expected_span);
        Ok(node_id)
    }

    pub fn log_debug_constraints(&self, module_env: ModuleEnv) {
        if !log::log_enabled!(log::Level::Trace) {
            return;
        }
        if self.ty_constraints.is_empty() {
            log::trace!("No type constraints before unification.");
        } else {
            log::trace!("Type constraints before unification:");
            for constraint in &self.ty_constraints {
                log::trace!("  {}", constraint.format_with(&module_env));
            }
        }
        if self.mut_constraints.is_empty() {
            log::trace!("No mutability constraints before unification.");
        } else {
            log::trace!("Mutability constraints before unification:");
            for constraint in &self.mut_constraints {
                log::trace!("  {constraint}");
            }
        }
    }

    #[allow(dead_code)]
    fn log_debug_effect_constraints(&mut self) {
        self.effects.log_debug_constraints();
    }

    pub(crate) fn add_same_type_with_sub_effects_constraint(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    ) {
        if current == expected {
            return;
        }
        self.ty_constraints
            .push(TypeConstraint::SameTypeWithSubEffects {
                current,
                current_span,
                expected,
                expected_span,
            });
    }

    pub(crate) fn add_same_type_constraint(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    ) {
        if current == expected {
            return;
        }
        self.ty_constraints.push(TypeConstraint::SameType {
            current,
            current_span,
            expected,
            expected_span,
        });
    }

    pub(crate) fn add_sub_type_constraint(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    ) {
        if current == expected {
            return;
        }
        self.ty_constraints.push(TypeConstraint::SubType {
            current,
            current_span,
            expected,
            expected_span,
        });
    }

    fn add_same_mut_constraint(
        &mut self,
        current: MutType,
        current_span: Location,
        expected: MutType,
        expected_span: Location,
    ) {
        if current == expected {
            return;
        }
        self.mut_constraints.push(MutConstraint::SameMut {
            current,
            current_span,
            expected,
            expected_span,
        });
    }

    fn add_mut_be_at_least_constraint(
        &mut self,
        current: MutType,
        current_span: Location,
        target: MutType,
        reason_span: Location,
    ) {
        if target == MutType::constant() {
            // everything has at least constant mutability
            return;
        }
        if current == MutType::mutable() {
            // mutable can be used for all cases
            return;
        }
        self.mut_constraints.push(MutConstraint::MutBeAtLeast {
            current,
            current_span,
            target,
            reason_span,
        });
    }

    pub(crate) fn add_same_effect_constraint(
        &mut self,
        current: &EffType,
        current_span: Location,
        expected: &EffType,
        expected_span: Location,
    ) {
        if current == expected {
            return;
        }
        self.effects
            .add_same_constraint(current, current_span, expected, expected_span);
    }

    pub(crate) fn add_effect_dep_constraint_with_origin(
        &mut self,
        current: &EffType,
        current_span: Location,
        target: &EffType,
        target_span: Location,
        origin: super::effect_solver::EffectConstraintOrigin,
    ) -> Result<(), InternalCompilationError> {
        self.effects
            .add_effect_dep_with_origin(current, current_span, target, target_span, origin)
    }

    /// Add a constraint that the two function types must be equal.
    /// They must have the same number of arguments.
    #[allow(dead_code)]
    pub(crate) fn add_same_fn_type_constraint(
        &mut self,
        current: &FnType,
        current_span: Location,
        expected: &FnType,
        expected_span: Location,
    ) {
        self.add_same_fn_type_constraint_impl(current, current_span, expected, expected_span, true);
    }

    /// Add a constraint that the two function types must be equal, optionally skipping effects.
    /// They must have the same number of arguments.
    /// When `include_effects` is false, the effect constraint is not added. This is used for
    /// trait implementations where effects are validated separately.
    pub(crate) fn add_same_fn_type_constraint_without_effects(
        &mut self,
        current: &FnType,
        current_span: Location,
        expected: &FnType,
        expected_span: Location,
    ) {
        self.add_same_fn_type_constraint_impl(
            current,
            current_span,
            expected,
            expected_span,
            false,
        );
    }

    fn add_same_fn_type_constraint_impl(
        &mut self,
        current: &FnType,
        current_span: Location,
        expected: &FnType,
        expected_span: Location,
        include_effects: bool,
    ) {
        for (current_arg, expected_arg) in current.args.iter().zip(expected.args.iter()) {
            self.add_same_type_with_sub_effects_constraint(
                current_arg.ty,
                current_span,
                expected_arg.ty,
                expected_span,
            );
            self.add_same_mut_constraint(
                current_arg.mut_ty,
                current_span,
                expected_arg.mut_ty,
                expected_span,
            );
        }
        self.add_same_type_with_sub_effects_constraint(
            current.ret,
            current_span,
            expected.ret,
            expected_span,
        );
        if include_effects {
            self.add_same_effect_constraint(
                &current.effects,
                current_span,
                &expected.effects,
                expected_span,
            );
        }
    }

    /// Make a new effect depending on the given effects
    pub fn make_dependent_effect<T: Borrow<EffType> + Clone>(
        &mut self,
        deps: impl AsRef<[T]>,
    ) -> EffType {
        self.effects.make_dependent_effect(deps)
    }

    /// Make the two effects equal and fuse their dependencies
    pub fn unify_effects(&mut self, eff1: &EffType, eff2: &EffType) -> EffType {
        self.effects.unify_effects(eff1, eff2)
    }

    pub fn unify(
        self,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<UnifiedTypeInference, InternalCompilationError> {
        UnifiedTypeInference::unify_type_inference(self, trait_solver, arena)
    }
}

#[derive(new)]
pub struct AnnotationTypeMapper<'a, 'b> {
    ty_inf: &'a mut TypeInference,
    explicit_subst: Option<&'b InstSubst>,
}
impl TypeMapper for AnnotationTypeMapper<'_, '_> {
    fn map_type(&mut self, ty: Type) -> Type {
        let var = { ty.data().as_variable().copied() };
        if let Some(var) = var {
            if let Some(ty) = self
                .explicit_subst
                .and_then(|explicit_subst| explicit_subst.0.get(&var))
            {
                *ty
            } else {
                self.ty_inf.fresh_type_var_ty()
            }
        } else {
            ty
        }
    }

    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
        if mut_ty.is_variable() {
            self.ty_inf.fresh_mut_var_ty()
        } else {
            mut_ty
        }
    }

    fn map_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        let mut result = EffType::empty();
        for effect in eff_ty.iter() {
            if let Effect::Variable(var) = effect {
                if let Some(eff) = self
                    .explicit_subst
                    .and_then(|explicit_subst| explicit_subst.1.get(&var))
                {
                    result.extend(eff);
                } else {
                    result.insert(Effect::Variable(self.ty_inf.fresh_effect_var()));
                }
            } else {
                result.insert(effect);
            }
        }
        result
    }

    fn affects_type(&mut self, ty: Type) -> bool {
        // The mapper only acts on variables (type, mutability, or effect),
        // so a fully concrete type is unchanged.
        !ty.is_constant()
    }
}

fn node_contains_any_yield(arena: &NodeArena, node_id: NodeId, yield_nodes: &[NodeId]) -> bool {
    yield_nodes.contains(&node_id)
        || arena[node_id]
            .kind
            .child_node_ids()
            .into_iter()
            .any(|child| node_contains_any_yield(arena, child, yield_nodes))
}

fn collect_free_variables(
    expr_id: DExprId,
    arena: &DExprArena,
    bound: &mut Vec<FxHashSet<ustr::Ustr>>,
    free: &mut FxHashSet<ustr::Ustr>,
) {
    let expr = &arena[expr_id];
    use ExprKind::*;
    match &expr.kind {
        Identifier(path) => {
            if let [(name, _)] = &path.segments[..] {
                let is_bound = bound.iter().rev().any(|scope| scope.contains(name));
                if !is_bound {
                    free.insert(*name);
                }
            }
        }
        Let(data) => {
            collect_free_variables(data.expr, arena, bound, free);
            if let Some(scope) = bound.last_mut() {
                scope.insert(data.pattern.kind.name.0);
            }
        }
        PatternConstraint(data) => collect_free_variables(data.expr, arena, bound, free),
        EffectsUnsafe(expr) => collect_free_variables(*expr, arena, bound, free),
        Abstract(data) => {
            let mut scope = FxHashSet::default();
            for (arg, _) in &data.args {
                scope.insert(*arg);
            }
            bound.push(scope);
            collect_free_variables(data.body, arena, bound, free);
            bound.pop();
        }
        Block(exprs) => {
            bound.push(FxHashSet::default());
            for expr in exprs {
                collect_free_variables(*expr, arena, bound, free);
            }
            bound.pop();
        }
        Match(data) => {
            collect_free_variables(data.cond_expr, arena, bound, free);
            for (pattern, body) in &data.alternatives {
                let mut scope = FxHashSet::default();
                collect_pattern_vars(pattern, &mut scope);
                bound.push(scope);
                collect_free_variables(*body, arena, bound, free);
                bound.pop();
            }
            if let Some(default) = &data.default {
                collect_free_variables(*default, arena, bound, free);
            }
        }
        ForLoop(_) => {
            // For loops are desugared before type inference
            unreachable!("ForLoop should be desugared")
        }
        Apply(data) => {
            collect_free_variables(data.func, arena, bound, free);
            for arg in &data.args {
                collect_free_variables(*arg, arena, bound, free);
            }
        }
        NamedSubscript(data) => {
            collect_free_variables(data.receiver, arena, bound, free);
            for arg in &data.args {
                collect_free_variables(*arg, arena, bound, free);
            }
        }
        Assign(data) => {
            collect_free_variables(data.place, arena, bound, free);
            collect_free_variables(data.value, arena, bound, free);
        }
        AssignOp(data) => {
            collect_free_variables(data.place, arena, bound, free);
            collect_free_variables(data.value, arena, bound, free);
        }
        Tuple(args) | Array(args) => {
            for arg in args {
                collect_free_variables(*arg, arena, bound, free);
            }
        }
        SetLiteral(_) | MapLiteral(_) => {
            unreachable!("collection literals should be desugared before free-variable analysis")
        }
        Project(data) => collect_free_variables(data.expr, arena, bound, free),
        FieldAccess(data) => collect_free_variables(data.expr, arena, bound, free),
        TypeAscription(data) => collect_free_variables(data.expr, arena, bound, free),
        Return(expr) => {
            collect_free_variables(*expr, arena, bound, free);
        }
        Yield(expr) => {
            collect_free_variables(*expr, arena, bound, free);
        }
        Loop(data) => {
            collect_free_variables(data.body, arena, bound, free);
        }
        Break(data) => {
            if let Some(value) = data.value {
                collect_free_variables(value, arena, bound, free);
            }
        }
        Record(fields) => {
            for (_, expr) in fields {
                collect_free_variables(*expr, arena, bound, free);
            }
        }
        StructLiteral(data) => {
            for (_, expr) in &data.fields {
                collect_free_variables(*expr, arena, bound, free);
            }
        }
        Index(data) => {
            collect_free_variables(data.array, arena, bound, free);
            collect_free_variables(data.index, arena, bound, free);
        }
        Literal(_, _)
        | FormattedString(_)
        | PropertyPath(_)
        | TraitAssociatedConst(_)
        | Continue(_)
        | Error => {}
    }
}

fn place_evaluation_depends_on_addressor_place(arena: &NodeArena, node_id: NodeId) -> bool {
    use NodeKind::*;

    match &arena[node_id].kind {
        Apply(app) => app.ty.returns_place(),
        StaticApply(app) => app.ty.returns_place(),
        TraitMethodApply(app) => app.ty.returns_place(),
        CallDictionaryMethod(call) => call.ty.returns_place(),
        Project(project) => place_evaluation_depends_on_addressor_place(arena, project.value),
        FieldAccess(field_access) => {
            place_evaluation_depends_on_addressor_place(arena, field_access.value)
        }
        Block(block) => block
            .body
            .last()
            .is_some_and(|node| place_evaluation_depends_on_addressor_place(arena, *node)),
        _ => false,
    }
}

fn place_evaluation_depends_on_projection_place(arena: &NodeArena, node_id: NodeId) -> bool {
    use NodeKind::*;

    match &arena[node_id].kind {
        Project(_) | FieldAccess(_) => true,
        Block(block) => block
            .body
            .last()
            .is_some_and(|node| place_evaluation_depends_on_projection_place(arena, *node)),
        WithPlace(node) => place_evaluation_depends_on_projection_place(arena, node.body),
        _ => false,
    }
}

fn assignment_initializes_storage(
    arena: &NodeArena,
    place_id: NodeId,
    env: &TypingEnv<'_>,
) -> bool {
    use NodeKind::*;

    match &arena[place_id].kind {
        LoadLocal(load) => {
            env.all_locals[load.id.as_index()].assignment_mode
                == LocalAssignmentMode::InitializeStorage
        }
        Project(project) => assignment_initializes_storage(arena, project.value, env),
        FieldAccess(field_access) => assignment_initializes_storage(arena, field_access.value, env),
        _ => false,
    }
}

impl TypeInference {
    /// Whether `ty` has a concrete `TrivialCopy` impl in scope. Cached per
    /// inference pass to avoid recloning the module's impl table on every
    /// probe.
    pub(super) fn type_has_concrete_trivial_copy_impl(
        &mut self,
        env: &mut TypingEnv<'_>,
        ty: Type,
        span: Location,
    ) -> bool {
        if !ty.is_constant() {
            return false;
        }
        if let Some(&cached) = self.trivial_copy_cache.get(&ty) {
            return cached;
        }
        let mut trait_solver =
            TraitSolverProbe::from_module(env.module_env.current, env.module_env.modules);
        let result = trait_solver
            .solve_outputs(
                env.module_env.expect_std_trait_id(TRIVIAL_COPY_TRAIT_NAME),
                &[ty],
                span,
                env.ir_arena,
            )
            .is_ok();
        self.trivial_copy_cache.insert(ty, result);
        result
    }
}

fn visible_arg_passing_from_runtime<'a>(
    runtime_arg_passing: Option<&'a [ResolvedArgPassing]>,
    inst_data: &hir::FnInstData,
    visible_arg_count: usize,
) -> Option<&'a [ResolvedArgPassing]> {
    let runtime_arg_passing = runtime_arg_passing?;
    let hidden_dict_arg_count = inst_data.dicts_req.len();
    if hidden_dict_arg_count == 0 {
        Some(runtime_arg_passing)
    } else {
        assert_eq!(
            runtime_arg_passing.len(),
            hidden_dict_arg_count + visible_arg_count,
            "runtime argument passing should contain hidden evidence followed by visible arguments"
        );
        Some(&runtime_arg_passing[hidden_dict_arg_count..])
    }
}

fn collect_pattern_vars(pattern: &Pattern, bound: &mut FxHashSet<ustr::Ustr>) {
    use PatternKind::*;
    if let Variant { vars, .. } = &pattern.kind {
        for var in vars {
            if let PatternVar::Named((name, _)) = var {
                bound.insert(*name);
            }
        }
    }
}

fn property_to_fn_path(
    path: &ast::Path,
    variable: &str,
    access: PropertyAccess,
    span: Location,
    env: &TypingEnv,
) -> Result<ast::Path, InternalCompilationError> {
    let (scope, mod_path) = path.segments.split_last().unwrap();
    let fn_name = format!("@{} {}.{}", access.as_prefix(), scope.0, variable);
    let mut fn_path = ast::Path::new(mod_path.to_vec());
    fn_path.segments.push((ustr(&fn_name), span));
    if env.module_env.get_function(&fn_path.segments)?.is_none() {
        Err(internal_compilation_error!(UnknownProperty {
            scope: path.clone(),
            variable: ustr(variable),
            cause: access,
            span,
        }))
    } else {
        Ok(fn_path)
    }
}

fn fields_to_record_type<P: crate::ast::Phase>(
    fields: &[&RecordField<P>],
    types: Vec<Type>,
) -> Type {
    Type::record(
        fields
            .iter()
            .map(|field| field.0.0)
            .zip(types)
            .collect::<Vec<_>>(),
    )
}
