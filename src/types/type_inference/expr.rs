use std::borrow::Borrow;

use derive_new::new;
use ena::unify::InPlaceUnificationTable;
use smallvec::{SmallVec, smallvec};
use ustr::{Ustr, ustr};

use crate::{
    FxHashMap, FxHashSet,
    ast::{
        self, DExprArena, DExprId, Desugared, ExprKind, Pattern, PatternConstraintKind,
        PatternKind, PatternVar, PropertyAccess, RecordField, RecordFields, UnnamedArg, UstrSpan,
    },
    compiler::error::{
        DuplicatedFieldContext, InternalCompilationError, InvalidLoopControlKind, LoopControlKind,
        UnsafeFeature, WhatIsNotAProductType, WhichProductTypeIsNot,
    },
    containers::{SVec2, b, continuous_hashmap_to_vec},
    format::FormatWith,
    hir::{
        self, CallArgument, FieldAccess as HirFieldAccess, LoopId, NodeArena, NodeId, NodeKind,
        Project as HirProject, ProjectAt as HirProjectAt, StoreLocal, Variant as HirVariant,
        function::{
            FunctionDefinition, PendingArgPassing, PendingValueArgPassing, ResolvedArgPassing,
            ResolvedValueArgPassing, unresolved_arg_passing_for_args,
        },
        node_is_place_reference, place_resolution_may_create_temp,
        place_result_base_argument_index,
        value::LiteralValue,
    },
    internal_compilation_error,
    module::{
        DeferredLocalStorage, FunctionId, LocalAssignmentMode, LocalDecl, LocalDeclId, ModuleEnv,
        ModuleFunctionSpans, PendingFunctionBody, PendingLocalClone, PendingLocalDrop,
        PendingModuleFunction, PendingTakeLocalValueMode, ProjectionIndex, ResolvedLocalDrop,
        TraitId, TypeDefLookupResult, id::Id,
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
            EffType, Effect, EffectVar, EffectVarKey, EffectsInstSubst, PrimitiveEffect, effect,
            no_effects,
        },
        mutability::{MutType, MutVar, MutVarKey},
        r#trait::{Trait, TraitMethodIndex},
        trait_solver::{TraitSolver, TraitSolverProbe},
        r#type::{
            FnArgType, FnReturnConvention, FnType, TyVarKey, Type, TypeInstSubst, TypeKind, TypeVar,
        },
        type_like::TypeLike,
        type_mapper::{BitmapInstantiationMapper, TypeMapper},
        type_scheme::{PubTypeConstraint, TypeScheme},
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
    let [(trait_name, trait_span), associated_const] = path.segments.as_slice() else {
        return None;
    };
    Some((
        ast::Path::single(*trait_name, *trait_span),
        *associated_const,
    ))
}

use super::{
    constraints::{EffectConstraint, MutConstraint, TypeConstraint},
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
    pub(super) effect_unification_table: InPlaceUnificationTable<EffectVarKey>,
    pub(super) effect_constraints: Vec<EffectConstraint>,
    /// Memoised results of `TrivialCopy` solver probes keyed by the queried concrete type.
    /// `TraitSolverProbe::from_module` clones the module's impl table on every call, so this cache avoids re-cloning when the same type is checked repeatedly during a single inference pass.
    trivial_copy_cache: FxHashMap<Type, bool>,
    next_loop_id: LoopId,
}

struct PreparedPlace {
    prefix: Vec<NodeId>,
    place: NodeId,
}

struct PreparedCallArguments {
    arguments: Vec<CallArgument>,
    temp_stores: Vec<NodeId>,
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
        span: Location,
    ) {
        let trait_def = env.module_env.trait_def(trait_id);
        let subst = trait_def.type_param_subst_for_tys(input_tys, output_tys);
        let inst_subst = (subst, FxHashMap::default());
        let mut mapper = BitmapInstantiationMapper::new(&inst_subst);
        for constraint in trait_def
            .parent_constraints
            .iter()
            .chain(trait_def.constraints.iter())
        {
            let mut constraint = constraint.map(&mut mapper);
            constraint.instantiate_location(span);
            let parent = constraint
                .as_have_trait()
                .map(|(trait_id, input_tys, output_tys, _)| {
                    (*trait_id, input_tys.to_vec(), output_tys.to_vec())
                });
            self.add_pub_constraint(constraint);
            if let Some((parent_trait_id, parent_input_tys, parent_output_tys)) = parent {
                self.add_instantiated_trait_assumptions(
                    env,
                    parent_trait_id,
                    &parent_input_tys,
                    &parent_output_tys,
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
        self.add_pub_constraint(PubTypeConstraint::new_have_trait(
            trait_id,
            input_tys.clone(),
            output_tys.clone(),
            expr_span,
        ));
        self.add_instantiated_trait_assumptions(env, trait_id, &input_tys, &output_tys, expr_span);
        let associated_const_tys =
            trait_def.instantiate_associated_const_tys_for_tys(&input_tys, &output_tys);
        let ty = associated_const_tys[associated_const_index.as_index()];
        let node = NodeKind::GetTraitAssociatedConst(b(hir::GetTraitAssociatedConst {
            trait_id,
            associated_const_index,
            associated_const_name: associated_const_name.0,
            associated_const_span: associated_const_name.1,
            input_tys,
            output_tys,
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
        self.effect_unification_table.new_key(None)
    }

    pub fn fresh_effect_var_ty(&mut self) -> EffType {
        EffType::single_variable(self.fresh_effect_var())
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
        let named_ty = Type::named(type_def, params);
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

        let args_ty = explicit_locals
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
            env.new_import_slots,
            env.new_type_deps,
            env.module_env,
            Some((ret_ty, env.ast_arena[body].span)),
            expected_fn_ty
                .as_ref()
                .map_or(FnReturnConvention::Value, |fn_ty| fn_ty.return_convention),
            env.annotation_ty_subst,
            vec![],
            env.fuel_checks_enabled,
            env.lambda_functions,
            env.base_local_function_index,
            env.ast_arena,
            &mut fn_arena,
        );

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
            FunctionDefinition::new(ty_scheme, arg_names, None),
            PendingFunctionBody::new(fn_arena, code_id),
            runtime_arg_count,
            Some(spans),
            fn_all_locals,
        );
        let function_id = env.collect_lambda_module_function(function);
        let fn_node_id = env.ir_arena.alloc(N::new(
            K::GetFunction(b(hir::GetFunction {
                function: FunctionId::Local(function_id),
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
                span,
            ));
            let captures_value_dictionary = env.ir_arena.alloc(N::new(
                K::GetTraitDictionary(b(hir::GetTraitDictionary {
                    trait_id: value_trait_id,
                    input_tys: vec![capture_env_ty],
                    output_tys: vec![],
                })),
                env.module_env
                    .trait_def(value_trait_id)
                    .get_dictionary_type_for_tys(&[capture_env_ty], &[]),
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
                    let trait_constraints = trait_def.constraints.clone();
                    let (inst_fn_ty, inst_data, subst) =
                        definition.ty_scheme.instantiate_with_fresh_vars(
                            self,
                            expr_span,
                            Some(trait_ty_var_count),
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
                    let mut trait_tys = continuous_hashmap_to_vec(subst.0).unwrap();
                    assert_eq!(trait_tys.len(), trait_ty_var_count as usize);
                    let output_tys = trait_tys.split_off(trait_input_type_count as usize);
                    let input_tys = trait_tys;
                    self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                        trait_id,
                        input_tys.clone(),
                        output_tys.clone(),
                        expr_span,
                    ));
                    let node = K::GetTraitMethod(b(hir::GetTraitMethod {
                        trait_id,
                        method_index,
                        method_path: path.clone(),
                        method_span: expr_span,
                        input_tys,
                        output_tys,
                        inst_data,
                    }));
                    (
                        node,
                        Type::function_type(inst_fn_ty),
                        MutType::constant(),
                        no_effects(),
                    )
                }
                // Retrieve the function from the environment, if it exists
                else if let Some((definition, function, _module_id, _arg_passing)) = env
                    .get_function(path)?
                    .map(|(definition, function, module_id, arg_passing)| {
                        (definition.clone(), function, module_id, arg_passing)
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
                let initializer_is_borrow = node_is_place_reference(env.ir_arena, node_id);
                let initializer_place_needs_temp =
                    place_resolution_may_create_temp(env.ir_arena, node_id);
                let initializer_is_known_immutable = matches!(
                    initializer_mut_ty,
                    MutType::Resolved(mut_ty) if !mut_ty.is_mutable()
                );
                let initializer_is_known_trivial_copy =
                    self.type_has_concrete_trivial_copy_impl(env, node_ty, expr_span);
                let defer_storage = node_ty != Type::never()
                    && initializer_is_borrow
                    && !initializer_place_needs_temp
                    && !mut_val.is_mutable()
                    && !initializer_is_known_immutable
                    && !initializer_is_known_trivial_copy;
                let needs_owned_snapshot = initializer_place_needs_temp
                    || mut_val.is_mutable()
                    || initializer_is_known_trivial_copy;
                let needs_clone = needs_owned_snapshot
                    && node_ty != Type::never()
                    && initializer_is_borrow
                    && !initializer_is_known_trivial_copy;
                if needs_clone && !node_ty.is_function() {
                    self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                        value_trait_id(env),
                        vec![node_ty],
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
                    local.set_owned_storage(
                        self.unresolved_or_skipped_drop_for_value(env, node_id, node_ty, expr_span),
                    );
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
                let value_id = if node_ty != Type::never()
                    && initializer_is_borrow
                    && (initializer_place_needs_temp || initializer_is_known_trivial_copy)
                {
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
                        self.add_same_type_constraint(
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
                        self.add_same_type_constraint(
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
                self.add_same_type_constraint(ty, sp(*expr), outer_ty, outer_span);
                let effects = env.ir_arena[node_id].effects.clone();
                let return_value = if env.expected_return_convention.returns_place() {
                    if ty != Type::never() && !node_is_place_reference(env.ir_arena, node_id) {
                        return Err(internal_compilation_error!(Unsupported {
                            span: sp(*expr),
                            reason: "addressor return expression must be a place".into(),
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
                        let return_convention = match &*env.ir_arena[func_node_id].ty.data() {
                            TypeKind::Function(fn_ty) => fn_ty.return_convention,
                            _ => {
                                // First-class place-returning functions are not supported yet:
                                // unresolved dynamic callees are inferred as value-returning calls.
                                FnReturnConvention::Value
                            }
                        };
                        let abi_args = match &*env.ir_arena[func_node_id].ty.data() {
                            TypeKind::Function(fn_ty) => Some(fn_ty.args.clone()),
                            _ => None,
                        };
                        // Build the function type
                        let app_ty = FnType::new_with_return_convention(
                            args_tys.clone(),
                            ret_ty,
                            call_effects.clone(),
                            return_convention,
                        );
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
                            ty: app_ty,
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
                // Generates the following constraints:
                // FieldAccess(record_expr: T, field) -> V
                //     where T: Coercible<Target = U>, RecordFieldIs(U, V, field)
                let (record_node_id, record_mut) = self.infer_expr(env, data.expr)?;
                let effects = env.ir_arena[record_node_id].effects.clone();
                // Note: record_node.ty is T
                let record_node_ty = env.ir_arena[record_node_id].ty;
                if record_node_ty == Type::never() {
                    self.diverging_prefix_result(env, [record_node_id], effects)
                } else {
                    let record_ty = self.fresh_type_var_ty(); // U
                    let (field, field_span) = data.name;
                    self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                        repr_trait_id(env),
                        vec![record_node_ty],
                        vec![record_ty],
                        field_span,
                    ));
                    let element_ty = self.fresh_type_var_ty(); // V
                    self.add_pub_constraint(PubTypeConstraint::new_record_field_is(
                        record_ty,
                        sp(data.expr),
                        field,
                        field_span,
                        element_ty,
                    ));
                    let node = K::FieldAccess(HirFieldAccess::new(record_node_id, field));
                    (node, element_ty, record_mut, effects)
                }
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
                // New type for the array
                let element_ty = self.fresh_type_var_ty();
                let array_ty = env.array_type(element_ty);
                // Infer type of the array expression and make sure it is an array
                let (array_node_id, array_expr_mut) = self.infer_expr(env, data.array)?;
                let array_effects = env.ir_arena[array_node_id].effects.clone();
                if env.ir_arena[array_node_id].ty == Type::never() {
                    let effects = self.make_dependent_effect([&array_effects]);
                    self.diverging_prefix_result(env, [array_node_id], effects)
                } else {
                    let array_node_ty = env.ir_arena[array_node_id].ty;
                    self.add_sub_type_constraint(
                        array_node_ty,
                        sp(data.array),
                        array_ty,
                        sp(data.array),
                    );
                    // Check type of the index expression to be int
                    let index_node_id = self.check_expr(
                        env,
                        data.index,
                        int_type(),
                        MutType::constant(),
                        sp(data.index),
                    )?;
                    // Build the index node and return it
                    let index_effects = env.ir_arena[index_node_id].effects.clone();
                    if env.ir_arena[index_node_id].ty == Type::never() {
                        let mut nodes =
                            self.place_evaluation_prefix_nodes(env.ir_arena, array_node_id);
                        nodes.push(index_node_id);
                        let effects = self.make_dependent_effect([&array_effects, &index_effects]);
                        self.diverging_prefix_result(env, nodes, effects)
                    } else {
                        let (path, (definition, function, _module_id, arg_passing)) = {
                            let (path, (definition, function, module_id, arg_passing)) =
                                env.get_std_function(ustr("array_index"), expr_span)?;
                            (path, (definition.clone(), function, module_id, arg_passing))
                        };
                        let (inst_fn_ty, inst_data, _subst) = definition
                            .ty_scheme
                            .instantiate_with_fresh_vars(self, expr_span, None, env.module_env);
                        self.add_same_type_constraint(
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
                        let visible_arg_passing = visible_native_arg_passing(
                            arg_passing,
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
                        let call = K::StaticApply(b(hir::StaticApplication {
                            function,
                            function_path: Some(path),
                            function_span: expr_span,
                            extra_arguments: Vec::new(),
                            arguments: prepared_arguments.arguments,
                            argument_names: vec![ustr("array"), ustr("index")],
                            ty: inst_fn_ty,
                            inst_data,
                        }));
                        let call =
                            hir::Node::new(call, element_ty, combined_effects.clone(), expr_span);
                        let node = self.wrap_call_with_temp_drops(
                            env,
                            temp_start_index,
                            prepared_arguments.temp_stores,
                            call,
                        );
                        (node, element_ty, array_expr_mut, combined_effects)
                    }
                }
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
                    self.add_same_type_constraint(
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
                let ty = data.ty.map(&mut AnnotationTypeMapper::new(
                    self,
                    env.annotation_ty_subst,
                ));
                self.add_same_type_constraint(
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
                    let node = self.discard_unused_value(env, node, expr_span);
                    let diverges = env.ir_arena[node].ty == Type::never();
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
        local.set_owned_storage(self.unresolved_or_skipped_drop_for_value(env, value, ty, span));
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
        native_arg_passing: Option<&[ResolvedArgPassing]>,
    ) -> PreparedCallArguments {
        let arg_passing = self.argument_passing_for_args(arg_tys, abi_arg_tys, native_arg_passing);
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
                    if node_is_place_reference(env.ir_arena, *arg)
                        && place_resolution_may_create_temp(env.ir_arena, *arg)
                    {
                        let prepared = self.prepare_place_for_consumer(env, *arg, span);
                        stores.extend(prepared.prefix);
                        *arg = prepared.place;
                    }
                    if self.call_value_argument_needs_shared_ref_temp(
                        env, *arg, arg_ty.ty, *passing, span,
                    ) {
                        let value_ty = env.ir_arena[*arg].ty;
                        let (store, load) =
                            self.store_owned_temp(env, *arg, value_ty, span, ustr("$arg"));
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
        native_arg_passing: Option<&[ResolvedArgPassing]>,
    ) -> Vec<PendingArgPassing> {
        assert_eq!(arg_tys.len(), abi_arg_tys.len());
        if let Some(native_arg_passing) = native_arg_passing {
            assert_eq!(arg_tys.len(), native_arg_passing.len());
            return native_arg_passing
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
        let is_stable_place = node_is_place_reference(env.ir_arena, arg)
            && !matches!(env.ir_arena[arg].kind, NodeKind::GetTraitMethod(_));
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
            && (!node_is_place_reference(env.ir_arena, arg)
                || place_resolution_may_create_temp(env.ir_arena, arg))
            && !self.type_has_concrete_trivial_copy_impl(env, ty, span)
            && !ty.is_function()
        {
            self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                value_trait_id(env),
                vec![ty],
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
                    NodeKind::FieldAccess(HirFieldAccess::new(value, field_access.field))
                })
            }
            NodeKind::ProjectAt(project) => {
                self.prepare_projection_place(env, place, project.value, span, |value| {
                    NodeKind::ProjectAt(HirProjectAt::new(value, project.index))
                })
            }
            NodeKind::StaticApply(mut app) if app.ty.returns_place() => {
                if let Some(base_index) =
                    place_result_base_argument_index(env.ir_arena, &app.arguments)
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
                    place_result_base_argument_index(env.ir_arena, &app.arguments)
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
                    place_result_base_argument_index(env.ir_arena, &call.arguments)
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
                    place_result_base_argument_index(env.ir_arena, &app.arguments)
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

    fn unresolved_or_skipped_drop_for_value(
        &mut self,
        env: &mut TypingEnv,
        value: NodeId,
        ty: Type,
        span: Location,
    ) -> PendingLocalDrop {
        if self.node_value_needs_semantic_drop(env, value, ty, span) {
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
        let drop =
            owns_storage.then(|| self.unresolved_or_skipped_drop_for_value(env, value, ty, span));

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

        // Pre-extract the children we need to recurse into so we can drop the borrow on the arena before the recursive call.
        // Avoids cloning the whole `NodeKind` just to satisfy the borrow checker.
        let children: SmallVec<[NodeId; 4]> = match &env.ir_arena[value].kind {
            Immediate(_) | GetFunction(_) | GetTraitMethod(_) => return false,
            Variant(variant) => smallvec![variant.payload],
            Block(block) => block.tail_node().into_iter().collect(),
            Tuple(nodes) | Record(nodes) => nodes.iter().copied().collect(),
            BuildClosure(closure) => closure.captures.iter().copied().collect(),
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
            NodeKind::ProjectAt(project) => {
                self.place_evaluation_prefix_nodes(arena, project.value)
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

        if place_evaluation_depends_on_place_result(env.ir_arena, value) {
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
                let trait_ty_var_count = trait_def.type_var_count();
                let trait_input_type_count = trait_def.input_type_count();
                let trait_constraints = trait_def.constraints.clone();
                // Validate the number of arguments
                if definition.ty_scheme.ty.args.len() != args.len() {
                    return Err(internal_compilation_error!(WrongNumberOfArguments {
                        expected: definition.ty_scheme.ty.args.len(),
                        expected_span: path_span,
                        got: args.len(),
                        got_span: args_span(),
                    }));
                }
                // Instantiate its type scheme
                let (inst_fn_ty, inst_data, subst) =
                    definition.ty_scheme.instantiate_with_fresh_vars(
                        self,
                        path_span,
                        Some(trait_ty_var_count),
                        env.module_env,
                    );
                assert!(
                    inst_data.dicts_req.is_empty(),
                    "Instantiation data for trait method is not supported yet."
                );
                // Instantiate the constraints and add them to our list.
                let mut mapper = BitmapInstantiationMapper::new(&subst);
                trait_constraints.iter().for_each(|constraint| {
                    let mut constraint = constraint.map(&mut mapper);
                    constraint.instantiate_location(path_span);
                    self.add_pub_constraint(constraint);
                });
                // Make sure the types of the trait arguments match the expected types
                let (mut args_node_ids, args_effects, args_diverge) =
                    self.check_exprs_until_never(env, args, &inst_fn_ty.args, path_span)?;
                if args_diverge {
                    let nodes =
                        self.value_evaluation_prefix_nodes_for_many(env.ir_arena, args_node_ids);
                    self.diverging_prefix_result(env, nodes, args_effects)
                } else {
                    let mut trait_tys = continuous_hashmap_to_vec(subst.0).unwrap();
                    assert_eq!(trait_tys.len(), trait_ty_var_count as usize);
                    let output_tys = trait_tys.split_off(trait_input_type_count as usize);
                    let input_tys = trait_tys;
                    self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                        trait_id,
                        input_tys.clone(),
                        output_tys,
                        path_span,
                    ));
                    // Build and return the trait method node
                    let ret_ty = inst_fn_ty.ret;
                    let combined_effects =
                        self.make_dependent_effect([&args_effects, &inst_fn_ty.effects]);
                    let temp_start_index = env.cur_locals.len();
                    let prepared_arguments = self.prepare_call_arguments(
                        env,
                        &mut args_node_ids,
                        &inst_fn_ty.args,
                        &inst_fn_ty.args,
                        expr_span,
                        None,
                    );
                    let call = K::TraitMethodApply(b(hir::TraitMethodApplication {
                        trait_id,
                        method_index,
                        method_path: path.clone(),
                        method_span: path_span,
                        arguments: prepared_arguments.arguments,
                        arguments_unnamed,
                        ty: inst_fn_ty,
                        input_tys,
                        inst_data,
                    }));
                    let call = hir::Node::new(call, ret_ty, combined_effects.clone(), expr_span);
                    let node = self.wrap_call_with_temp_drops(
                        env,
                        temp_start_index,
                        prepared_arguments.temp_stores,
                        call,
                    );
                    (node, ret_ty, MutType::constant(), combined_effects)
                }
            } else if let Some((definition, function, _module_id, arg_passing)) = env
                .get_function(path)?
                .map(|(definition, function, module_id, arg_passing)| {
                    (definition.clone(), function, module_id, arg_passing)
                })
            {
                if definition.ty_scheme.ty.args.len() != args.len() {
                    return Err(internal_compilation_error!(WrongNumberOfArguments {
                        expected: definition.ty_scheme.ty.args.len(),
                        expected_span: path_span,
                        got: args.len(),
                        got_span: args_span(),
                    }));
                }
                // Instantiate its type scheme
                let (inst_fn_ty, inst_data, _subst) = definition
                    .ty_scheme
                    .instantiate_with_fresh_vars(self, path_span, None, env.module_env);
                // Get argument names if any
                let argument_names = arguments_unnamed.filter_args(&definition.arg_names);
                // Get the code and make sure the types of its arguments match the expected types
                let (mut args_node_ids, args_effects, args_diverge) =
                    self.check_exprs_until_never(env, args, &inst_fn_ty.args, path_span)?;
                if args_diverge {
                    let nodes =
                        self.value_evaluation_prefix_nodes_for_many(env.ir_arena, args_node_ids);
                    self.diverging_prefix_result(env, nodes, args_effects)
                } else {
                    // Build and return the function node
                    let ret_ty = inst_fn_ty.ret;
                    let combined_effects =
                        self.make_dependent_effect([&args_effects, &inst_fn_ty.effects]);
                    let visible_arg_passing =
                        visible_native_arg_passing(arg_passing, &inst_data, args_node_ids.len());
                    let temp_start_index = env.cur_locals.len();
                    let prepared_arguments = self.prepare_call_arguments(
                        env,
                        &mut args_node_ids,
                        &inst_fn_ty.args,
                        &definition.ty_scheme.ty.args,
                        expr_span,
                        visible_arg_passing,
                    );
                    let call = K::StaticApply(b(hir::StaticApplication {
                        function,
                        function_path: Some(path.clone()),
                        function_span: path_span,
                        extra_arguments: Vec::new(),
                        arguments: prepared_arguments.arguments,
                        argument_names,
                        ty: inst_fn_ty,
                        inst_data,
                    }));
                    let call = hir::Node::new(call, ret_ty, combined_effects.clone(), expr_span);
                    let node = self.wrap_call_with_temp_drops(
                        env,
                        temp_start_index,
                        prepared_arguments.temp_stores,
                        call,
                    );
                    (node, ret_ty, MutType::constant(), combined_effects)
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
            let node_id = self.infer_expr_drop_mut(env, *expr)?;
            let ty = env.ir_arena[node_id].ty;
            let expr_effects = env.ir_arena[node_id].effects.clone();
            nodes.push(node_id);
            tys.push(ty);
            effects.push(expr_effects);
            if ty == Type::never() {
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

        // Other cases, infer and add constraints
        let (node_id, actual_mut) = self.infer_expr(env, expr_id)?;
        let node_ty = env.ir_arena[node_id].ty;
        self.add_sub_type_constraint(node_ty, expr_span, expected_ty, expected_span);
        self.add_mut_be_at_least_constraint(actual_mut, expr_span, expected_mut, expected_span);
        Ok(node_id)
    }

    pub fn log_debug_constraints(&self, module_env: ModuleEnv) {
        if self.ty_constraints.is_empty() {
            log::debug!("No type constraints before unification.");
        } else {
            log::debug!("Type constraints before unification:");
            for constraint in &self.ty_constraints {
                log::debug!("  {}", constraint.format_with(&module_env));
            }
        }
        if self.mut_constraints.is_empty() {
            log::debug!("No mutability constraints before unification.");
        } else {
            log::debug!("Mutability constraints before unification:");
            for constraint in &self.mut_constraints {
                log::debug!("  {constraint}");
            }
        }
    }

    #[allow(dead_code)]
    fn log_debug_effect_constraints(&mut self) {
        log::debug!("Effect substitution table:");
        for i in 0..self.effect_unification_table.len() {
            let var = EffectVar::new(i as u32);
            let value = self.effect_unification_table.probe_value(var);
            match value {
                Some(value) => log::debug!("  {var} → {value}"),
                None => log::debug!("  {var} → {} (unbound)", {
                    self.effect_unification_table.find(var)
                }),
            }
        }
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

    fn add_same_effect_constraint(
        &mut self,
        current: &EffType,
        current_span: Location,
        expected: &EffType,
        expected_span: Location,
    ) {
        if current == expected {
            return;
        }
        self.effect_constraints.push(EffectConstraint::SameEffect {
            current: current.clone(),
            current_span,
            expected: expected.clone(),
            expected_span,
        });
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
            self.add_same_type_constraint(
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
        self.add_same_type_constraint(current.ret, current_span, expected.ret, expected_span);
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
        let deps = deps.as_ref();

        // Handle the trivial cases.
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

        // Otherwise, we need to create a new effect variable.
        let effect_var = self.effect_unification_table.new_key(Some(effects));
        EffType::single_variable(effect_var)
    }

    /// Make the two effects equal and fuse their dependencies
    pub fn unify_effects(&mut self, eff1: &EffType, eff2: &EffType) -> EffType {
        let var1 = eff1.to_single_variable();
        let var2 = eff2.to_single_variable();
        match (var1, var2) {
            (None, None) => eff1.union(eff2),
            (None, Some(var)) => {
                self.effect_unification_table
                    .union_value(var, Some(eff1.clone()));
                eff1.clone()
            }
            (Some(var), None) => {
                self.effect_unification_table
                    .union_value(var, Some(eff2.clone()));
                eff2.clone()
            }
            (Some(var1), Some(var2)) => {
                self.effect_unification_table.union(var1, var2);
                eff1.clone()
            }
        }
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
    explicit_ty_subst: Option<&'b TypeInstSubst>,
}
impl TypeMapper for AnnotationTypeMapper<'_, '_> {
    fn map_type(&mut self, ty: Type) -> Type {
        let var = { ty.data().as_variable().copied() };
        if let Some(var) = var {
            if let Some(ty) = self
                .explicit_ty_subst
                .and_then(|explicit_ty_subst| explicit_ty_subst.get(&var))
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
        EffType::from_vec(
            eff_ty
                .iter()
                .map(|effect| {
                    if effect.is_variable() {
                        Effect::Variable(self.ty_inf.fresh_effect_var())
                    } else {
                        effect
                    }
                })
                .collect(),
        )
    }

    fn affects_type(&mut self, ty: Type) -> bool {
        // The mapper only acts on variables (type, mutability, or effect),
        // so a fully concrete type is unchanged.
        !ty.is_constant()
    }
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
        Assign(data) => {
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

fn place_evaluation_depends_on_place_result(arena: &NodeArena, node_id: NodeId) -> bool {
    use NodeKind::*;

    match &arena[node_id].kind {
        Apply(app) => app.ty.returns_place(),
        StaticApply(app) => app.ty.returns_place(),
        TraitMethodApply(app) => app.ty.returns_place(),
        CallDictionaryMethod(call) => call.ty.returns_place(),
        Project(project) => place_evaluation_depends_on_place_result(arena, project.value),
        FieldAccess(field_access) => {
            place_evaluation_depends_on_place_result(arena, field_access.value)
        }
        ProjectAt(project) => place_evaluation_depends_on_place_result(arena, project.value),
        Block(block) => block
            .body
            .last()
            .is_some_and(|node| place_evaluation_depends_on_place_result(arena, *node)),
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
        ProjectAt(project) => assignment_initializes_storage(arena, project.value, env),
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
            .solve_output_types(
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

fn visible_native_arg_passing(
    passing: Option<&'static [ResolvedArgPassing]>,
    inst_data: &hir::FnInstData,
    visible_arg_count: usize,
) -> Option<&'static [ResolvedArgPassing]> {
    let passing = passing?;
    let hidden_dict_arg_count = inst_data.dicts_req.len();
    if hidden_dict_arg_count == 0 {
        Some(passing)
    } else {
        assert!(
            passing.len() >= hidden_dict_arg_count
                && passing.len() <= hidden_dict_arg_count + visible_arg_count
        );
        Some(&passing[hidden_dict_arg_count..])
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
