use std::{borrow::Borrow, iter::once};

use derive_new::new;
use ena::unify::InPlaceUnificationTable;
use itertools::Itertools;
use ustr::{Ustr, ustr};

use crate::{
    FxHashMap, FxHashSet,
    compiler::error::{
        DuplicatedFieldContext, InternalCompilationError, WhatIsNotAProductType,
        WhichProductTypeIsNot,
    },
    containers::{SVec2, b, continuous_hashmap_to_vec},
    format::FormatWith,
    hir::function::{Function, FunctionDefinition, ScriptFunction},
    hir::value::{LiteralValue, Value},
    hir::{self, EnvStore, Immediate, NodeArena, NodeId, NodeKind},
    internal_compilation_error,
    module::{LocalDecl, LocalDeclId, ModuleEnv, ModuleFunction, TypeDefLookupResult, id::Id},
    parser::{
        ast::{
            self, DExprArena, DExprId, Desugared, ExprKind, Pattern, PatternConstraintKind,
            PatternKind, PatternVar, PropertyAccess, RecordField, RecordFields, UnnamedArg,
        },
        location::Location,
    },
    std::{STD_MODULE_ID, array::array_type, core::REPR_TRAIT, math::int_type},
    types::{
        effects::{
            EffType, Effect, EffectVar, EffectVarKey, EffectsSubstitution, PrimitiveEffect, effect,
            no_effects,
        },
        mutability::{MutType, MutVar, MutVarKey},
        trait_solver::TraitSolver,
        r#type::{FnArgType, FnType, TyVarKey, Type, TypeKind, TypeSubstitution, TypeVar},
        type_like::TypeLike,
        type_mapper::TypeMapper,
        type_scheme::{PubTypeConstraint, TypeScheme},
        typing_env::{LoopFrame, TypingEnv},
    },
};

use super::{
    constraints::{EffectConstraint, MutConstraint, TypeConstraint},
    unify::UnifiedTypeInference,
};

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

    pub fn fresh_type_var_subst(&mut self, source: &[TypeVar]) -> TypeSubstitution {
        source
            .iter()
            .map(|&ty_var| (ty_var, self.fresh_type_var_ty()))
            .collect()
    }

    pub fn fresh_effect_var_subst(&mut self, source: &FxHashSet<EffectVar>) -> EffectsSubstitution {
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
    ) -> (crate::types::r#type::TypeDefRef, Type, Type, Option<Ustr>) {
        let (type_def, tag) = type_def_lookup.lookup_payload();
        let (payload_ty, _inst_data, subst) = type_def
            .payload_scheme(tag)
            .instantiate_with_fresh_vars(self, use_site, None);
        let params: Vec<_> = type_def
            .shape
            .ty_quantifiers
            .iter()
            .map(|quantifier| quantifier.instantiate(&subst.0))
            .collect();
        let named_ty = Type::named(type_def.clone(), params);
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
        let mut capture_args = Vec::new(); // inner Ids

        // Sort for deterministic order.
        let mut sorted_free_vars: Vec<_> = free_vars.into_iter().collect();
        sorted_free_vars.sort();

        let mut fn_all_locals = Vec::new();
        for var_name in sorted_free_vars {
            let found = env.get_variable_index_and_id(&var_name);
            if let Some((index, outer_id)) = found {
                // It is a local variable in the current environment, capture it.
                let local = &env.all_locals[outer_id.as_index()];
                let capture_id = env.ir_arena.alloc(N::new(
                    K::EnvLoad(hir::EnvLoad {
                        index: index as u32,
                        id: outer_id,
                    }),
                    local.ty,
                    no_effects(),
                    span,
                ));
                capture_node_ids.push(capture_id);
                let inner_id = LocalDeclId::from_index(fn_all_locals.len());
                let mut inner_local = local.clone();
                inner_local.scope = span; // the local's scope is the whole lambda
                fn_all_locals.push(inner_local);
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
                    let id = LocalDeclId::from_index(fn_all_locals.len());
                    fn_all_locals.push(LocalDecl::new(*name, arg_ty.mut_ty, arg_ty.ty, None, span));
                    id
                })
                .collect::<Vec<_>>();
            (explicit_locals, fn_ty.ret)
        } else {
            let explicit_locals = args
                .iter()
                .map(|name| {
                    let id = LocalDeclId::from_index(fn_all_locals.len());
                    fn_all_locals.push(LocalDecl::new(
                        *name,
                        self.fresh_mut_var_ty(),
                        self.fresh_type_var_ty(),
                        None,
                        span,
                    ));
                    id
                })
                .collect::<Vec<_>>();
            (explicit_locals, self.fresh_type_var_ty())
        };

        let args_ty = explicit_locals
            .iter()
            .map(|id| fn_all_locals[id.as_index()].as_fn_arg_type())
            .collect();

        // 4. Build environment for typing the function's body.
        let fn_cur_locals = capture_args.into_iter().chain(explicit_locals).collect();
        let all_arg_names = fn_all_locals
            .iter()
            .map(|local| local.name.0)
            .collect::<Vec<_>>();

        // The lambda uses the same HIR arena as the outer function (module's arena).
        let mut inner_env = TypingEnv::new(
            &mut fn_all_locals,
            fn_cur_locals,
            env.new_import_slots,
            env.new_type_deps,
            env.module_env,
            Some((ret_ty, env.ast_arena[body].span)),
            env.annotation_ty_subst,
            vec![],
            env.lambda_functions,
            env.base_local_function_index,
            env.ast_arena,
            env.ir_arena,
        );

        // 5. Infer the body's type.
        let code_id = self.check_expr(
            &mut inner_env,
            body,
            ret_ty,
            MutType::constant(),
            env.ast_arena[body].span,
        )?;

        let code = &inner_env.ir_arena[code_id];
        let effects = code.effects.clone();

        // 6. Store and return the function's type.
        let fn_ty = FnType::new(args_ty, ret_ty, effects);
        let fn_ty_wrapper = Type::function_type(fn_ty.clone());
        let arg_names: Vec<_> = args.iter().map(|(name, _)| *name).collect();
        let code = ScriptFunction::new(code_id, all_arg_names);
        let ty_scheme = TypeScheme::new_just_type(fn_ty);
        let function = ModuleFunction {
            definition: FunctionDefinition::new(ty_scheme, arg_names, None),
            code: b(code) as Function,
            spans: None, // FIXME: add spans
            locals: fn_all_locals,
        };
        // TODO: Maybe consider generating the BuildClosure node here.
        let function_id = env.collect_lambda_module_function(function);
        let value_fn = Value::function(function_id, env.current_module_id());
        let fn_node_id = env.ir_arena.alloc(N::new(
            K::Immediate(Immediate::new(value_fn)),
            fn_ty_wrapper,
            no_effects(),
            span,
        ));

        let node_id = if capture_node_ids.is_empty() {
            fn_node_id
        } else {
            let node = K::BuildClosure(b(hir::BuildClosure {
                function: fn_node_id,
                captures: capture_node_ids,
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
                K::Immediate(Immediate::new(value.clone())),
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
                    && let Some((index, id)) = env.get_variable_index_and_id(name)
                {
                    let local = &env.all_locals[id.as_index()];
                    let node = K::EnvLoad(hir::EnvLoad {
                        index: index as u32,
                        id,
                    });
                    (node, local.ty, local.mut_ty, no_effects())
                }
                // Retrieve the trait method from the environment, if it exists
                else if let Some((_module_name, trait_descr)) =
                    env.module_env.get_trait_function(path)?
                {
                    let (trait_ref, function_index, definition) = trait_descr;
                    let (inst_fn_ty, inst_data, subst) =
                        definition.ty_scheme.instantiate_with_fresh_vars(
                            self,
                            expr_span,
                            Some(trait_ref.type_var_count()),
                        );
                    assert!(
                        inst_data.dicts_req.is_empty(),
                        "Instantiation data for trait function is not supported yet."
                    );
                    trait_ref.constraints.iter().for_each(|constraint| {
                        let mut constraint = constraint.instantiate(&subst);
                        constraint.instantiate_location(expr_span);
                        self.add_pub_constraint(constraint);
                    });
                    let mut trait_tys = continuous_hashmap_to_vec(subst.0).unwrap();
                    assert_eq!(trait_tys.len(), trait_ref.type_var_count() as usize);
                    let output_tys = trait_tys.split_off(trait_ref.input_type_count() as usize);
                    let input_tys = trait_tys;
                    self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                        trait_ref.clone(),
                        input_tys.clone(),
                        output_tys.clone(),
                        expr_span,
                    ));
                    let node = K::GetTraitFunction(b(hir::GetTraitFunction {
                        trait_ref,
                        function_index,
                        function_path: path.clone(),
                        function_span: expr_span,
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
                else if let Some((definition, function, _module_name)) = env.get_function(path)? {
                    let (fn_ty, inst_data, _subst) = definition
                        .ty_scheme
                        .instantiate_with_fresh_vars(self, expr_span, None);
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
                        self.instantiate_type_def(type_def, expr_span);
                    if payload_ty != Type::unit() {
                        return Err(internal_compilation_error!(IsNotCorrectProductType {
                            which: WhichProductTypeIsNot::Unit,
                            type_def: type_def.clone(),
                            what: WhatIsNotAProductType::from_tag(tag),
                            instantiation_span: expr_span,
                        }));
                    }
                    // But the value of the node is the underlying data.
                    let value = if let Some(tag) = tag {
                        Value::unit_variant(tag)
                    } else {
                        Value::unit()
                    };
                    let node = K::Immediate(Immediate::new(value));
                    (node, ty, MutType::constant(), EffType::empty())
                }
                // Otherwise, the name is neither a known variable or function, assume it to be a variant constructor
                else {
                    // Variants cannot be paths
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
                    // Build the variant value.
                    let node = K::Immediate(Immediate::new(Value::unit_variant(tag)));
                    (node, variant_ty, MutType::constant(), no_effects())
                }
            }
            Let(data) => {
                let name = data.pattern.kind.name;
                let mut_val = data.pattern.kind.mut_val;
                let node_id = self.infer_expr_drop_mut(env, data.expr)?;
                let node_ty = env.ir_arena[node_id].ty;
                let node_effects = env.ir_arena[node_id].effects.clone();
                let local = LocalDecl::new(
                    name,
                    MutType::resolved(mut_val),
                    node_ty,
                    data.ty_ascription,
                    expr_span,
                );
                let index = env.cur_locals.len();
                let id = LocalDeclId::from_index(env.all_locals.len());
                env.all_locals.push(local);
                env.cur_locals.push(id);
                let node = K::EnvStore(EnvStore {
                    value: node_id,
                    index: index as u32,
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
                            TypeDefLookupResult::Struct(type_def.clone()),
                            data.span,
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
                let node_id = self.infer_expr_drop_mut(env, *expr)?;
                let ty = env.ir_arena[node_id].ty;
                self.add_same_type_constraint(ty, sp(*expr), outer_ty, outer_span);
                let effects = env.ir_arena[node_id].effects.clone();
                let node = K::Return(node_id);
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
                    Self::diverging_prefix_result([func_node_id], effects)
                } else {
                    // Infer the type and mutability of the arguments and collect their code and constraints
                    let (args_nodes, args_tys, args_effects, args_diverge) =
                        self.infer_exprs_ret_arg_ty_until_never(env, &data.args)?;
                    if args_diverge {
                        let nodes = once(func_node_id).chain(args_nodes).collect::<Vec<_>>();
                        let effects = self.make_dependent_effect([&func_effects, &args_effects]);
                        Self::diverging_prefix_result(nodes, effects)
                    } else {
                        // Allocate a fresh variable for the return type and effects of the function
                        let ret_ty = self.fresh_type_var_ty();
                        let call_effects = self.fresh_effect_var_ty();
                        // Build the function type
                        let func_ty = Type::function_type(FnType::new(
                            args_tys,
                            ret_ty,
                            call_effects.clone(),
                        ));
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
                        // Store and return the result
                        let node = K::Apply(b(hir::Application {
                            function: func_node_id,
                            arguments: args_nodes,
                        }));
                        (node, ret_ty, MutType::constant(), combined_effects)
                    }
                }
            }
            Block(exprs) => {
                assert!(!exprs.is_empty());
                let env_size = env.cur_locals.len();
                let (nodes, types, effects, _diverges) =
                    self.infer_exprs_drop_mut_until_never(env, exprs)?;
                // Adjust the lexical scope of the variables declared in the block to end at the end of the block.
                for local_id in env.cur_locals.iter().skip(env_size) {
                    let local = &mut env.all_locals[local_id.as_index()];
                    assert_eq!(local.scope.source_id(), expr_span.source_id());
                    assert!(local.scope.end() <= expr_span.end());
                    local.scope = Location::new(
                        local.scope.start(),
                        expr_span.end(),
                        local.scope.source_id(),
                    );
                }
                env.cur_locals.truncate(env_size);
                let node = K::Block(b(SVec2::from_vec(nodes)));
                let ty = types.last().copied().unwrap_or(Type::unit());
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
                    Self::diverging_prefix_result([place_id], effects)
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
                        let effects = self.make_dependent_effect([&place_effects, &value_effects]);
                        Self::diverging_prefix_result([place_id, value_id], effects)
                    } else {
                        let combined_effects =
                            self.make_dependent_effect([&value_effects, &place_effects]);
                        let node = K::Assign(hir::Assignment {
                            place: place_id,
                            value: value_id,
                        });
                        (node, Type::unit(), MutType::constant(), combined_effects)
                    }
                }
            }
            Tuple(exprs) => {
                let (nodes, types, effects, diverges) =
                    self.infer_exprs_drop_mut_until_never(env, exprs)?;
                if diverges {
                    Self::diverging_prefix_result(nodes, effects)
                } else {
                    let ty = Type::tuple(types);
                    let node = if let Some(values) = nodes_as_bare_immediate(env.ir_arena, &nodes) {
                        K::Immediate(Immediate::new(Value::tuple(values)))
                    } else {
                        K::Tuple(b(SVec2::from_vec(nodes)))
                    };
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
                    Self::diverging_prefix_result([tuple_node_id], effects)
                } else {
                    let tuple_ty = self.fresh_type_var_ty(); // U
                    let (index, index_span) = data.index;
                    self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                        REPR_TRAIT.clone(),
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
                    let node = K::Project(tuple_node_id, index);
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
                        self.instantiate_type_def(type_def, expr_span);
                    // Check that it is a record.
                    if !payload_ty.data().is_record() {
                        return Err(internal_compilation_error!(IsNotCorrectProductType {
                            which: WhichProductTypeIsNot::Record,
                            type_def: type_def.clone(),
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
                        Self::diverging_prefix_result(nodes, effects)
                    } else {
                        // But the value of the node is the underlying record.
                        // If all nodes can be resolved to bare immediates, we can create an immediate value.
                        let resolved_nodes_value =
                            nodes_as_bare_immediate(env.ir_arena, &nodes).map(Value::tuple);
                        let node = if let Some(tag) = tag {
                            if let Some(value) = resolved_nodes_value {
                                let value = Value::raw_variant(tag, value);
                                K::Immediate(Immediate::new(value))
                            } else {
                                let record_node_id = env.ir_arena.alloc(N::new(
                                    K::Record(b(SVec2::from_vec(nodes))),
                                    payload_ty,
                                    effects.clone(),
                                    expr_span,
                                ));
                                K::Variant(tag, record_node_id)
                            }
                        } else if let Some(value) = resolved_nodes_value {
                            K::Immediate(Immediate::new(value))
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
                    let record_span = Location::fuse(fields.iter().map(|(n, _)| n.1)).unwrap();
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
                    // Build the variant construction node.
                    let node = if let Some(values) =
                        nodes_as_bare_immediate_ids(env.ir_arena, &[payload_node_id])
                    {
                        let value = values.first().unwrap().clone();
                        K::Immediate(Immediate::new(Value::raw_variant(tag, value)))
                    } else {
                        K::Variant(tag, payload_node_id)
                    };
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
                    Self::diverging_prefix_result([record_node_id], effects)
                } else {
                    let record_ty = self.fresh_type_var_ty(); // U
                    let (field, field_span) = data.name;
                    self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                        REPR_TRAIT.clone(),
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
                    let node = K::FieldAccess(record_node_id, field);
                    (node, element_ty, record_mut, effects)
                }
            }
            Array(exprs) => {
                use crate::std::array::Array;
                if exprs.is_empty() {
                    // The element type is a fresh type variable
                    let element_ty = self.fresh_type_var_ty();
                    // Build an empty array node and return it
                    let node = K::Immediate(Immediate::new(Value::native(Array::new())));
                    (
                        node,
                        array_type(element_ty),
                        MutType::constant(),
                        no_effects(),
                    )
                } else {
                    let (nodes, types, effects, diverges) =
                        self.infer_exprs_drop_mut_until_never(env, exprs)?;
                    if diverges {
                        Self::diverging_prefix_result(nodes, effects)
                    } else {
                        // The element type is the first element's type
                        // All elements must be of the first element's type
                        let element_ty = types[0];
                        // Infer the type of the elements and collect their code and constraints
                        for (ty, expr) in types.into_iter().skip(1).zip(exprs.iter().skip(1)) {
                            self.add_sub_type_constraint(ty, sp(*expr), element_ty, sp(exprs[0]));
                        }
                        // Build the array node and return it
                        let element_nodes = SVec2::from_vec(nodes);
                        let ty = array_type(element_ty);
                        // Can we build it as an immediate?
                        let node = if let Some(values) =
                            nodes_as_bare_immediate(env.ir_arena, &element_nodes)
                        {
                            let value = Value::native(Array::from_vec(values));
                            K::Immediate(Immediate::new(value))
                        } else {
                            K::Array(b(element_nodes))
                        };
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
                let array_ty = array_type(element_ty);
                // Infer type of the array expression and make sure it is an array
                let (array_node_id, array_expr_mut) = self.infer_expr(env, data.array)?;
                let array_effects = env.ir_arena[array_node_id].effects.clone();
                if env.ir_arena[array_node_id].ty == Type::never() {
                    let effects = self.make_dependent_effect([&array_effects]);
                    Self::diverging_prefix_result([array_node_id], effects)
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
                        let effects = self.make_dependent_effect([&array_effects, &index_effects]);
                        Self::diverging_prefix_result([array_node_id, index_node_id], effects)
                    } else {
                        let combined_effects = self.make_dependent_effect([
                            &effect(PrimitiveEffect::Fallible),
                            &array_effects,
                            &index_effects,
                        ]);
                        let node = K::Index(array_node_id, index_node_id);
                        (node, element_ty, array_expr_mut, combined_effects)
                    }
                }
            }
            EffectsUnsafe(expr) => {
                if env.current_module_id() != STD_MODULE_ID {
                    return Err(internal_compilation_error!(Unsupported {
                        span: expr_span,
                        reason: "`effects_unsafe` is only available while compiling the standard library"
                            .to_string(),
                    }));
                }

                let (inner_node_id, inner_mut_ty) = self.infer_expr(env, *expr)?;
                let inner_node = env.ir_arena[inner_node_id].clone();
                return Ok((
                    env.ir_arena.alloc(N::new(
                        inner_node.kind,
                        inner_node.ty,
                        no_effects(),
                        expr_span,
                    )),
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
            Loop(body) => {
                let result_ty = self.fresh_type_var();
                env.loop_frames.push(LoopFrame::new(result_ty, false));
                let body_id =
                    self.check_expr(env, *body, Type::unit(), MutType::constant(), sp(*body))?;
                let loop_frame = env.loop_frames.pop().unwrap();
                let effects = env.ir_arena[body_id].effects.clone();
                let ty = if loop_frame.saw_break {
                    Type::variable(loop_frame.result_ty)
                } else {
                    Type::never()
                };
                (K::Loop(body_id), ty, MutType::constant(), effects)
            }
            SoftBreak => {
                let ty = if let Some(loop_frame) = env.loop_frames.last_mut() {
                    loop_frame.saw_break = true;
                    self.add_same_type_constraint(
                        Type::variable(loop_frame.result_ty),
                        expr_span,
                        Type::unit(),
                        expr_span,
                    );
                    Type::never()
                } else {
                    Type::unit()
                };
                (K::SoftBreak, ty, MutType::constant(), no_effects())
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

    pub(crate) fn diverging_prefix_node(node_ids: impl IntoIterator<Item = NodeId>) -> NodeKind {
        NodeKind::Block(b(SVec2::from_vec(node_ids.into_iter().collect())))
    }

    pub(crate) fn diverging_prefix_result(
        node_ids: impl IntoIterator<Item = NodeId>,
        effects: EffType,
    ) -> (NodeKind, Type, MutType, EffType) {
        (
            Self::diverging_prefix_node(node_ids),
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
            if let Some((_module_name, trait_descr)) = env.module_env.get_trait_function(path)? {
                let (trait_ref, function_index, definition) = trait_descr;
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
                let (inst_fn_ty, inst_data, subst) = definition
                    .ty_scheme
                    .instantiate_with_fresh_vars(self, path_span, Some(trait_ref.type_var_count()));
                assert!(
                    inst_data.dicts_req.is_empty(),
                    "Instantiation data for trait function is not supported yet."
                );
                // Instantiate the constraints and add them to our list.
                trait_ref.constraints.iter().for_each(|constraint| {
                    let mut constraint = constraint.instantiate(&subst);
                    constraint.instantiate_location(path_span);
                    self.add_pub_constraint(constraint);
                });
                // Make sure the types of the trait arguments match the expected types
                let (args_node_ids, args_effects, args_diverge) =
                    self.check_exprs_until_never(env, args, &inst_fn_ty.args, path_span)?;
                if args_diverge {
                    Self::diverging_prefix_result(args_node_ids, args_effects)
                } else {
                    let mut trait_tys = continuous_hashmap_to_vec(subst.0).unwrap();
                    assert_eq!(trait_tys.len(), trait_ref.type_var_count() as usize);
                    let output_tys = trait_tys.split_off(trait_ref.input_type_count() as usize);
                    let input_tys = trait_tys;
                    self.add_pub_constraint(PubTypeConstraint::new_have_trait(
                        trait_ref.clone(),
                        input_tys.clone(),
                        output_tys,
                        path_span,
                    ));
                    // Build and return the trait function node
                    let ret_ty = inst_fn_ty.ret;
                    let combined_effects =
                        self.make_dependent_effect([&args_effects, &inst_fn_ty.effects]);
                    let node = K::TraitFnApply(b(hir::TraitFnApplication {
                        trait_ref,
                        function_index,
                        function_path: path.clone(),
                        function_span: path_span,
                        arguments: args_node_ids,
                        arguments_unnamed,
                        ty: inst_fn_ty,
                        input_tys,
                        inst_data,
                    }));
                    (node, ret_ty, MutType::constant(), combined_effects)
                }
            } else if let Some((definition, function, _module_name)) = env.get_function(path)? {
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
                    .instantiate_with_fresh_vars(self, path_span, None);
                // Get argument names if any
                let argument_names = arguments_unnamed.filter_args(&definition.arg_names);
                // Get the code and make sure the types of its arguments match the expected types
                let (args_node_ids, args_effects, args_diverge) =
                    self.check_exprs_until_never(env, args, &inst_fn_ty.args, path_span)?;
                if args_diverge {
                    Self::diverging_prefix_result(args_node_ids, args_effects)
                } else {
                    // Build and return the function node
                    let ret_ty = inst_fn_ty.ret;
                    let combined_effects =
                        self.make_dependent_effect([&args_effects, &inst_fn_ty.effects]);
                    let node = K::StaticApply(b(hir::StaticApplication {
                        function,
                        function_path: Some(path.clone()),
                        function_span: path_span,
                        arguments: args_node_ids,
                        argument_names,
                        ty: inst_fn_ty,
                        inst_data,
                    }));
                    (node, ret_ty, MutType::constant(), combined_effects)
                }
            } else if let Some(type_def) = env.get_type_def(path)? {
                // Retrieve the payload type and the tag, if it is an enum.
                let (type_def, payload_ty, ty, tag) =
                    self.instantiate_type_def(type_def, expr_span);
                // Compute the arity from the payload type.
                let payload_tys = if payload_ty == Type::unit() {
                    vec![]
                } else {
                    match &*payload_ty.data() {
                        TypeKind::Tuple(tuple) => tuple.clone(),
                        TypeKind::Record(_) => {
                            return Err(internal_compilation_error!(IsNotCorrectProductType {
                                which: WhichProductTypeIsNot::Tuple,
                                type_def: type_def.clone(),
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
                    Self::diverging_prefix_result(node_ids, effects)
                } else {
                    // But the value of the node is the underlying tuple.
                    // If all nodes can be resolved to bare immediates, we can create an immediate value.
                    let resolved_nodes_value =
                        nodes_as_bare_immediate(env.ir_arena, &node_ids).map(Value::tuple);
                    let inner_kind = if let Some(value) = resolved_nodes_value {
                        K::Immediate(Immediate::new(value))
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
                        K::Variant(tag, inner_node_id)
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
                    Self::diverging_prefix_result(payload_node_ids, effects)
                } else {
                    let (payload_ty, payload_node_id) = match payload_node_ids.len() {
                        0 => (
                            Type::unit(),
                            env.ir_arena.alloc(N::new(
                                K::Immediate(Immediate::new(Value::unit())),
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
                            let node = if let Some(values) =
                                nodes_as_bare_immediate(env.ir_arena, &payload_node_ids)
                            {
                                K::Immediate(Immediate::new(Value::tuple(values)))
                            } else {
                                K::Tuple(b(SVec2::from_vec(payload_node_ids)))
                            };
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
                    // Build the variant construction node.
                    let node = if let Some(values) =
                        nodes_as_bare_immediate_ids(env.ir_arena, &[payload_node_id])
                    {
                        let value = values.first().unwrap().clone();
                        K::Immediate(Immediate::new(Value::raw_variant(tag, value)))
                    } else {
                        K::Variant(tag, payload_node_id)
                    };
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
            let payload_node = Self::diverging_prefix_node(node_ids);
            Ok((payload_node, Type::never(), effects))
        } else {
            let payload_ty = fields_to_record_type(fields, types);
            let payload_node =
                if let Some(values) = nodes_as_bare_immediate(env.ir_arena, &node_ids) {
                    NodeKind::Immediate(Immediate::new(Value::tuple(values)))
                } else {
                    NodeKind::Record(b(SVec2::from_vec(node_ids)))
                };
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
                let node = K::Immediate(Immediate::new(value.clone()));
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

        // Partition the effects into primitive and unresolved ones.
        let (primitives, variables) = deps
            .iter()
            .flat_map(|eff| eff.borrow().iter())
            .partition::<FxHashSet<_>, _>(|eff| eff.is_primitive());

        // If all effects are primitive, we can just return them.
        if variables.is_empty() {
            return EffType::from_iter(primitives);
        } else if variables.len() == 1 && primitives.is_empty() {
            // If there is only one variable and no primitive, we can just return it.
            return EffType::single(*variables.iter().next().unwrap());
        }

        // Otherwise, we need to create a new effect variable.
        let effects = EffType::from_iter(variables.into_iter().chain(primitives).unique());
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
    explicit_ty_subst: Option<&'b TypeSubstitution>,
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
                        *effect
                    }
                })
                .collect(),
        )
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
        Return(expr) | Loop(expr) => {
            collect_free_variables(*expr, arena, bound, free);
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
        Literal(_, _) | FormattedString(_) | PropertyPath(_) | SoftBreak | Error => {}
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

fn fields_to_record_type<P: crate::parser::ast::Phase>(
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

/// Return a list of cloned values if all nodes (by NodeId) are immediate values and have no effects.
fn nodes_as_bare_immediate(
    arena: &NodeArena,
    node_ids: &[impl Borrow<NodeId>],
) -> Option<Vec<Value>> {
    let nodes = node_ids
        .iter()
        .map(|id| {
            let node = &arena[*id.borrow()];
            match &node.kind {
                NodeKind::Immediate(immediate) => {
                    // For now, do not support function values for transformation into composed immediates.
                    // The reason is that different functions might have different instantiation requirements.
                    if node.effects.any() || node.ty.data().is_function() {
                        None
                    } else {
                        Some(&immediate.value)
                    }
                }
                _ => None,
            }
        })
        .collect::<Option<Vec<&Value>>>()?;
    Some(nodes.into_iter().cloned().collect())
}

/// Same as `nodes_as_bare_immediate` but takes a direct slice of NodeId.
fn nodes_as_bare_immediate_ids(arena: &NodeArena, node_ids: &[NodeId]) -> Option<Vec<Value>> {
    nodes_as_bare_immediate(arena, node_ids)
}
