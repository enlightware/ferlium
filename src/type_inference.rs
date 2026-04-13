// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    borrow::Borrow,
    cell::RefCell,
    fmt::{self, Display},
    iter::once,
    mem,
};

use crate::{
    FxHashMap, FxHashSet,
    ast::{
        self, DExprArena, DExprId, Desugared, ExprKind, Pattern, PatternConstraintKind,
        PatternKind, PatternVar, RecordField, RecordFields, UnnamedArg,
    },
    containers::continuous_hashmap_to_vec,
    effects::{PrimitiveEffect, effect},
    error::{
        DuplicatedFieldContext, MutabilityMustBeWhat, WhatIsNotAProductType, WhichProductTypeIsNot,
    },
    format::FormatWith,
    function::{Function, FunctionDefinition},
    internal_compilation_error,
    location::Location,
    module::{LocalDecl, LocalDeclId, ModuleFunction, TypeDefLookupResult, id::Id},
    std::core::REPR_TRAIT,
    r#trait::TraitRef,
    trait_solver::TraitSolver,
    type_like::TypeLike,
    type_mapper::TypeMapper,
    type_scheme::TypeScheme,
    type_substitution::{TypeSubstituer, substitute_fn_type, substitute_type, substitute_types},
};
use derive_new::new;
use ena::unify::{EqUnifyValue, InPlace, InPlaceUnificationTable, Snapshot, UnifyKey, UnifyValue};
use itertools::{Itertools, multiunzip};
use ustr::{Ustr, ustr};

use crate::{
    ast::PropertyAccess,
    containers::{SVec2, b},
    dictionary_passing::DictionaryReq,
    effects::{EffType, Effect, EffectVar, EffectVarKey, EffectsSubstitution, no_effects},
    error::{ADTAccessType, InternalCompilationError, MutabilityMustBeContext},
    function::ScriptFunction,
    ir::{self, EnvStore, FnInstData, Immediate, NodeArena, NodeId, NodeKind},
    module::ModuleEnv,
    mutability::{MutType, MutVal, MutVar, MutVarKey},
    std::{array::array_type, math::int_type},
    r#type::{FnArgType, FnType, TyVarKey, Type, TypeKind, TypeSubstitution, TypeVar},
    type_scheme::PubTypeConstraint,
    typing_env::{LoopFrame, TypingEnv},
    value::Value,
};

pub type InstSubstitution = (TypeSubstitution, EffectsSubstitution);

impl UnifyKey for TyVarKey {
    type Value = Option<Type>;

    fn index(&self) -> u32 {
        self.name()
    }

    fn from_index(u: u32) -> Self {
        Self::new(u)
    }

    fn tag() -> &'static str {
        "TyVarKey"
    }
}

impl EqUnifyValue for Type {}

impl UnifyKey for MutVarKey {
    type Value = Option<MutVal>;

    fn index(&self) -> u32 {
        self.name()
    }

    fn from_index(u: u32) -> Self {
        Self::new(u)
    }

    fn tag() -> &'static str {
        "MutVarKey"
    }
}

impl EqUnifyValue for MutVal {}

impl UnifyKey for EffectVarKey {
    type Value = Option<EffType>;

    fn index(&self) -> u32 {
        self.name()
    }

    fn from_index(u: u32) -> Self {
        Self::new(u)
    }

    fn tag() -> &'static str {
        "EffectVarKey"
    }
}

/// Effects can always be unified through the union operation
impl UnifyValue for EffType {
    type Error = ena::unify::NoError;

    fn unify_values(a: &Self, b: &Self) -> Result<Self, Self::Error> {
        Ok(a.union(b))
    }
}

/// A constraint on types.
#[derive(Debug, Clone)]
pub enum TypeConstraint {
    SameType {
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    },
    SubType {
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    },
    Pub(PubTypeConstraint),
}

impl FormatWith<ModuleEnv<'_>> for TypeConstraint {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        use TypeConstraint::*;
        match self {
            SameType {
                current, expected, ..
            } => {
                write!(
                    f,
                    "{} = {}",
                    current.format_with(env),
                    expected.format_with(env)
                )
            }
            SubType {
                current, expected, ..
            } => {
                write!(
                    f,
                    "{} ≤ {}",
                    current.format_with(env),
                    expected.format_with(env)
                )
            }
            Pub(constraint) => constraint.fmt_with(f, env),
        }
    }
}

/// A constraint on mutability.
#[derive(Debug, Clone)]
pub enum MutConstraint {
    SameMut {
        current: MutType,
        current_span: Location,
        expected: MutType,
        expected_span: Location,
    },
    MutBeAtLeast {
        current: MutType,
        current_span: Location,
        target: MutType,
        reason_span: Location,
    },
}

impl Display for MutConstraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use MutConstraint::*;
        match self {
            SameMut {
                current, expected, ..
            } => write!(f, "{current} = {expected}"),
            MutBeAtLeast {
                current, target, ..
            } => write!(f, "{current} ≥ {target}"),
        }
    }
}

/// A constraint on effects.
#[derive(Debug, Clone)]
pub enum EffectConstraint {
    SameEffect {
        current: EffType,
        current_span: Location,
        expected: EffType,
        expected_span: Location,
    },
}

impl Display for EffectConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use EffectConstraint::*;
        match self {
            SameEffect {
                current, expected, ..
            } => write!(f, "{current} = {expected}"),
        }
    }
}

/// Whether the unification should target a subtype or the same type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubOrSameType {
    SubType,
    SameType,
}

/// The type inference status, containing the unification table and the constraints
#[derive(Default, Debug)]
pub struct TypeInference {
    ty_unification_table: InPlaceUnificationTable<TyVarKey>,
    ty_constraints: Vec<TypeConstraint>,
    mut_unification_table: InPlaceUnificationTable<MutVarKey>,
    mut_constraints: Vec<MutConstraint>,
    ty_coverage_constraints: Vec<(Location, Type, Vec<Value>)>,
    effect_unification_table: InPlaceUnificationTable<EffectVarKey>,
    effect_constraints: Vec<EffectConstraint>,
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

    pub fn add_ty_coverage_constraint(&mut self, span: Location, ty: Type, values: Vec<Value>) {
        self.ty_coverage_constraints.push((span, ty, values));
    }

    fn instantiate_type_def(
        &mut self,
        type_def_lookup: TypeDefLookupResult,
        use_site: Location,
    ) -> (crate::r#type::TypeDefRef, Type, Type, Option<Ustr>) {
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
        use ir::Node as N;
        use ir::NodeKind as K;

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
                    K::EnvLoad(ir::EnvLoad {
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

        // The lambda uses the same IR arena as the outer function (module's arena).
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
            let node = K::BuildClosure(b(ir::BuildClosure {
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
        use ir::Node as N;
        use ir::NodeKind as K;
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
                    let node = K::EnvLoad(ir::EnvLoad {
                        index: index as u32,
                        id,
                    });
                    (node, local.ty, local.mut_ty, no_effects())
                }
                // Retrieve the trait method from the environment, if it exists
                else if let Some((module_name, _trait_descr)) =
                    env.module_env.get_trait_function(path)?
                {
                    // TODO: add TraitFnImmediate for trait functions
                    let module_text = match module_name {
                        Some(name) => format!(" in module {name}"),
                        None => "current module".to_string(),
                    };
                    return Err(internal_compilation_error!(Unsupported {
                        span: expr_span,
                        reason: format!(
                            "First-class trait method is unsupported: method {path} in {module_text} cannot be used"
                        )
                    }));
                }
                // Retrieve the function from the environment, if it exists
                else if let Some((definition, function, _module_name)) = env.get_function(path)? {
                    let (fn_ty, inst_data, _subst) = definition
                        .ty_scheme
                        .instantiate_with_fresh_vars(self, expr_span, None);
                    let node = K::GetFunction(b(ir::GetFunction {
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
                (node, Type::unit(), MutType::constant(), node_effects)
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
                // No, we emit code to evaluate function
                // Infer the type and mutability of the arguments and collect their code and constraints
                let (args_nodes, args_tys, args_effects) =
                    self.infer_exprs_ret_arg_ty(env, &data.args)?;
                // Allocate a fresh variable for the return type and effects of the function
                let ret_ty = self.fresh_type_var_ty();
                let call_effects = self.fresh_effect_var_ty();
                // Build the function type
                let func_ty =
                    Type::function_type(FnType::new(args_tys, ret_ty, call_effects.clone()));
                // Check the function against its function type
                let func_node_id =
                    self.check_expr(env, data.func, func_ty, MutType::constant(), expr_span)?;
                // Unify effects
                let func_effects = &env.ir_arena[func_node_id].effects;
                let combined_effects =
                    self.make_dependent_effect([&args_effects, func_effects, &call_effects]);
                // Store and return the result
                let node = K::Apply(b(ir::Application {
                    function: func_node_id,
                    arguments: args_nodes,
                }));
                (node, ret_ty, MutType::constant(), combined_effects)
            }
            Block(exprs) => {
                assert!(!exprs.is_empty());
                let env_size = env.cur_locals.len();
                let (nodes, types, effects) = self.infer_exprs_drop_mut(env, exprs)?;
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
                let value_id = self.infer_expr_drop_mut(env, data.value)?;
                let (place_id, place_mut) = self.infer_expr(env, data.place)?;
                let place_span = env.ir_arena[place_id].span;
                self.add_mut_be_at_least_constraint(
                    place_mut,
                    place_span,
                    MutType::mutable(),
                    data.sign_span,
                );
                let value_ty = env.ir_arena[value_id].ty;
                let value_span = env.ir_arena[value_id].span;
                let place_ty = env.ir_arena[place_id].ty;
                self.add_sub_type_constraint(value_ty, value_span, place_ty, place_span);
                let value_effects = &env.ir_arena[value_id].effects;
                let place_effects = &env.ir_arena[place_id].effects;
                let combined_effects = self.make_dependent_effect([value_effects, place_effects]);
                let node = K::Assign(ir::Assignment {
                    place: place_id,
                    value: value_id,
                });
                (node, Type::unit(), MutType::constant(), combined_effects)
            }
            Tuple(exprs) => {
                let (nodes, types, effects) = self.infer_exprs_drop_mut(env, exprs)?;
                let ty = Type::tuple(types);
                let node = if let Some(values) = nodes_as_bare_immediate(env.ir_arena, &nodes) {
                    K::Immediate(Immediate::new(Value::tuple(values)))
                } else {
                    K::Tuple(b(SVec2::from_vec(nodes)))
                };
                (node, ty, MutType::constant(), effects)
            }
            Project(data) => {
                // Generates the following constraints:
                // Project(tuple_expr: T, index) -> V
                //     where T: Coercible<Target = U>, TupleHasField(U, V, index)
                let (tuple_node_id, tuple_mut) = self.infer_expr(env, data.expr)?;
                // Note: tuple_node.ty is T
                let tuple_node_ty = env.ir_arena[tuple_node_id].ty;
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
                let effects = env.ir_arena[tuple_node_id].effects.clone();
                let node = K::Project(tuple_node_id, index);
                (node, element_ty, tuple_mut, effects)
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
                    let mut effects = EffType::empty();
                    let nodes: Vec<_> = layout
                        .iter()
                        .zip(fields.iter())
                        .map(|(layout_field, field)| {
                            assert_eq!(
                                layout_field.0, field.0.0,
                                "Record field names should match the layout",
                            );
                            let node_id = self.check_expr(
                                env,
                                field.1,
                                layout_field.1,
                                MutType::constant(),
                                sp(field.1),
                            )?;
                            effects = effects.union(&env.ir_arena[node_id].effects);
                            Ok(node_id)
                        })
                        .collect::<Result<_, _>>()?;
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
                // Note: record_node.ty is T
                let record_node_ty = env.ir_arena[record_node_id].ty;
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
                let effects = env.ir_arena[record_node_id].effects.clone();
                let node = K::FieldAccess(record_node_id, field);
                (node, element_ty, record_mut, effects)
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
                    // The element type is the first element's type
                    let first_node_id = self.infer_expr_drop_mut(env, exprs[0])?;
                    // Infer the type of the elements and collect their code and constraints
                    let (other_nodes, types, other_effects) =
                        self.infer_exprs_drop_mut(env, &exprs[1..])?;
                    // All elements must be of the first element's type
                    let element_ty = env.ir_arena[first_node_id].ty;
                    for (ty, expr) in types.into_iter().zip(exprs.iter().skip(1)) {
                        self.add_sub_type_constraint(ty, sp(*expr), element_ty, sp(exprs[0]));
                    }
                    // Unify effects
                    let first_effects = &env.ir_arena[first_node_id].effects;
                    let combined_effects =
                        self.make_dependent_effect([first_effects, &other_effects]);
                    // Build the array node and return it
                    let element_nodes: SVec2<_> = once(first_node_id).chain(other_nodes).collect();
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
                    (node, ty, MutType::constant(), combined_effects)
                }
            }
            Index(data) => {
                // New type for the array
                let element_ty = self.fresh_type_var_ty();
                let array_ty = array_type(element_ty);
                // Infer type of the array expression and make sure it is an array
                let (array_node_id, array_expr_mut) = self.infer_expr(env, data.array)?;
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
                let array_effects = &env.ir_arena[array_node_id].effects;
                let index_effects = &env.ir_arena[index_node_id].effects;
                let combined_effects = self.make_dependent_effect([
                    &effect(PrimitiveEffect::Fallible),
                    array_effects,
                    index_effects,
                ]);
                let node = K::Index(array_node_id, index_node_id);
                (node, element_ty, array_expr_mut, combined_effects)
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

    fn infer_static_apply(
        &mut self,
        env: &mut TypingEnv,
        path: &ast::Path,
        path_span: Location,
        args: &[DExprId],
        expr_span: Location,
        arguments_unnamed: UnnamedArg,
    ) -> Result<(NodeKind, Type, MutType, EffType), InternalCompilationError> {
        use ir::Node as N;
        use ir::NodeKind as K;
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
                let (args_node_ids, args_effects) =
                    self.check_exprs(env, args, &inst_fn_ty.args, path_span)?;
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
                let node = K::TraitFnApply(b(ir::TraitFnApplication {
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
                let (args_node_ids, args_effects) =
                    self.check_exprs(env, args, &inst_fn_ty.args, path_span)?;
                // Build and return the function node
                let ret_ty = inst_fn_ty.ret;
                let combined_effects =
                    self.make_dependent_effect([&args_effects, &inst_fn_ty.effects]);
                let node = K::StaticApply(b(ir::StaticApplication {
                    function,
                    function_path: Some(path.clone()),
                    function_span: path_span,
                    arguments: args_node_ids,
                    argument_names,
                    ty: inst_fn_ty,
                    inst_data,
                }));
                (node, ret_ty, MutType::constant(), combined_effects)
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
                let mut effects = EffType::empty();
                let node_ids: Vec<_> = payload_tys
                    .iter()
                    .zip(args.iter())
                    .map(|(ty, arg)| {
                        let node_id = self.check_expr(
                            env,
                            *arg,
                            *ty,
                            MutType::constant(),
                            env.ast_arena[*arg].span,
                        )?;
                        effects = effects.union(&env.ir_arena[node_id].effects);
                        Ok(node_id)
                    })
                    .collect::<Result<_, _>>()?;
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
            } else {
                // Structural variants cannot be paths
                if path.segments.len() > 1 {
                    return Err(internal_compilation_error!(InvalidVariantConstructor {
                        span: path_span,
                    }));
                }
                // If it is not a known function or trait or type def, assume it to be a variant constructor.
                // Build the payload type and node.
                let (payload_node_ids, payload_types, effects) =
                    self.infer_exprs_drop_mut(env, args)?;
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
            },
        )
    }

    fn infer_exprs_drop_mut(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[DExprId],
    ) -> Result<(Vec<NodeId>, Vec<Type>, EffType), InternalCompilationError> {
        let (nodes, tys, effects): (_, _, Vec<_>) = exprs
            .iter()
            .map(|arg| {
                let node_id = self.infer_expr_drop_mut(env, *arg)?;
                let ty = env.ir_arena[node_id].ty;
                let effects = env.ir_arena[node_id].effects.clone();
                Ok::<(NodeId, Type, EffType), InternalCompilationError>((node_id, ty, effects))
            })
            .process_results(|iter| multiunzip(iter))?;

        let combined_effects = self.make_dependent_effect(&effects);
        Ok((nodes, tys, combined_effects))
    }

    fn infer_record(
        &mut self,
        env: &mut TypingEnv,
        fields: &[&RecordField<Desugared>],
    ) -> Result<(NodeKind, Type, EffType), InternalCompilationError> {
        let exprs = fields.iter().map(|(_, expr)| *expr).collect::<Vec<_>>();
        let (node_ids, types, effects) = self.infer_exprs_drop_mut(env, &exprs)?;
        let payload_ty = fields_to_record_type(fields, types);
        let payload_node = if let Some(values) = nodes_as_bare_immediate(env.ir_arena, &node_ids) {
            NodeKind::Immediate(Immediate::new(Value::tuple(values)))
        } else {
            NodeKind::Record(b(SVec2::from_vec(node_ids)))
        };
        Ok((payload_node, payload_ty, effects))
    }

    // fn infer_exprs_drop_mut_zipped(
    //     &mut self,
    //     env: &mut TypingEnv,
    //     exprs: &[DExprId],
    // ) -> Result<(Vec<(ir::Node, Type)>, EffType), InternalCompilationError> {
    //     let mut effects = Vec::with_capacity(exprs.len());
    //     let nodes_and_tys = exprs
    //         .iter()
    //         .map(|arg| {
    //             let node = self.infer_expr_drop_mut(env, *arg)?;
    //             let ty = node.ty;
    //             effects.push(node.effects.clone());
    //             Ok::<(ir::Node, Type), InternalCompilationError>((node, ty))
    //         })
    //         .collect::<Result<Vec<_>, _>>()?;

    //     let combined_effects = self.make_dependent_effect(&effects);
    //     Ok((nodes_and_tys, combined_effects))
    // }

    fn infer_exprs_ret_arg_ty(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[DExprId],
    ) -> Result<(Vec<NodeId>, Vec<FnArgType>, EffType), InternalCompilationError> {
        let (node_ids, tys, effects): (_, _, Vec<_>) = exprs
            .iter()
            .map(|arg| {
                let (node_id, mut_ty) = self.infer_expr(env, *arg)?;
                let ty = env.ir_arena[node_id].ty;
                let effects = env.ir_arena[node_id].effects.clone();
                Ok::<(NodeId, FnArgType, EffType), InternalCompilationError>((
                    node_id,
                    FnArgType::new(ty, mut_ty),
                    effects,
                ))
            })
            .process_results(|iter| multiunzip(iter))?;
        let combined_effects = self.make_dependent_effect(&effects);
        Ok((node_ids, tys, combined_effects))
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
        fields.sort_by(|(name_a, _), (name_b, _)| name_a.0.cmp(&name_b.0));
        Ok(fields)
    }

    fn check_exprs(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[DExprId],
        expected_tys: &[FnArgType],
        expected_span: Location,
    ) -> Result<(Vec<NodeId>, EffType), InternalCompilationError> {
        let (node_ids, effects): (_, Vec<_>) = exprs
            .iter()
            .zip(expected_tys)
            .map(|(arg, arg_ty)| {
                let node_id =
                    self.check_expr(env, *arg, arg_ty.ty, arg_ty.mut_ty, expected_span)?;
                let effects = env.ir_arena[node_id].effects.clone();
                Ok((node_id, effects))
            })
            .process_results(|iter| multiunzip(iter))?;
        let combined_effects = self.make_dependent_effect(&effects);
        Ok((node_ids, combined_effects))
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
        use ir::Node as N;
        use ir::NodeKind as K;

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

#[derive(Debug, Clone)]
struct PendingEffectDependency {
    source: EffType,
    source_span: Location,
    target: EffectVarKey,
    target_span: Location,
}

pub(crate) struct UnifiedTypeInferenceSnapshot {
    ty_unification_table: Snapshot<InPlace<TyVarKey>>,
    mut_unification_table: Snapshot<InPlace<MutVarKey>>,
    effect_unification_table: Snapshot<InPlace<EffectVarKey>>,
    remaining_ty_constraints_len: usize,
    effect_constraints_inv: Vec<PendingEffectDependency>,
}

/// The type inference after unification, with only public constraints remaining
#[derive(Default, Debug)]
pub struct UnifiedTypeInference {
    ty_unification_table: InPlaceUnificationTable<TyVarKey>,
    /// Remaining constraints that cannot be solved, will be part of the resulting type scheme
    remaining_ty_constraints: Vec<PubTypeConstraint>,
    mut_unification_table: InPlaceUnificationTable<MutVarKey>,
    effect_unification_table: InPlaceUnificationTable<EffectVarKey>,
    effect_constraints_inv: Vec<PendingEffectDependency>,
}

impl UnifiedTypeInference {
    pub fn new_with_ty_vars(count: u32) -> Self {
        let mut unified_ty_inf = Self::default();
        unified_ty_inf.add_ty_vars(count);
        unified_ty_inf
    }

    pub(crate) fn fresh_type_var(&mut self) -> TypeVar {
        self.ty_unification_table.new_key(None)
    }

    pub fn add_ty_vars(&mut self, count: u32) {
        for _ in 0..count {
            self.ty_unification_table.new_key(None);
        }
    }

    pub(crate) fn fresh_type_var_subst(&mut self, count: u32) -> TypeSubstitution {
        (0..count)
            .map(|old_var| (TypeVar::new(old_var), Type::variable(self.fresh_type_var())))
            .collect()
    }

    pub(crate) fn snapshot(&mut self) -> UnifiedTypeInferenceSnapshot {
        UnifiedTypeInferenceSnapshot {
            ty_unification_table: self.ty_unification_table.snapshot(),
            mut_unification_table: self.mut_unification_table.snapshot(),
            effect_unification_table: self.effect_unification_table.snapshot(),
            remaining_ty_constraints_len: self.remaining_ty_constraints.len(),
            effect_constraints_inv: self.effect_constraints_inv.clone(),
        }
    }

    pub(crate) fn rollback_to(&mut self, snapshot: UnifiedTypeInferenceSnapshot) {
        self.ty_unification_table
            .rollback_to(snapshot.ty_unification_table);
        self.mut_unification_table
            .rollback_to(snapshot.mut_unification_table);
        self.effect_unification_table
            .rollback_to(snapshot.effect_unification_table);
        self.remaining_ty_constraints
            .truncate(snapshot.remaining_ty_constraints_len);
        self.effect_constraints_inv = snapshot.effect_constraints_inv;
    }

    pub fn unify_type_inference(
        ty_inf: TypeInference,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<Self, InternalCompilationError> {
        let TypeInference {
            ty_unification_table,
            ty_constraints,
            mut_unification_table,
            mut_constraints,
            ty_coverage_constraints,
            effect_unification_table,
            effect_constraints,
        } = ty_inf;
        let mut unified_ty_inf = UnifiedTypeInference {
            ty_unification_table,
            remaining_ty_constraints: vec![],
            mut_unification_table,
            effect_unification_table,
            effect_constraints_inv: Vec::default(),
        };
        let mut remaining_constraints = FxHashSet::default();

        // First, resolve mutability constraints.
        for constraint in mut_constraints {
            use MutConstraint::*;
            match constraint {
                SameMut {
                    current,
                    current_span,
                    expected,
                    expected_span,
                } => {
                    unified_ty_inf.unify_mut_must_be_at_least_or_equal(
                        current,
                        current_span,
                        expected,
                        expected_span,
                        MutabilityMustBeContext::Value,
                        SubOrSameType::SameType,
                    )?;
                }
                MutBeAtLeast {
                    current,
                    current_span,
                    target,
                    reason_span,
                } => {
                    unified_ty_inf.unify_mut_must_be_at_least_or_equal(
                        current,
                        current_span,
                        target,
                        reason_span,
                        MutabilityMustBeContext::Value,
                        SubOrSameType::SubType,
                    )?;
                }
            }
        }

        // Make the remaining mutability variables constant.
        for var in 0..unified_ty_inf.mut_unification_table.len() {
            let var = MutVarKey::new(var as u32);
            if unified_ty_inf
                .mut_unification_table
                .probe_value(var)
                .is_none()
            {
                unified_ty_inf
                    .mut_unification_table
                    .unify_var_value(var, Some(MutVal::constant()))
                    .expect("Cannot unify free mutability variable");
            }
        }

        // Then, solve all type equalities.
        for constraint in ty_constraints {
            use TypeConstraint::*;
            match constraint {
                SameType {
                    current,
                    current_span,
                    expected,
                    expected_span,
                } => unified_ty_inf.unify_same_type(
                    current,
                    current_span,
                    expected,
                    expected_span,
                )?,
                SubType {
                    current,
                    current_span,
                    expected,
                    expected_span,
                } => {
                    unified_ty_inf.unify_sub_type(current, current_span, expected, expected_span)?
                }
                Pub(cst) => {
                    remaining_constraints.insert(cst);
                }
            }
        }

        // Then, solve all effect equalities.
        for constraint in effect_constraints {
            use EffectConstraint::*;
            match constraint {
                SameEffect {
                    current,
                    current_span,
                    expected,
                    expected_span,
                } => unified_ty_inf.unify_same_effect(
                    current,
                    current_span,
                    expected,
                    expected_span,
                )?,
            }
        }

        // Then, solve type coverage constraints
        for (span, ty, values) in ty_coverage_constraints {
            let ty = unified_ty_inf.normalize_type(ty);
            let all_values = ty.data().all_values().ok_or_else(|| {
                internal_compilation_error!(TypeValuesCannotBeEnumerated { span, ty })
            })?;
            let mut complete = true;
            for ty_value in all_values {
                if !values.contains(&ty_value) {
                    complete = false;
                    break;
                }
            }
            if complete {
                continue;
            }
            return Err(internal_compilation_error!(NonExhaustivePattern {
                span,
                ty
            }));
        }

        // Then, solve other constraints.
        if !remaining_constraints.is_empty() {
            loop {
                // Loop as long as we make progress.

                // Perform simplification for algebraic data type constraints.
                // Check for incompatible constraints as well.
                let mut tuples_at_index_is: FxHashMap<Type, FxHashMap<usize, (Type, Location)>> =
                    FxHashMap::default();
                let mut records_field_is: FxHashMap<Type, FxHashMap<Ustr, (Type, Location)>> =
                    FxHashMap::default();
                let mut variants_are: FxHashMap<Type, FxHashMap<Ustr, (Type, Location)>> =
                    FxHashMap::default();
                let mut have_traits: FxHashMap<(TraitRef, Vec<Type>), (Vec<Type>, Location)> =
                    FxHashMap::default();
                for constraint in &remaining_constraints {
                    use PubTypeConstraint::*;
                    match constraint {
                        TupleAtIndexIs {
                            tuple_ty,
                            tuple_span,
                            index,
                            index_span,
                            element_ty,
                        } => {
                            let tuple_ty = unified_ty_inf.normalize_type(*tuple_ty);
                            let element_ty = unified_ty_inf.normalize_type(*element_ty);
                            // tuple_span and index_span *must* originate from the same module
                            let span =
                                Location::fuse([tuple_span.use_site, index_span.use_site]).unwrap();
                            if let Some(variant) = variants_are.get(&tuple_ty) {
                                let variant_span = variant.iter().next().unwrap().1.1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::Variant,
                                    variant_span,
                                    ADTAccessType::TupleProject,
                                    span,
                                ));
                            } else if let Some(record) = records_field_is.get(&tuple_ty) {
                                let record_span = record.iter().next().unwrap().1.1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::RecordAccess,
                                    record_span,
                                    ADTAccessType::TupleProject,
                                    span,
                                ));
                            } else if let Some(tuple) = tuples_at_index_is.get_mut(&tuple_ty) {
                                if let Some((expected_ty, expected_span)) = tuple.get(index) {
                                    unified_ty_inf.unify_same_type(
                                        element_ty,
                                        span,
                                        *expected_ty,
                                        *expected_span,
                                    )?;
                                } else {
                                    tuple.insert(*index, (element_ty, span));
                                }
                            } else {
                                let tuple = FxHashMap::from_iter([(*index, (element_ty, span))]);
                                tuples_at_index_is.insert(tuple_ty, tuple);
                            }
                        }
                        RecordFieldIs {
                            record_ty,
                            record_span,
                            field,
                            field_span,
                            element_ty,
                        } => {
                            let record_ty = unified_ty_inf.normalize_type(*record_ty);
                            let element_ty = unified_ty_inf.normalize_type(*element_ty);
                            // record_span and field_span *must* originate from the same module
                            let span = Location::fuse([record_span.use_site, field_span.use_site])
                                .unwrap();
                            if let Some(variant) = variants_are.get(&record_ty) {
                                let variant_span = variant.iter().next().unwrap().1.1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::Variant,
                                    variant_span,
                                    ADTAccessType::TupleProject,
                                    span,
                                ));
                            } else if let Some(tuple) = tuples_at_index_is.get(&record_ty) {
                                let tuple_span = tuple.iter().next().unwrap().1.1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::TupleProject,
                                    tuple_span,
                                    ADTAccessType::RecordAccess,
                                    span,
                                ));
                            } else if let Some(record) = records_field_is.get_mut(&record_ty) {
                                if let Some((expected_ty, expected_span)) = record.get(field) {
                                    unified_ty_inf.unify_same_type(
                                        element_ty,
                                        span,
                                        *expected_ty,
                                        *expected_span,
                                    )?;
                                } else {
                                    record.insert(*field, (element_ty, span));
                                }
                            } else {
                                let record = FxHashMap::from_iter([(*field, (element_ty, span))]);
                                records_field_is.insert(record_ty, record);
                            }
                        }
                        TypeHasVariant {
                            variant_ty,
                            variant_span,
                            tag,
                            payload_ty,
                            payload_span,
                        } => {
                            let variant_ty = unified_ty_inf.normalize_type(*variant_ty);
                            let payload_ty = unified_ty_inf.normalize_type(*payload_ty);
                            // We observed that sometimes variant_span and payload_span come from different modules.
                            // So we just use variant_span here.
                            let span = variant_span.use_site;
                            if let Some(tuple) = tuples_at_index_is.get(&variant_ty) {
                                let index_span = tuple.iter().next().unwrap().1.1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::TupleProject,
                                    index_span,
                                    ADTAccessType::Variant,
                                    span,
                                ));
                            } else if let Some(record) = records_field_is.get(&variant_ty) {
                                let record_span = record.iter().next().unwrap().1.1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::RecordAccess,
                                    record_span,
                                    ADTAccessType::Variant,
                                    span,
                                ));
                            } else if let Some(variants) = variants_are.get_mut(&variant_ty) {
                                if let Some((expected_ty, expected_span)) = variants.get(tag) {
                                    unified_ty_inf.unify_same_type(
                                        payload_ty,
                                        payload_span.use_site,
                                        *expected_ty,
                                        *expected_span,
                                    )?;
                                } else {
                                    variants.insert(*tag, (payload_ty, span));
                                }
                            } else {
                                let variant = FxHashMap::from_iter([(
                                    *tag,
                                    (payload_ty, payload_span.use_site),
                                )]);
                                variants_are.insert(variant_ty, variant);
                            }
                        }
                        HaveTrait {
                            trait_ref,
                            input_tys,
                            output_tys,
                            span,
                        } => {
                            let input_types = unified_ty_inf.normalize_types(input_tys);
                            let output_types = unified_ty_inf.normalize_types(output_tys);
                            let key = (trait_ref.clone(), input_types);
                            if let Some(have_trait) = have_traits.get(&key) {
                                assert_eq!(have_trait.0.len(), output_types.len());
                                for (expected, actual) in
                                    have_trait.0.iter().zip(output_types.iter())
                                {
                                    unified_ty_inf.unify_same_type(
                                        *actual,
                                        span.use_site,
                                        *expected,
                                        have_trait.1,
                                    )?;
                                }
                            } else {
                                have_traits.insert(key, (output_types, span.use_site));
                            }
                        }
                    }
                }

                // Perform unification.
                let constraints = remaining_constraints.into_iter().collect::<Vec<_>>();
                let old_constraint_count = constraints.len();
                let old_constraint_var_count = total_constraints_var_count(constraints.iter());
                let is_ty_adt = |ty| {
                    tuples_at_index_is.contains_key(&ty)
                        || records_field_is.contains_key(&ty)
                        || variants_are.contains_key(&ty)
                };
                remaining_constraints = unified_ty_inf
                    .unify_constraint_pass(&constraints, is_ty_adt, trait_solver, arena)?
                    .into_iter()
                    .collect();
                let new_constraint_var_count =
                    total_constraints_var_count(remaining_constraints.iter());

                // Break if no progress was made
                if remaining_constraints.len() == old_constraint_count
                    && new_constraint_var_count == old_constraint_var_count
                {
                    break;
                }
            }
        }

        // Create minimalist types for orphan variant constraints.
        // FIXME: something is missing here
        // remaining_constraints = unified_ty_inf.simplify_variant_constraints(remaining_constraints);

        // Flatten inverted effect constraints into normal constraints
        let effect_constraints_inv = mem::take(&mut unified_ty_inf.effect_constraints_inv);
        for dep in effect_constraints_inv {
            unified_ty_inf.expand_inv_effect_dep(dep)?;
        }

        // FIXME: think whether we should have an intermediate struct without the remaining_constraints in it.
        unified_ty_inf.remaining_ty_constraints = remaining_constraints.into_iter().collect();
        Ok(unified_ty_inf)
    }

    /// Substitute the remaining constraints using the current unification tables,
    /// storing the normalized constraints back into self.
    pub fn normalize_remaining_constraints(&mut self) {
        let constraints = mem::take(&mut self.remaining_ty_constraints);
        self.remaining_ty_constraints = self.substitute_in_constraints(&constraints);
    }

    /// Borrow the remaining constraints. Call `normalize_remaining_constraints`
    /// first if you need them fully substituted.
    pub fn remaining_constraints(&self) -> &[PubTypeConstraint] {
        &self.remaining_ty_constraints
    }

    /// Extract the remaining constraints from self.
    pub fn take_constraints(&mut self) -> Vec<PubTypeConstraint> {
        mem::take(&mut self.remaining_ty_constraints)
    }

    /// Re-solve remaining constraints after defaulting has added new information
    /// to the unification tables. Constraints that are now solvable are removed.
    pub fn resolve_remaining_constraints(
        &mut self,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<(), InternalCompilationError> {
        loop {
            self.normalize_remaining_constraints();
            let constraints = mem::take(&mut self.remaining_ty_constraints);
            let old_count = constraints.len();
            let old_var_count = total_constraints_var_count(constraints.iter());
            self.remaining_ty_constraints =
                self.unify_constraint_pass(&constraints, |_| false, trait_solver, arena)?;
            let new_var_count = total_constraints_var_count(self.remaining_ty_constraints.iter());
            if self.remaining_ty_constraints.len() == old_count && new_var_count == old_var_count {
                break;
            }
        }
        Ok(())
    }

    /// Default variant constraints in the provided boundary by unifying
    /// eligible type variables with minimalist variant types.
    pub fn default_orphan_variants_in_constraints(
        &mut self,
        constraints: &[PubTypeConstraint],
    ) -> Result<(), InternalCompilationError> {
        use crate::type_scheme::VariantConstraint;

        // First, collect the type variables that are invalid for variant simplification.
        let mut invalid_ty_vars = FxHashSet::<TypeVar>::default();
        for constraint in constraints {
            match constraint {
                PubTypeConstraint::TypeHasVariant { payload_ty, .. } => {
                    invalid_ty_vars.extend(payload_ty.inner_ty_vars());
                }
                PubTypeConstraint::HaveTrait { .. } => {}
                _ => {
                    invalid_ty_vars.extend(constraint.inner_ty_vars());
                }
            }
        }

        // Collect variant constraints grouped by type variable.
        let mut variants: FxHashMap<TypeVar, VariantConstraint> = FxHashMap::default();
        let mut variant_spans: FxHashMap<TypeVar, Location> = FxHashMap::default();
        for constraint in constraints {
            if let PubTypeConstraint::TypeHasVariant {
                variant_ty,
                variant_span,
                tag,
                payload_ty,
                ..
            } = constraint
            {
                if let Some(ty_var) = variant_ty.data().as_variable() {
                    if !invalid_ty_vars.contains(ty_var) {
                        let existing = variants
                            .entry(*ty_var)
                            .or_default()
                            .insert(*tag, *payload_ty);
                        assert!(existing.is_none(), "Duplicate variant constraint for {tag}");
                        variant_spans
                            .entry(*ty_var)
                            .or_insert(variant_span.use_site);
                    }
                }
            }
        }

        // Unify each variable with its minimalist variant type.
        for (ty_var, variant) in variants {
            let variant_ty = Type::variant(variant.into_iter().collect::<Vec<_>>());
            let span = variant_spans[&ty_var];
            self.unify_same_type(Type::variable(ty_var), span, variant_ty, span)?;
        }
        Ok(())
    }

    /// Default Num-constrained type variables to int or float by unifying
    /// directly in the unification table.
    pub fn default_num_types(
        &mut self,
        constraints: &[PubTypeConstraint],
        trait_solver: &mut TraitSolver<'_>,
        _arena: &mut NodeArena,
    ) -> Result<(), InternalCompilationError> {
        if constraints.is_empty() {
            return Ok(());
        }

        use crate::module::ConcreteTraitImplKey;
        use crate::std::math::{NUM_TRAIT, float_type, int_type};

        let default_tys = [int_type(), float_type()];
        let mut progress = true;
        while progress {
            progress = false;

            // Re-substitute orphan constraints to see current state of type variables.
            let subst_constraints = self.substitute_in_constraints(constraints);

            // First, collect invalid type variables and Num type variables.
            let mut invalid_ty_vars = FxHashSet::<TypeVar>::default();
            let mut num_ty_vars = FxHashSet::<TypeVar>::default();
            for constraint in &subst_constraints {
                if let PubTypeConstraint::HaveTrait {
                    trait_ref,
                    input_tys,
                    output_tys,
                    ..
                } = constraint
                {
                    assert!(!input_tys.is_empty());
                    if *trait_ref == *NUM_TRAIT {
                        let maybe_ty_var = input_tys[0].data().as_variable().cloned();
                        if let Some(ty_var) = maybe_ty_var {
                            num_ty_vars.insert(ty_var);
                        }
                    }
                    let input_ty_vars: FxHashSet<_> =
                        input_tys.iter().flat_map(|ty| ty.inner_ty_vars()).collect();
                    invalid_ty_vars.extend(
                        output_tys
                            .iter()
                            .flat_map(|ty| ty.inner_ty_vars())
                            .filter(|ty_var| !input_ty_vars.contains(ty_var)),
                    );
                } else if !constraint.is_type_has_variant() {
                    invalid_ty_vars.extend(constraint.inner_ty_vars());
                }
            }

            // Determine defaults for Num-constrained type variables.
            let mut defaulted_ty_vars = FxHashMap::<TypeVar, usize>::default();
            for constraint in &subst_constraints {
                if let PubTypeConstraint::HaveTrait {
                    trait_ref,
                    input_tys,
                    output_tys,
                    ..
                } = constraint
                {
                    if input_tys.len() > 1 || !output_tys.is_empty() {
                        continue;
                    }
                    let maybe_ty_var = input_tys[0].data().as_variable().cloned();
                    if let Some(ty_var) = maybe_ty_var {
                        if invalid_ty_vars.contains(&ty_var) {
                            continue;
                        }
                        if !num_ty_vars.contains(&ty_var) {
                            continue;
                        }
                        let mut default_index =
                            defaulted_ty_vars.get(&ty_var).copied().unwrap_or(0);
                        while default_index < default_tys.len() {
                            let key = ConcreteTraitImplKey::new(
                                trait_ref.clone(),
                                vec![default_tys[default_index]],
                            );
                            if trait_solver.has_concrete_impl(&key) {
                                break;
                            }
                            default_index += 1;
                        }
                        defaulted_ty_vars.insert(ty_var, default_index);
                    }
                }
            }

            if defaulted_ty_vars.is_empty() {
                break;
            }

            // Unify each defaulted variable with its default type.
            let span = constraints[0].use_site();
            for (ty_var, default_index) in &defaulted_ty_vars {
                if let Some(default_ty) = default_tys.get(*default_index) {
                    // Check if the variable is already resolved to something else.
                    let current = self.lookup_type_var(*ty_var);
                    if current.data().as_variable().is_some() {
                        self.unify_same_type(Type::variable(*ty_var), span, *default_ty, span)?;
                        progress = true;
                    }
                }
            }
        }
        Ok(())
    }

    /// For expressions, try to default remaining unconstrained type variables to int.
    /// This handles cases like `concat([], [])` where the element type has no Num constraint
    /// but can be safely defaulted to int if all trait constraints are satisfiable.
    pub fn default_unconstrained_expr_ty_vars(
        &mut self,
        expr_ty: Type,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> bool {
        use crate::std::math::int_type;

        let mut progress = false;

        // Re-substitute the expression type through current tables.
        let substituted_ty = self.substitute_in_type(expr_ty);
        let remaining_vars: Vec<TypeVar> = substituted_ty
            .inner_ty_vars()
            .into_iter()
            .filter(|v| {
                // Only consider variables that are still unresolved.
                self.lookup_type_var(*v).data().as_variable().is_some()
            })
            .collect();

        // Get current normalized constraints.
        self.normalize_remaining_constraints();
        let subst_constraints = self.remaining_constraints().to_vec();

        for ty_var in remaining_vars {
            // Only default if this variable appears in at least one remaining constraint.
            let has_constraint = subst_constraints
                .iter()
                .any(|c| c.contains_any_type_var(ty_var));
            if !has_constraint {
                continue;
            }

            // Check if all constraints mentioning this variable are satisfied with int.
            let mut all_satisfied = true;
            let trial_subst: InstSubstitution = (
                FxHashMap::from_iter([(ty_var, int_type())]),
                FxHashMap::default(),
            );
            for c in &subst_constraints {
                if !c.contains_any_type_var(ty_var) {
                    continue;
                }
                let inst_c = c.instantiate(&trial_subst);
                if let PubTypeConstraint::HaveTrait {
                    trait_ref,
                    input_tys,
                    span,
                    ..
                } = &inst_c
                {
                    if input_tys.iter().all(Type::is_constant)
                        && trait_solver
                            .solve_impl(trait_ref, input_tys, span.use_site, arena)
                            .is_err()
                    {
                        all_satisfied = false;
                        break;
                    }
                }
            }

            if all_satisfied {
                let span = subst_constraints
                    .iter()
                    .find(|c| c.contains_any_type_var(ty_var))
                    .expect("there must be a relevant constraint for expr defaulting")
                    .use_site();
                if self
                    .unify_same_type(Type::variable(ty_var), span, int_type(), span)
                    .is_ok()
                {
                    progress = true;
                }
            }
        }

        progress
    }

    /// Repeatedly default the provided constraints and re-solve remaining
    /// constraints until reaching a fixed point.
    ///
    /// This is boundary-aware: only the supplied constraints participate in
    /// variant and numeric defaulting.
    /// If `root_ty` is provided, expression-only unconstrained defaulting is
    /// also attempted for variables visible from that root type.
    pub fn resolve_specific_defaults_to_fixed_point(
        &mut self,
        mut constraints: Vec<PubTypeConstraint>,
        root_ty: Option<Type>,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<(), InternalCompilationError> {
        let expr_var_count = |this: &mut Self| {
            root_ty
                .map(|root_ty| {
                    this.substitute_in_type(root_ty)
                        .inner_ty_vars()
                        .into_iter()
                        .filter(|v| this.lookup_type_var(*v).data().as_variable().is_some())
                        .count()
                })
                .unwrap_or(0)
        };
        let constraints_var_count = |constraints: &[PubTypeConstraint]| {
            constraints
                .iter()
                .map(|constraint| constraint.inner_ty_vars().len())
                .sum::<usize>()
        };

        loop {
            let old_expr_var_count = expr_var_count(self);
            let old_constraints_var_count = constraints_var_count(&constraints);

            self.default_orphan_variants_in_constraints(&constraints)?;
            self.default_num_types(&constraints, trait_solver, arena)?;
            self.resolve_remaining_constraints(trait_solver, arena)?;
            let unconstrained_progress = root_ty
                .map(|root_ty| {
                    self.default_unconstrained_expr_ty_vars(root_ty, trait_solver, arena)
                })
                .unwrap_or(false);

            constraints = self.substitute_in_constraints(&constraints);

            let new_expr_var_count = expr_var_count(self);
            let new_constraints_var_count = constraints_var_count(&constraints);

            if !unconstrained_progress
                && new_expr_var_count == old_expr_var_count
                && new_constraints_var_count == old_constraints_var_count
            {
                break;
            }
        }

        self.normalize_remaining_constraints();

        Ok(())
    }

    /// Repeatedly default expression constraints and re-solve remaining constraints
    /// until reaching a fixed point.
    pub fn resolve_expr_defaults_to_fixed_point(
        &mut self,
        expr_ty: Type,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<(), InternalCompilationError> {
        let orphan_constraints = self.remaining_constraints().to_vec();
        self.resolve_specific_defaults_to_fixed_point(
            orphan_constraints,
            Some(expr_ty),
            trait_solver,
            arena,
        )
    }

    fn normalize_type(&mut self, ty: Type) -> Type {
        substitute_type(ty, &mut NormalizeTypes(self))
    }

    fn normalize_types(&mut self, tys: &[Type]) -> Vec<Type> {
        substitute_types(tys, &mut NormalizeTypes(self))
    }

    fn normalize_mut_type(&mut self, mut_ty: MutType) -> MutType {
        NormalizeTypes(self).substitute_mut_type(mut_ty)
    }

    pub fn unify_fn_arg_effects(&mut self, fn_type: &FnType) {
        for arg in &fn_type.args {
            if let Some(fn_arg) = arg.ty.data().as_function() {
                let mut first_var = None;
                fn_arg.effects.iter().for_each(|eff| {
                    if let Some(var) = eff.as_variable() {
                        if let Some(first_var) = first_var {
                            self.effect_unification_table.union(first_var, *var);
                        } else {
                            first_var = Some(*var);
                        }
                    }
                });
            }
        }
    }

    pub fn effect_unioned(&mut self, var: EffectVar) -> Option<EffectVar> {
        let root = self.effect_unification_table.find(var);
        if root != var { Some(root) } else { None }
    }

    pub fn unify_sub_type(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.unify_sub_or_same_type(
            current,
            current_span,
            expected,
            expected_span,
            SubOrSameType::SubType,
        )
    }

    pub fn unify_same_type(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.unify_sub_or_same_type(
            current,
            current_span,
            expected,
            expected_span,
            SubOrSameType::SameType,
        )
    }

    fn unify_sub_or_same_type(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
        sub_or_same: SubOrSameType,
    ) -> Result<(), InternalCompilationError> {
        if current == expected {
            return Ok(());
        }
        let current_ty = self.normalize_type(current);
        let expected_ty = self.normalize_type(expected);
        if current_ty == expected_ty {
            return Ok(());
        }
        let cur_data = { current_ty.data().clone() };
        let exp_data = { expected_ty.data().clone() };
        use SubOrSameType::*;
        use TypeKind::*;
        match (cur_data, exp_data) {
            (Never, _) => Ok(()),
            (_, Never) => Ok(()),
            (Variable(cur), Variable(exp)) => self
                .ty_unification_table
                .unify_var_var(cur, exp)
                .map_err(|_| {
                    internal_compilation_error!(TypeMismatch {
                        current_ty,
                        current_span,
                        expected_ty,
                        expected_span,
                        sub_or_same: SameType,
                    })
                }),
            (Variable(var), _) => {
                self.unify_type_variable(var, current_span, expected_ty, expected_span)
            }
            (_, Variable(var)) => {
                self.unify_type_variable(var, expected_span, current_ty, current_span)
            }
            (Native(cur), Native(exp)) => {
                if cur.bare_ty != exp.bare_ty {
                    return Err(internal_compilation_error!(TypeMismatch {
                        current_ty,
                        current_span,
                        expected_ty,
                        expected_span,
                        sub_or_same: SameType,
                    }));
                }
                for (cur_arg_ty, exp_arg_ty) in
                    cur.arguments.into_iter().zip(exp.arguments.into_iter())
                {
                    self.unify_sub_or_same_type(
                        cur_arg_ty,
                        current_span,
                        exp_arg_ty,
                        expected_span,
                        sub_or_same,
                    )?;
                }
                Ok(())
            }
            (Variant(cur), Variant(exp)) => {
                if cur.len() != exp.len() {
                    return Err(internal_compilation_error!(TypeMismatch {
                        current_ty,
                        current_span,
                        expected_ty,
                        expected_span,
                        sub_or_same,
                    }));
                }
                for (cur_variant, exp_variant) in cur.into_iter().zip(exp.into_iter()) {
                    if cur_variant.0 != exp_variant.0 {
                        return Err(internal_compilation_error!(TypeMismatch {
                            current_ty,
                            current_span,
                            expected_ty,
                            expected_span,
                            sub_or_same,
                        }));
                    }
                    self.unify_sub_or_same_type(
                        cur_variant.1,
                        current_span,
                        exp_variant.1,
                        expected_span,
                        sub_or_same,
                    )?;
                }
                Ok(())
            }
            (Tuple(cur), Tuple(exp)) => {
                if cur.len() != exp.len() {
                    return Err(internal_compilation_error!(TypeMismatch {
                        current_ty,
                        current_span,
                        expected_ty,
                        expected_span,
                        sub_or_same,
                    }));
                }
                for (cur_el_ty, exp_el_ty) in cur.into_iter().zip(exp.into_iter()) {
                    self.unify_sub_or_same_type(
                        cur_el_ty,
                        current_span,
                        exp_el_ty,
                        expected_span,
                        sub_or_same,
                    )?;
                }
                Ok(())
            }
            (Record(cur), Record(exp)) => {
                for (cur_field, exp_field) in cur.into_iter().zip(exp) {
                    if cur_field.0 != exp_field.0 {
                        return Err(internal_compilation_error!(TypeMismatch {
                            current_ty,
                            current_span,
                            expected_ty,
                            expected_span,
                            sub_or_same,
                        }));
                    }
                    self.unify_sub_or_same_type(
                        cur_field.1,
                        current_span,
                        exp_field.1,
                        expected_span,
                        sub_or_same,
                    )?;
                }
                Ok(())
            }
            (Function(cur), Function(exp)) => {
                if cur.args.len() != exp.args.len() {
                    return Err(internal_compilation_error!(TypeMismatch {
                        current_ty,
                        current_span,
                        expected_ty,
                        expected_span,
                        sub_or_same,
                    }));
                }
                for ((index, cur_arg), exp_arg) in cur.args.iter().enumerate().zip(exp.args.iter())
                {
                    // Contravariance of argument types.
                    self.unify_mut_must_be_at_least_or_equal(
                        exp_arg.mut_ty,
                        current_span,
                        cur_arg.mut_ty,
                        expected_span,
                        MutabilityMustBeContext::FnTypeArg(index),
                        sub_or_same,
                    )?;
                    self.unify_sub_or_same_type(
                        exp_arg.ty,
                        current_span,
                        cur_arg.ty,
                        expected_span,
                        sub_or_same,
                    )?;
                }
                // Covariant effects.
                self.add_effect_dep(&cur.effects, current_span, &exp.effects, expected_span)?;
                // Covariance of return type.
                self.unify_sub_or_same_type(
                    cur.ret,
                    current_span,
                    exp.ret,
                    expected_span,
                    sub_or_same,
                )
            }
            (Named(cur), Named(exp)) => {
                if cur.def != exp.def {
                    return Err(internal_compilation_error!(NamedTypeMismatch {
                        current_decl: cur.def,
                        current_span,
                        expected_decl: exp.def,
                        expected_span,
                    }));
                }
                assert_eq!(
                    cur.params.len(),
                    exp.params.len(),
                    "A Named type must have the same number of arguments for all its instances"
                );
                for (cur_el_ty, exp_el_ty) in cur.params.into_iter().zip(exp.params.into_iter()) {
                    self.unify_sub_or_same_type(
                        cur_el_ty,
                        current_span,
                        exp_el_ty,
                        expected_span,
                        sub_or_same,
                    )?;
                }
                Ok(())
            }
            _ => Err(internal_compilation_error!(TypeMismatch {
                current_ty,
                current_span,
                expected_ty,
                expected_span,
                sub_or_same: SameType,
            })),
        }
    }

    fn unify_type_variable(
        &mut self,
        var: TypeVar,
        var_span: Location,
        ty: Type,
        ty_span: Location,
    ) -> Result<(), InternalCompilationError> {
        if ty.contains_any_type_var(var) {
            Err(internal_compilation_error!(InfiniteType(var, ty, ty_span)))
        } else {
            // If the type is a function type with concrete (non-variable) effects,
            // we need to generalize those effects to preserve effect polymorphism.
            // Otherwise, the concrete effects would be "baked in" and the function
            // parameter couldn't contribute its effect variable to the parent function.
            let ty = self.generalize_function_effects(ty);
            self.ty_unification_table
                .unify_var_value(var, Some(ty))
                .map_err(|(l, r)| {
                    internal_compilation_error!(TypeMismatch {
                        current_ty: l,
                        current_span: var_span,
                        expected_ty: r,
                        expected_span: ty_span,
                        sub_or_same: SubOrSameType::SameType
                    })
                })
        }
    }

    /// Generalize concrete effects in a function type to effect variables.
    /// This is needed when unifying a type variable with a function type,
    /// to preserve effect polymorphism.
    fn generalize_function_effects(&mut self, ty: Type) -> Type {
        use TypeKind::*;
        let ty_data = ty.data();
        match &*ty_data {
            Function(fn_ty) => {
                let fn_ty = fn_ty.clone();
                drop(ty_data);
                // Check if the function has any non-variable effects
                let has_primitive_effects = fn_ty.effects.iter().any(|e| e.is_primitive());
                if has_primitive_effects {
                    // Create a fresh effect variable
                    let fresh_eff_var = self.effect_unification_table.new_key(None);
                    // Add the concrete effects as dependencies to this fresh variable
                    // This is done through the inverted constraints mechanism
                    for eff in fn_ty.effects.iter() {
                        if eff.is_primitive() {
                            self.effect_constraints_inv.push(PendingEffectDependency {
                                source: EffType::single(*eff),
                                source_span: Location::new_synthesized(),
                                target: fresh_eff_var,
                                target_span: Location::new_synthesized(),
                            });
                        } else if let Some(var) = eff.as_variable() {
                            // Also union any existing effect variables
                            self.effect_unification_table.union(fresh_eff_var, *var);
                        }
                    }
                    // Create a new function type with the fresh effect variable
                    let new_fn_ty = FnType::new(
                        fn_ty.args.clone(),
                        fn_ty.ret,
                        EffType::single_variable(fresh_eff_var),
                    );
                    Type::function_type(new_fn_ty)
                } else {
                    ty
                }
            }
            _ => {
                drop(ty_data);
                ty
            }
        }
    }

    fn unify_tuple_project(
        &mut self,
        tuple_ty: Type,
        tuple_span: Location,
        index: usize,
        index_span: Location,
        element_ty: Type,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        let tuple_ty = self.normalize_type(tuple_ty);
        let element_ty = self.normalize_type(element_ty);
        let tuple_data = { tuple_ty.data().clone() };
        match tuple_data {
            // A type variable may or may not be a tuple, defer the unification
            TypeKind::Variable(_) => Ok(Some(PubTypeConstraint::new_tuple_at_index_is(
                tuple_ty, tuple_span, index, index_span, element_ty,
            ))),
            // A tuple, verify length and element type
            TypeKind::Tuple(tys) => {
                if let Some(ty) = tys.get(index) {
                    self.unify_same_type(*ty, tuple_span, element_ty, index_span)?;
                    Ok(None)
                } else {
                    Err(internal_compilation_error!(InvalidTupleIndex {
                        index,
                        index_span,
                        tuple_length: tys.len(),
                        tuple_span,
                    }))
                }
            }
            // Not a tuple, error
            _ => Err(internal_compilation_error!(InvalidTupleProjection {
                expr_ty: tuple_ty,
                expr_span: tuple_span,
                index_span,
            })),
        }
    }

    fn unify_record_field_access(
        &mut self,
        record_ty: Type,
        record_span: Location,
        field: Ustr,
        field_span: Location,
        element_ty: Type,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        let record_ty = self.normalize_type(record_ty);
        let element_ty = self.normalize_type(element_ty);
        let record_data = { record_ty.data().clone() };
        match record_data {
            // A type variable may or may not be a tuple, defer the unification
            TypeKind::Variable(_) => Ok(Some(PubTypeConstraint::new_record_field_is(
                record_ty,
                record_span,
                field,
                field_span,
                element_ty,
            ))),
            // A record, verify element type
            TypeKind::Record(tys) => {
                if let Some(ty) = tys
                    .iter()
                    .find_map(|(name, ty)| if *name == field { Some(*ty) } else { None })
                {
                    self.unify_same_type(ty, record_span, element_ty, field_span)?;
                    Ok(None)
                } else {
                    Err(internal_compilation_error!(InvalidRecordField {
                        field_span,
                        record_ty,
                        record_span,
                    }))
                }
            }
            // Not a record, error
            _ => Err(internal_compilation_error!(InvalidRecordFieldAccess {
                record_ty,
                record_span,
                field_span,
            })),
        }
    }

    fn unify_type_has_variant(
        &mut self,
        ty: Type,
        variant_span: Location,
        tag: Ustr,
        payload_ty: Type,
        payload_span: Location,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        let ty = self.normalize_type(ty);
        let payload_ty = self.normalize_type(payload_ty);
        let data = { ty.data().clone() };
        match data {
            // A type variable may or may not be a variant, defer the unification
            TypeKind::Variable(_) => Ok(Some(PubTypeConstraint::new_type_has_variant(
                ty,
                variant_span,
                tag,
                payload_ty,
                payload_span,
            ))),
            // A variant, verify payload type
            TypeKind::Variant(variants) => {
                if let Some(ty) = variants
                    .iter()
                    .find_map(|(name, ty)| if *name == tag { Some(ty) } else { None })
                {
                    self.unify_same_type(*ty, payload_span, payload_ty, payload_span)?;
                    Ok(None)
                } else {
                    Err(internal_compilation_error!(InvalidVariantName {
                        name: payload_span,
                        ty,
                        valid: ()
                    }))
                }
            }
            // Not a variant, error
            _ => Err(internal_compilation_error!(InvalidVariantType {
                name: payload_span,
                ty,
            })),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn unify_have_trait(
        &mut self,
        trait_ref: TraitRef,
        input_tys: &[Type],
        output_tys: &[Type],
        span: Location,
        assumptions: &[&PubTypeConstraint],
        is_ty_adt: impl Fn(Type) -> bool,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        let input_tys = self.normalize_types(input_tys);
        let output_tys = self.normalize_types(output_tys);

        // Look for the special case of a Repr trait constraint where the target
        // is either definitely not a named type or is a tuple, a record or a variant.
        // This is needed to avoid creating functions where tuples and records would
        // unify indirectly through the Repr constraint, which could never be instantiated.
        if trait_ref == *REPR_TRAIT {
            let input_ty = input_tys[0];
            let ty_data = input_ty.data();
            let is_known_non_named_ty = !ty_data.is_named() && !ty_data.is_variable();
            let unify_to_ty = if ty_data.is_named() {
                let named = ty_data.as_named().unwrap().clone();
                drop(ty_data);
                Some(named.instantiated_shape())
            } else if is_known_non_named_ty || is_ty_adt(input_ty) {
                drop(ty_data);
                Some(input_ty)
            } else {
                drop(ty_data);
                None
            };
            if let Some(unify_to_ty) = unify_to_ty {
                self.unify_same_type(unify_to_ty, span, output_tys[0], span)?;
                return Ok(None);
            }
        }

        // Normal case.
        // Is the trait fully resolved?
        let resolved = input_tys.iter().all(Type::is_constant);
        Ok(if resolved {
            // Fully resolved, validate the trait implementation.
            let impl_output_tys =
                trait_solver.solve_output_types(&trait_ref, &input_tys, span, arena)?;
            // Found, unify the output types.
            assert!(output_tys.is_empty() || output_tys.len() == impl_output_tys.len());
            for (cur_ty, exp_ty) in output_tys.iter().zip(impl_output_tys.iter()) {
                self.unify_same_type(*cur_ty, span, *exp_ty, span)?;
            }
            None
        } else {
            // Partially resolved, we can progress a bit.
            let has_structured_non_constant_input = input_tys
                .iter()
                .any(|ty| !ty.is_constant() && !ty.data().is_variable());
            if has_structured_non_constant_input {
                let _ = trait_solver.try_improve_trait_application(
                    self,
                    &trait_ref,
                    &input_tys,
                    &output_tys,
                    assumptions,
                    span,
                    arena,
                )?;
            }
            let input_tys = self.normalize_types(&input_tys);
            let output_tys = self.normalize_types(&output_tys);
            if input_tys.iter().all(Type::is_constant) {
                let impl_output_tys =
                    trait_solver.solve_output_types(&trait_ref, &input_tys, span, arena)?;
                assert!(output_tys.is_empty() || output_tys.len() == impl_output_tys.len());
                for (cur_ty, exp_ty) in output_tys.iter().zip(impl_output_tys.iter()) {
                    self.unify_same_type(*cur_ty, span, *exp_ty, span)?;
                }
                None
            } else {
                // Not fully resolved, defer the unification.
                Some(PubTypeConstraint::new_have_trait(
                    trait_ref, input_tys, output_tys, span,
                ))
            }
        })
    }

    fn unify_constraint_pass(
        &mut self,
        constraints: &[PubTypeConstraint],
        is_ty_adt: impl Fn(Type) -> bool,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<Vec<PubTypeConstraint>, InternalCompilationError> {
        let mut new_constraints = Vec::with_capacity(constraints.len());
        for (constraint_index, constraint) in constraints.iter().enumerate() {
            use PubTypeConstraint::*;
            let unified_constraint = match constraint {
                TupleAtIndexIs {
                    tuple_ty,
                    tuple_span,
                    index,
                    index_span,
                    element_ty,
                } => self.unify_tuple_project(
                    *tuple_ty,
                    tuple_span.use_site,
                    *index,
                    index_span.use_site,
                    *element_ty,
                )?,
                RecordFieldIs {
                    record_ty,
                    record_span,
                    field,
                    field_span,
                    element_ty,
                } => self.unify_record_field_access(
                    *record_ty,
                    record_span.use_site,
                    *field,
                    field_span.use_site,
                    *element_ty,
                )?,
                TypeHasVariant {
                    variant_ty,
                    variant_span,
                    tag,
                    payload_ty,
                    payload_span,
                } => self.unify_type_has_variant(
                    *variant_ty,
                    variant_span.use_site,
                    *tag,
                    *payload_ty,
                    payload_span.use_site,
                )?,
                HaveTrait {
                    trait_ref,
                    input_tys,
                    output_tys,
                    span,
                } => {
                    let assumptions = constraints
                        .iter()
                        .enumerate()
                        .filter_map(|(index, constraint)| {
                            (index != constraint_index).then_some(constraint)
                        })
                        .collect::<Vec<_>>();
                    self.unify_have_trait(
                        trait_ref.clone(),
                        input_tys,
                        output_tys,
                        span.use_site,
                        &assumptions,
                        &is_ty_adt,
                        trait_solver,
                        arena,
                    )?
                }
            };
            if let Some(new_constraint) = unified_constraint {
                new_constraints.push(new_constraint);
            }
        }
        Ok(new_constraints)
    }

    fn unify_mut_must_be_at_least_or_equal(
        &mut self,
        current: MutType,
        current_span: Location,
        target: MutType,
        target_span: Location,
        ctx: MutabilityMustBeContext,
        sub_or_same: SubOrSameType,
    ) -> Result<(), InternalCompilationError> {
        let current_mut = self.normalize_mut_type(current);
        let target_mut = self.normalize_mut_type(target);
        // Note: here is the truth table of the constant/mutable relationship between
        // current and target, when sub_or_same is SubType:
        //            | cur cst | cur mut
        // -----------|---------|---------
        // target cst |   ok    |   ok
        // target mut |   err   |   ok
        // When it is SameType, the table is a perfect diagonal.
        use MutType::*;
        use MutabilityMustBeWhat::*;
        match (current_mut, target_mut) {
            (Variable(current), Variable(target)) => {
                // Do unification. Fuse both variable as it is acceptable
                // due to the transitivity of the "must be at least mutability" relationship.
                self.mut_unification_table
                    .unify_var_var(current, target)
                    .map_err(|_| {
                        internal_compilation_error!(MutabilityMustBe {
                            source_span: current_span,
                            reason_span: target_span,
                            what: Equal,
                            ctx,
                        })
                    })
            }
            (Variable(current), Resolved(target)) => self.unify_mut_current_variable(
                current,
                current_span,
                target,
                target_span,
                ctx,
                sub_or_same,
            ),
            (Resolved(current), Variable(target)) => self.unify_mut_target_variable(
                current,
                current_span,
                target,
                target_span,
                ctx,
                sub_or_same,
            ),
            (Resolved(current), Resolved(target)) => {
                use SubOrSameType::*;
                if match sub_or_same {
                    // Check mutability value coercion.
                    SubType => current < target,
                    // Must be exactly the same.
                    SameType => current != target,
                } {
                    Err(internal_compilation_error!(MutabilityMustBe {
                        source_span: current_span,
                        reason_span: target_span,
                        what: match sub_or_same {
                            SubType => Mutable,
                            SameType => Equal,
                        },
                        ctx,
                    }))
                } else {
                    Ok(())
                }
            }
        }
    }

    pub fn unify_mut_current_variable(
        &mut self,
        current: MutVar,
        source_span: Location,
        target: MutVal,
        reason_span: Location,
        ctx: MutabilityMustBeContext,
        sub_or_same: SubOrSameType,
    ) -> Result<(), InternalCompilationError> {
        use MutabilityMustBeWhat::*;
        use SubOrSameType::*;
        match sub_or_same {
            SubType => {
                // Target is resolved, if it is constant, we are done as anything can be used as constant.
                if target == MutVal::constant() {
                    Ok(())
                } else {
                    // If it is mutable, current must be mutable as well.
                    self.mut_unification_table
                        .unify_var_value(current, Some(MutVal::mutable()))
                        .map_err(|_| {
                            internal_compilation_error!(MutabilityMustBe {
                                source_span,
                                reason_span,
                                what: Mutable,
                                ctx
                            })
                        })
                }
            }
            SameType => self
                .mut_unification_table
                .unify_var_value(current, Some(target))
                .map_err(|_| {
                    internal_compilation_error!(MutabilityMustBe {
                        source_span,
                        reason_span,
                        what: Equal,
                        ctx
                    })
                }),
        }
    }

    pub fn unify_mut_target_variable(
        &mut self,
        current: MutVal,
        reason_span: Location,
        target: MutVar,
        source_span: Location,
        ctx: MutabilityMustBeContext,
        sub_or_same: SubOrSameType,
    ) -> Result<(), InternalCompilationError> {
        use MutabilityMustBeWhat::*;
        use SubOrSameType::*;
        match sub_or_same {
            SubType => {
                // Current is resolved, if it is mutable, we are done as it can be used for anything.
                if current == MutVal::mutable() {
                    Ok(())
                } else {
                    // If it is constant, target must be constant as well.
                    self.mut_unification_table
                        .unify_var_value(target, Some(MutVal::constant()))
                        .map_err(|_| {
                            internal_compilation_error!(MutabilityMustBe {
                                source_span,
                                reason_span,
                                what: Constant,
                                ctx
                            })
                        })
                }
            }
            SameType => self
                .mut_unification_table
                .unify_var_value(target, Some(current))
                .map_err(|_| {
                    internal_compilation_error!(MutabilityMustBe {
                        source_span,
                        reason_span,
                        what: Equal,
                        ctx
                    })
                }),
        }
    }

    /// Make current and target the same effect type.
    pub fn unify_same_effect(
        &mut self,
        current: EffType,
        current_span: Location,
        target: EffType,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        let current_vars = current.inner_vars();
        let current_any_vars = !current_vars.is_empty();
        let target_vars = target.inner_vars();
        let target_any_vars = !target_vars.is_empty();
        match (current_any_vars, target_any_vars) {
            (false, false) => {
                if current == target {
                    Ok(())
                } else {
                    Err(internal_compilation_error!(InvalidEffectDependency {
                        source: current,
                        source_span: current_span,
                        target,
                        target_span,
                    }))
                }
            }
            (true, false) => {
                for var in current_vars {
                    self.effect_unification_table
                        .union_value(var, Some(target.clone()));
                }
                Ok(())
            }
            (false, true) => {
                for var in target_vars {
                    self.effect_unification_table
                        .union_value(var, Some(current.clone()));
                }
                Ok(())
            }
            (true, true) => {
                if current_vars.len() > 1 {
                    return Err(internal_compilation_error!(Unsupported {
                        span: current_span,
                        reason: "Cannot unify multiple effect variables in the source".into(),
                    }));
                }
                if target_vars.len() > 1 {
                    return Err(internal_compilation_error!(Unsupported {
                        span: target_span,
                        reason: "Cannot unify multiple effect variables in the target".into(),
                    }));
                }
                self.effect_unification_table.union_value(
                    current_vars[0],
                    Some(EffType::multiple_primitive(&target.inner_non_vars())),
                );
                self.effect_unification_table.union_value(
                    target_vars[0],
                    Some(EffType::multiple_primitive(&current.inner_non_vars())),
                );
                self.effect_unification_table
                    .unify_var_var(current_vars[0], target_vars[0])
                    .map_err(|_| {
                        internal_compilation_error!(InvalidEffectDependency {
                            source: current,
                            source_span: current_span,
                            target,
                            target_span,
                        })
                    })
            }
        }
    }

    pub fn add_effect_dep(
        &mut self,
        current: &EffType,
        current_span: Location,
        target: &EffType,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        if current.is_empty() || current == target {
            return Ok(());
        }
        let cur_single = current.as_single();
        let cur_var = cur_single.and_then(|eff| eff.as_variable().cloned());
        let tgt_single = target.as_single();
        let tgt_var = tgt_single.and_then(|eff| eff.as_variable().cloned());
        if let Some(var) = cur_var {
            // Left is a variable, put the effect dependency on the right.
            self.effect_unification_table
                .union_value(var, Some(target.clone()));
        } else if let Some(var) = tgt_var {
            // Right is a variable, put the effect dependency to the inverted constraints,
            // to be resolved later.
            self.effect_constraints_inv.push(PendingEffectDependency {
                source: current.clone(),
                source_span: current_span,
                target: var,
                target_span,
            });
        } else {
            return Err(internal_compilation_error!(InvalidEffectDependency {
                source: current.clone(),
                source_span: current_span,
                target: target.clone(),
                target_span,
            }));
        }
        Ok(())
    }

    fn expand_inv_effect_dep(
        &mut self,
        dep: PendingEffectDependency,
    ) -> Result<(), InternalCompilationError> {
        if let Some(existing_effects) = self.effect_unification_table.probe_value(dep.target) {
            if current_satisfied_by_target(&dep.source, &existing_effects) {
                return Ok(());
            }

            let target_vars = existing_effects.inner_vars();
            if target_vars.is_empty() {
                return Err(internal_compilation_error!(InvalidEffectDependency {
                    source: dep.source,
                    source_span: dep.source_span,
                    target: existing_effects,
                    target_span: dep.target_span,
                }));
            }

            for var in target_vars {
                self.expand_inv_effect_dep(PendingEffectDependency {
                    source: dep.source.clone(),
                    source_span: dep.source_span,
                    target: var,
                    target_span: dep.target_span,
                })?;
            }
        } else {
            self.effect_unification_table.union_value(
                dep.target,
                Some(dep.source.union(&EffType::single_variable(dep.target))),
            );
        }
        Ok(())
    }

    pub fn substitute_in_module_function(
        &mut self,
        descr: &mut ModuleFunction,
        arena: &mut crate::ir::NodeArena,
    ) {
        descr.definition.ty_scheme.ty = self.substitute_in_fn_type(&descr.definition.ty_scheme.ty);
        descr.definition.ty_scheme.constraints =
            self.substitute_in_constraints(&descr.definition.ty_scheme.constraints);
        if let Some(root) = descr.get_code_entry() {
            self.substitute_in_node(arena, root);
        }
        for local in &mut descr.locals {
            local.ty = self.substitute_in_type(local.ty);
            local.mut_ty = self.substitute_in_mut_type(local.mut_ty);
        }
    }

    pub fn substitute_in_type(&mut self, ty: Type) -> Type {
        substitute_type(ty, &mut SubstituteTypes(self))
    }

    pub fn substitute_in_types(&mut self, tys: &[Type]) -> Vec<Type> {
        substitute_types(tys, &mut SubstituteTypes(self))
    }

    pub fn substitute_in_fn_type(&mut self, fn_ty: &FnType) -> FnType {
        substitute_fn_type(fn_ty, &mut SubstituteTypes(self))
    }

    pub fn substitute_in_mut_type(&mut self, mut_ty: MutType) -> MutType {
        SubstituteTypes(self).substitute_mut_type(mut_ty)
    }

    pub fn lookup_type_var(&mut self, var: TypeVar) -> Type {
        match self.ty_unification_table.probe_value(var) {
            Some(ty) => ty,
            _ => Type::variable(self.ty_unification_table.find(var)),
        }
    }

    fn substitute_type_lookup(&mut self, ty: Type) -> Type {
        let ty_data = ty.data();
        let var = match &*ty_data {
            TypeKind::Variable(var) => *var,
            _ => return ty,
        };
        drop(ty_data);
        self.lookup_type_var(var)
    }

    fn substitute_mut_lookup(&mut self, mut_ty: MutType, accept_var: bool) -> MutType {
        match mut_ty {
            MutType::Resolved(_) => mut_ty,
            MutType::Variable(var) => {
                let root = self.mut_unification_table.find(var);
                match self.mut_unification_table.probe_value(root) {
                    Some(val) => MutType::resolved(val),
                    _ => {
                        if accept_var {
                            MutType::variable(root)
                        } else {
                            panic!("Unresolved mutability variable")
                        }
                    }
                }
            }
        }
    }

    fn resolve_effect_var(&mut self, var: EffectVar) -> EffType {
        match self.effect_unification_table.probe_value(var) {
            Some(effects) => SubstituteTypes(self).substitute_effect_type(&effects),
            None => EffType::single_variable(self.effect_unification_table.find(var)),
        }
    }

    pub fn substitute_in_node(&mut self, arena: &mut ir::NodeArena, id: ir::NodeId) {
        let children = arena[id].kind.child_node_ids();
        for child in children {
            self.substitute_in_node(arena, child);
        }
        let node = &mut arena[id];
        node.ty = self.substitute_in_type(node.ty);
        node.effects = SubstituteTypes(self).substitute_effect_type(&node.effects);
        use ir::NodeKind::*;
        match &mut arena[id].kind {
            StaticApply(app) => {
                app.ty = self.substitute_in_fn_type(&app.ty);
                self.substitute_in_fn_inst_data(&mut app.inst_data);
            }
            TraitFnApply(app) => {
                app.ty = self.substitute_in_fn_type(&app.ty);
                app.input_tys = self.substitute_in_types(&app.input_tys);
                self.substitute_in_fn_inst_data(&mut app.inst_data);
            }
            GetFunction(get_fn) => {
                self.substitute_in_fn_inst_data(&mut get_fn.inst_data);
            }
            _ => {}
        }
    }

    fn substitute_in_fn_inst_data(&mut self, inst_data: &mut FnInstData) {
        use DictionaryReq::*;
        inst_data.dicts_req = inst_data
            .dicts_req
            .iter()
            .map(|dict| match dict {
                FieldIndex { ty, field } => FieldIndex {
                    ty: self.substitute_in_type(*ty),
                    field: *field,
                },
                TraitImpl {
                    trait_ref,
                    input_tys,
                    output_tys,
                } => TraitImpl {
                    trait_ref: trait_ref.clone(),
                    input_tys: self.substitute_in_types(input_tys),
                    output_tys: self.substitute_in_types(output_tys),
                },
            })
            .collect();
    }

    pub fn substitute_in_constraint(
        &mut self,
        constraint: &PubTypeConstraint,
    ) -> PubTypeConstraint {
        use PubTypeConstraint::*;
        match constraint {
            TupleAtIndexIs {
                tuple_ty,
                tuple_span,
                index,
                index_span,
                element_ty,
            } => {
                let tuple_ty = self.substitute_in_type(*tuple_ty);
                let element_ty = self.substitute_in_type(*element_ty);
                TupleAtIndexIs {
                    tuple_ty,
                    tuple_span: tuple_span.clone(),
                    index: *index,
                    index_span: index_span.clone(),
                    element_ty,
                }
            }
            RecordFieldIs {
                record_ty,
                record_span,
                field,
                field_span,
                element_ty,
            } => {
                let record_ty = self.substitute_in_type(*record_ty);
                let element_ty = self.substitute_in_type(*element_ty);
                RecordFieldIs {
                    record_ty,
                    record_span: record_span.clone(),
                    field: *field,
                    field_span: field_span.clone(),
                    element_ty,
                }
            }
            TypeHasVariant {
                variant_ty,
                variant_span,
                tag,
                payload_ty,
                payload_span,
            } => {
                let variant_ty = self.substitute_in_type(*variant_ty);
                let payload_ty = self.substitute_in_type(*payload_ty);
                TypeHasVariant {
                    variant_ty,
                    variant_span: variant_span.clone(),
                    tag: *tag,
                    payload_ty,
                    payload_span: payload_span.clone(),
                }
            }
            HaveTrait {
                trait_ref,
                input_tys,
                output_tys,
                span,
            } => {
                let input_tys = self.substitute_in_types(input_tys);
                let output_tys = self.substitute_in_types(output_tys);
                HaveTrait {
                    trait_ref: trait_ref.clone(),
                    input_tys,
                    output_tys,
                    span: span.clone(),
                }
            }
        }
    }

    fn substitute_in_constraints(
        &mut self,
        constraints: &[PubTypeConstraint],
    ) -> Vec<PubTypeConstraint> {
        constraints
            .iter()
            .map(|c| self.substitute_in_constraint(c))
            .collect()
    }

    pub fn log_debug_constraints(&self, module_env: ModuleEnv) {
        if self.remaining_ty_constraints.is_empty() {
            log::debug!("No type constraints after unification.");
        } else {
            log::debug!("Type constraints after unification:");
            if !self.remaining_ty_constraints.is_empty() {
                for constraint in &self.remaining_ty_constraints {
                    log::debug!("  {}", constraint.format_with(&module_env));
                }
            }
        }
    }

    pub fn log_debug_substitution_tables(&mut self, module_env: ModuleEnv) {
        log::debug!("Type substitution table:");
        for i in 0..self.ty_unification_table.len() {
            let var = TypeVar::new(i as u32);
            let value = self.ty_unification_table.probe_value(var);
            match value {
                Some(value) => log::debug!("  {var} → {}", value.format_with(&module_env)),
                None => log::debug!("  {var} → {} (unbound)", {
                    self.ty_unification_table.find(var)
                }),
            }
        }
        log::debug!("Mutability substitution table:");
        for i in 0..self.mut_unification_table.len() {
            let var = MutVar::new(i as u32);
            let value = self.mut_unification_table.probe_value(var);
            match value {
                Some(value) => log::debug!("  {var} → {value}"),
                None => log::debug!("  {var} → {} (unbound)", {
                    self.mut_unification_table.find(var)
                }),
            }
        }
        self.log_debug_effect_constraints();
    }

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
        if !self.effect_constraints_inv.is_empty() {
            log::debug!("Inverted effect constraints:");
            for dep in &self.effect_constraints_inv {
                log::debug!("  {} → {}", dep.source, dep.target);
            }
        }
    }
}

fn total_constraints_var_count<'a>(
    constraints: impl IntoIterator<Item = &'a PubTypeConstraint>,
) -> usize {
    constraints
        .into_iter()
        .map(|constraint| constraint.inner_ty_vars().len())
        .sum()
}

fn current_satisfied_by_target(current: &EffType, target: &EffType) -> bool {
    // A pending dependency is already satisfied if the target contains all currently required
    // primitive effects. Any target-side variables can still absorb the remaining uncertainty.
    let target_primitives = EffType::multiple_primitive(&target.inner_non_vars());
    current.is_subset_of(&target_primitives)
}

/// Substitution phase
struct SubstituteTypes<'a>(&'a mut UnifiedTypeInference);
impl TypeSubstituer for SubstituteTypes<'_> {
    fn substitute_type(&mut self, ty: Type) -> Type {
        self.0.substitute_type_lookup(ty)
    }

    fn substitute_mut_type(&mut self, mut_ty: MutType) -> MutType {
        self.0.substitute_mut_lookup(mut_ty, false)
    }

    /// Substitute the effect type by flattening the effect variables.
    fn substitute_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        use Effect::*;

        // Thread-local hash-map for cycle detection
        thread_local! {
            static VAR_VISITED: RefCell<FxHashSet<EffectVar>> = RefCell::new(FxHashSet::default());
        }

        EffType::from_iter(eff_ty.iter().flat_map(|eff| {
            EffType::into_iter(match eff {
                Primitive(effect) => EffType::single_primitive(*effect),
                Variable(var) => {
                    let cycle_detected = VAR_VISITED.with(|visited| {
                        let mut visited = visited.borrow_mut();
                        if visited.contains(var) {
                            true // Cycle detected
                        } else {
                            visited.insert(*var);
                            false
                        }
                    });

                    if cycle_detected {
                        return EffType::empty().into_iter();
                    }

                    let mut effects = self.0.resolve_effect_var(*var);

                    // add back the variable itself if not only variables
                    if !effects.is_only_vars() {
                        effects = effects.union(&EffType::single_variable(*var));
                    }

                    VAR_VISITED.with(|visited| {
                        visited.borrow_mut().remove(var);
                    });

                    effects
                }
            } as EffType)
        }))
    }
}

/// Normalization phase
struct NormalizeTypes<'a>(&'a mut UnifiedTypeInference);
impl TypeSubstituer for NormalizeTypes<'_> {
    fn substitute_type(&mut self, ty: Type) -> Type {
        self.0.substitute_type_lookup(ty)
    }

    fn substitute_mut_type(&mut self, mut_ty: MutType) -> MutType {
        self.0.substitute_mut_lookup(mut_ty, true)
    }

    fn substitute_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        eff_ty.clone()
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
