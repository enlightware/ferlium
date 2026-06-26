// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    FxHashMap, FxHashSet, Location, Modules,
    ast::{self, DExprArena, DModuleFunctionArg},
    compiler::{
        CompilationCapabilities,
        error::{
            AttributeTarget, InternalCompilationError, InvalidAttributeKind,
            InvalidSubscriptDefinitionKind, SubscriptDefinitionSubject, UnsafeFeature,
            UnsupportedSubscriptFeatureKind,
        },
    },
    containers::{SVec2, b},
    format::FormatWith,
    hir::{self, NodeArena},
    hir::{
        emit_hir::{
            ImplStubData, PendingModuleFunctions, PubTypeConstraintPtr,
            add_pending_function_anonymous, borrow_check_and_elaborate_dict, constraint_ptr,
            default_body_only_effects_in_function_descr, default_output_effects_in_functions,
            function_and_associated_lambdas, insert_inst_data_for_function_and_lambdas,
            instantiate_function_descr_in_place, is_compiler_provided_value_constraint,
            log_dropped_constraints_module, refresh_debug_info_for_functions, set_pending_function,
            substitute_and_canonicalize_functions,
        },
        function::CallableDefinition,
    },
    internal_compilation_error,
    module::{
        FunctionId, GENERATED_LAMBDA_PREFIX, LocalDecl, LocalDeclId, LocalFunctionId,
        LocalSubscriptId, Module, ModuleEnv, ModuleFunction, ModuleFunctionSpans, ModuleId,
        PendingFunctionBody, PendingModuleFunction, QualifiedNameEnv, TraitId, Visibility,
        YieldProvenance, id::Id,
    },
    std::{STD_MODULE_ID, new_module_using_std},
    types::{
        effects::{PrimitiveEffect, effect},
        mutability::MutType,
        r#trait::{Trait, TraitMethodIndex},
        trait_solver::{TraitSolver, trait_solver_from_module},
        r#type::{CallResultConvention, FnArgType, FnType, Type, TypeInstSubst, TypeVar},
        type_constraints::named_type_constraints_in_types,
        type_inference::{
            defaulting::{ConstraintBoundary, DefaultingScope},
            effect_solver::EffectConstraintOrigin,
            expr::{AnnotationTypeMapper, TypeInference},
            substitution::InstSubst,
            unify::UnifiedTypeInference,
        },
        type_like::{TypeLike, instantiate_types_in_place},
        type_mapper::{BitmapInstantiationMapper, TypeMapper},
        type_scheme::{
            PubTypeConstraint, TypeScheme, extra_parameters_from_constraints, normalize_types,
        },
        type_visitor::{TyVarsCollector, collect_ty_vars},
        typing_env::{SubscriptMemberTypingContext, TypingEnv},
    },
};

use indexmap::IndexMap;
use itertools::Itertools;
use log::log_enabled;
use ustr::{Ustr, ustr};

use crate::hir::elaboration::elaborate_generated_functions;
use crate::types::effects::{EffType, Effect, EffectVar, EffectsInstSubst};

/// Context passed to emit_functions when a trait implementation is being emitted.
pub(super) struct EmitTraitCtx<'a> {
    pub(super) trait_id: TraitId,
    pub(super) trait_def: Trait,
    pub(super) span: Location,
    pub(super) stub_data: Option<&'a ImplStubData>,
    pub(super) generic_param_count: usize,
    pub(super) generic_effect_param_count: usize,
    pub(super) for_trait: Option<&'a ast::DTraitImplFor>,
    pub(super) impl_constraints: &'a [PubTypeConstraint],
}

pub(crate) struct EmitTraitOutput {
    pub(crate) input_tys: Vec<Type>,
    pub(crate) output_tys: Vec<Type>,
    pub(crate) output_effs: Vec<EffType>,
    pub(crate) ty_var_count: u32,
    pub(crate) eff_var_count: u32,
    pub(crate) constraints: Vec<PubTypeConstraint>,
    pub(crate) functions: Vec<LocalFunctionId>,
}

#[derive(Clone, Copy, Debug, Default)]
struct FunctionAttributes {
    no_fuel_check: bool,
}

#[derive(Clone, Copy, Debug, Default)]
pub(super) enum EmitFunctionKind {
    #[default]
    Normal,
    SubscriptMember {
        subscript_name: Ustr,
        provenance: YieldProvenance,
        requires_mutable_yield: bool,
    },
}

#[derive(Clone, Copy, Debug)]
pub(super) struct SubscriptMemberAttachment {
    pub(super) subscript_id: LocalSubscriptId,
    pub(super) is_mut_member: bool,
    pub(super) provenance: YieldProvenance,
    pub(super) span: Location,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct EmitFunctionInput<'a> {
    pub(super) function: &'a ast::DModuleFunction,
    pub(super) kind: EmitFunctionKind,
    pub(super) subscript_attachments: &'a [SubscriptMemberAttachment],
}

impl<'a> EmitFunctionInput<'a> {
    pub(super) fn normal(function: &'a ast::DModuleFunction) -> Self {
        Self {
            function,
            kind: EmitFunctionKind::Normal,
            subscript_attachments: &[],
        }
    }
}

impl EmitFunctionKind {
    fn return_convention(self) -> CallResultConvention {
        match self {
            EmitFunctionKind::Normal => CallResultConvention::Value,
            EmitFunctionKind::SubscriptMember {
                provenance: YieldProvenance::YieldedOnce,
                ..
            } => CallResultConvention::YieldedOnce,
            EmitFunctionKind::SubscriptMember {
                provenance: YieldProvenance::AddressorPlace,
                ..
            } => CallResultConvention::AddressorPlace,
        }
    }

    fn body_expected_ty(self, default: Type) -> Type {
        match self {
            EmitFunctionKind::Normal => default,
            EmitFunctionKind::SubscriptMember {
                provenance: YieldProvenance::YieldedOnce,
                ..
            } => Type::unit(),
            EmitFunctionKind::SubscriptMember {
                provenance: YieldProvenance::AddressorPlace,
                ..
            } => default,
        }
    }

    fn force_anonymous(self) -> bool {
        matches!(self, EmitFunctionKind::SubscriptMember { .. })
    }

    fn requires_mutable_yield(self) -> bool {
        match self {
            EmitFunctionKind::Normal => false,
            EmitFunctionKind::SubscriptMember {
                provenance: YieldProvenance::YieldedOnce,
                requires_mutable_yield,
                ..
            } => requires_mutable_yield,
            EmitFunctionKind::SubscriptMember {
                provenance: YieldProvenance::AddressorPlace,
                ..
            } => false,
        }
    }

    fn requires_mutable_place(self) -> bool {
        match self {
            EmitFunctionKind::Normal => false,
            EmitFunctionKind::SubscriptMember {
                requires_mutable_yield,
                ..
            } => requires_mutable_yield,
        }
    }
}

fn normalize_effect_vars(vars: &mut [EffectVar]) -> EffectsInstSubst {
    let mut eff_subst = EffectsInstSubst::default();
    for (index, quantifier) in vars.iter_mut().enumerate() {
        let new_var = EffectVar::new(index as u32);
        eff_subst.insert(*quantifier, EffType::single_variable(new_var));
        *quantifier = new_var;
    }
    eff_subst
}

fn validate_function_attributes(
    attributes: &[ast::Attribute],
    function_name: Ustr,
    is_std_module: bool,
) -> Result<FunctionAttributes, InternalCompilationError> {
    let mut no_fuel_check = false;
    let known_attributes = [ustr("no_fuel_check")];
    for attribute in attributes {
        let attr_name = attribute.path.0;
        if !known_attributes.contains(&attr_name) {
            continue;
        }
        if !is_std_module {
            return Err(
                InternalCompilationError::new_unsafe_feature_use_not_allowed(
                    UnsafeFeature::FunctionAttribute(attr_name),
                    attribute.span,
                ),
            );
        }
        if !attribute.items.is_empty() {
            return Err(internal_compilation_error!(InvalidAttribute {
                attribute_name: attr_name,
                target: AttributeTarget::Function {
                    name: function_name,
                },
                kind: InvalidAttributeKind::HasArguments,
                span: attribute.span,
            }));
        }
        if no_fuel_check {
            return Err(internal_compilation_error!(InvalidAttribute {
                attribute_name: attr_name,
                target: AttributeTarget::Function {
                    name: function_name,
                },
                kind: InvalidAttributeKind::Duplicate,
                span: attribute.span,
            }));
        }
        no_fuel_check = true;
    }
    Ok(FunctionAttributes { no_fuel_check })
}

fn node_references_any_function(
    arena: &NodeArena,
    node_id: hir::NodeId,
    targets: &FxHashSet<FunctionId>,
) -> bool {
    if targets.is_empty() {
        return false;
    }
    match &arena[node_id].kind {
        hir::NodeKind::StaticApply(app) if targets.contains(&app.function) => return true,
        hir::NodeKind::GetFunction(get_fn) if targets.contains(&get_fn.function) => return true,
        _ => {}
    }
    arena[node_id]
        .kind
        .child_node_ids()
        .into_iter()
        .any(|child| node_references_any_function(arena, child, targets))
}

fn yield_path_is_block_structured(
    arena: &NodeArena,
    node_id: hir::NodeId,
    yield_node_id: hir::NodeId,
) -> bool {
    if node_id == yield_node_id {
        return true;
    }
    match &arena[node_id].kind {
        hir::NodeKind::Block(block) => block
            .body
            .iter()
            .any(|child| yield_path_is_block_structured(arena, *child, yield_node_id)),
        _ => false,
    }
}

fn wrap_body_with_call_depth_check_if_recursive(
    ty_inf: &mut TypeInference,
    arena: &mut NodeArena,
    body_id: hir::NodeId,
    recursive_function_ids: &FxHashSet<FunctionId>,
    return_ty: Type,
    check_span: Location,
    block_span: Location,
) -> hir::NodeId {
    if !node_references_any_function(arena, body_id, recursive_function_ids) {
        return body_id;
    }

    let check_id = arena.alloc(hir::Node::new(
        hir::NodeKind::CheckCallDepth,
        Type::unit(),
        effect(PrimitiveEffect::Fallible),
        check_span,
    ));
    let body_effects = arena[body_id].effects.clone();
    let effects = ty_inf.make_dependent_effect([&arena[check_id].effects, &body_effects]);
    arena.alloc(hir::Node::new(
        hir::NodeKind::Block(b(hir::Block {
            body: b(SVec2::from_vec(vec![check_id, body_id])),
            cleanup: Vec::new(),
        })),
        return_ty,
        effects,
        block_span,
    ))
}

struct DivergingReturnDefaultingInputs<'ctx, I> {
    ast_functions: I,
    local_fns: &'ctx [LocalFunctionId],
    function_explicit_root_tys: &'ctx [Vec<Type>],
    recursive_function_ids: &'ctx FxHashSet<FunctionId>,
    associated_lambdas: &'ctx FxHashMap<LocalFunctionId, Vec<LocalFunctionId>>,
    pending_functions: &'ctx mut PendingModuleFunctions,
}

fn default_unconstrained_diverging_returns_to_never<'func, I>(
    output: &mut Module,
    ty_inf: &mut UnifiedTypeInference,
    inputs: DivergingReturnDefaultingInputs<'_, I>,
) where
    I: Iterator<Item = EmitFunctionInput<'func>>,
{
    for ((input, id), explicit_root_tys) in inputs
        .ast_functions
        .zip(inputs.local_fns.iter())
        .zip(inputs.function_explicit_root_tys.iter())
    {
        let function = input.function;
        if function.ret_ty.is_some() {
            continue;
        }

        let Some(pending) = inputs.pending_functions.get(id) else {
            continue;
        };

        let body_is_never = pending.code.arena[pending.code.entry_node_id].ty == Type::never();
        let unproductive_recursive = inputs
            .recursive_function_ids
            .contains(&FunctionId::new(output.module_id(), *id))
            && node_references_any_function(
                &pending.code.arena,
                pending.code.entry_node_id,
                inputs.recursive_function_ids,
            );
        if !body_is_never && !unproductive_recursive {
            continue;
        }

        let descr = &output.functions[id.as_index()];
        let fn_ty = ty_inf.substitute_in_fn_type(&descr.definition.ty_scheme.ty);
        let Some(ret_var) = fn_ty.ret.data().as_variable().copied() else {
            continue;
        };

        if fn_ty
            .args
            .iter()
            .any(|arg| arg.ty.contains_any_type_var(ret_var))
            || explicit_root_tys.iter().any(|ty| {
                ty_inf
                    .substitute_in_type(*ty)
                    .contains_any_type_var(ret_var)
            })
            || ty_inf
                .remaining_constraints()
                .iter()
                .any(|constraint| constraint.contains_any_type_var(ret_var))
        {
            continue;
        }

        let subst: (TypeInstSubst, FxHashMap<_, _>) = (
            FxHashMap::from_iter([(ret_var, Type::never())]),
            FxHashMap::default(),
        );
        let mut mapper = BitmapInstantiationMapper::new(&subst);
        for function_id in function_and_associated_lambdas(id, inputs.associated_lambdas) {
            let descr = &mut output.functions[function_id.as_index()];
            descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
            let pending = inputs
                .pending_functions
                .get_mut(&function_id)
                .expect("expected pending function body");
            pending.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.clone();
            instantiate_function_descr_in_place(pending, &mut mapper);
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn emit_functions<'a, F, I>(
    output: &mut Module,
    solver_arena: &mut NodeArena,
    ast_functions: F,
    desugared_arena: &DExprArena,
    others: &Modules,
    trait_ctx: Option<EmitTraitCtx>,
    recursive_function_names: &FxHashSet<Ustr>,
    capabilities: CompilationCapabilities,
) -> Result<Option<EmitTraitOutput>, InternalCompilationError>
where
    I: Iterator<Item = EmitFunctionInput<'a>>,
    F: Fn() -> I,
{
    // First pass, populate the function table and allocate fresh mono type variables.
    let mut ty_inf = TypeInference::default();
    let mut impl_annotation_subst = None;
    let mut outer_annotation_var_count = 0;
    let mut outer_annotation_eff_var_count = 0;
    let mut explicit_trait_impl = None;
    let module_env = ModuleEnv::new(output, others);

    // If we are emitting a trait implementation, create generics for the trait input and output types
    // and add the constraints from the trait definition to the type inference.
    let trait_output = if let Some(trait_ctx) = &trait_ctx {
        let trait_def = &trait_ctx.trait_def;
        let input_tys = ty_inf.fresh_type_var_tys(trait_def.input_type_count() as usize);
        let output_tys = ty_inf.fresh_type_var_tys(trait_def.output_type_count() as usize);
        let output_effs = (0..trait_def.output_effect_count())
            .map(|_| ty_inf.fresh_effect_var_ty())
            .collect::<Vec<_>>();
        let explicit_quantifiers = if trait_ctx.generic_param_count > 0 {
            (0..trait_ctx.generic_param_count)
                .map(|index| TypeVar::new(index as u32))
                .collect::<Vec<_>>()
        } else if let Some(for_trait) = trait_ctx.for_trait {
            let mut tys = for_trait.input_tys();
            tys.extend(for_trait.output_tys());
            collect_ty_vars(&tys)
        } else {
            vec![]
        };
        // Reserve the leading annotation placeholder indices for explicit impl-level generics,
        // so any function-level generics in this shared path start after them.
        outer_annotation_var_count = explicit_quantifiers.len();
        let explicit_eff_quantifiers = (0..trait_ctx.generic_effect_param_count)
            .map(|index| EffectVar::new(index as u32))
            .collect::<FxHashSet<_>>();
        outer_annotation_eff_var_count = trait_ctx.generic_effect_param_count;
        if !explicit_quantifiers.is_empty() || !explicit_eff_quantifiers.is_empty() {
            impl_annotation_subst = Some((
                ty_inf.fresh_type_var_subst(&explicit_quantifiers),
                ty_inf.fresh_effect_var_subst(&explicit_eff_quantifiers),
            ));
        }
        explicit_trait_impl = trait_ctx.for_trait.map(|for_trait| {
            let mut mapper = impl_annotation_subst
                .as_ref()
                .map(BitmapInstantiationMapper::new);
            let mut instantiate = |ty: Type| match &mut mapper {
                Some(m) => ty.map(m),
                None => ty,
            };
            let input_tys: Vec<_> = for_trait
                .input_tys()
                .into_iter()
                .map(&mut instantiate)
                .collect();
            let output_tys: Vec<_> = for_trait
                .output_tys()
                .into_iter()
                .map(&mut instantiate)
                .collect();
            let output_effs: Vec<_> = for_trait
                .output_effs()
                .into_iter()
                .map(|eff| match &mut mapper {
                    Some(m) => m.map_effect_type(&eff),
                    None => eff,
                })
                .collect();
            let mut explicit_tys = input_tys.clone();
            explicit_tys.extend(output_tys.iter().copied());
            let explicit_constraints =
                named_type_constraints_in_types(explicit_tys, trait_ctx.span, &module_env);
            (input_tys, output_tys, output_effs, explicit_constraints)
        });
        if let Some((
            explicit_input_tys,
            explicit_output_tys,
            explicit_output_effs,
            explicit_constraints,
        )) = &explicit_trait_impl
        {
            if explicit_input_tys.len() != input_tys.len() {
                return Err(internal_compilation_error!(WrongNumberOfArguments {
                    expected: input_tys.len(),
                    expected_span: trait_ctx.span,
                    got: explicit_input_tys.len(),
                    got_span: trait_ctx.span,
                }));
            }
            if !explicit_output_tys.is_empty() && explicit_output_tys.len() != output_tys.len() {
                return Err(internal_compilation_error!(WrongNumberOfArguments {
                    expected: output_tys.len(),
                    expected_span: trait_ctx.span,
                    got: explicit_output_tys.len(),
                    got_span: trait_ctx.span,
                }));
            }
            if !explicit_output_effs.is_empty() && explicit_output_effs.len() != output_effs.len() {
                return Err(internal_compilation_error!(WrongNumberOfArguments {
                    expected: output_effs.len(),
                    expected_span: trait_ctx.span,
                    got: explicit_output_effs.len(),
                    got_span: trait_ctx.span,
                }));
            }
            for constraint in explicit_constraints {
                ty_inf.add_pub_constraint(constraint.clone());
            }
            for (input_ty, explicit_ty) in input_tys.iter().zip(explicit_input_tys.iter()) {
                ty_inf.add_same_type_with_sub_effects_constraint(
                    *input_ty,
                    trait_ctx.span,
                    *explicit_ty,
                    trait_ctx.span,
                );
            }
            for (output_ty, explicit_ty) in output_tys.iter().zip(explicit_output_tys.iter()) {
                ty_inf.add_same_type_with_sub_effects_constraint(
                    *output_ty,
                    trait_ctx.span,
                    *explicit_ty,
                    trait_ctx.span,
                );
            }
            for (output_eff, explicit_eff) in output_effs.iter().zip(explicit_output_effs.iter()) {
                ty_inf.add_same_effect_constraint(
                    output_eff,
                    trait_ctx.span,
                    explicit_eff,
                    trait_ctx.span,
                );
            }
        } else if let Some(stub_data) = trait_ctx.stub_data {
            // For a stub implementation, equate the fresh input types with the concrete types from the impl annotation.
            assert_eq!(input_tys.len(), stub_data.input_tys.len());
            for (ty_var, concrete_ty) in input_tys.iter().zip(stub_data.input_tys.iter()) {
                ty_inf.add_same_type_with_sub_effects_constraint(
                    *ty_var,
                    trait_ctx.span,
                    *concrete_ty,
                    trait_ctx.span,
                );
            }
        }
        for constraint in &trait_def.parent_constraints {
            ty_inf.add_pub_constraint(constraint.instantiate_location_cloned(trait_ctx.span));
        }
        for constraint in &trait_def.constraints {
            ty_inf.add_pub_constraint(constraint.instantiate_location_cloned(trait_ctx.span));
        }
        let mut mapper = impl_annotation_subst
            .as_ref()
            .map(BitmapInstantiationMapper::new);
        for constraint in trait_ctx.impl_constraints {
            let constraint = match &mut mapper {
                Some(m) => constraint.map(m),
                None => constraint.clone(),
            };
            ty_inf.add_pub_constraint(constraint);
        }
        Some(EmitTraitOutput {
            input_tys,
            output_tys,
            output_effs,
            ty_var_count: 0,
            eff_var_count: 0,
            constraints: vec![],
            functions: vec![],
        })
    } else {
        None
    };
    let instantiated_trait_method_defs = match (&trait_ctx, &trait_output) {
        (Some(trait_ctx), Some(trait_output)) => Some(trait_ctx.trait_def.instantiate_for_tys(
            &trait_output.input_tys,
            &trait_output.output_tys,
            &trait_output.output_effs,
        )),
        _ => None,
    };

    // Populate the function table
    let mut local_fns = Vec::new();
    let mut function_annotation_substs = Vec::new();
    let mut function_explicit_root_tys = Vec::new();
    let mut function_attrs = Vec::new();
    let mut function_kinds = Vec::new();
    let mut subscript_attachments: Vec<Vec<SubscriptMemberAttachment>> = Vec::new();
    for input in ast_functions() {
        let ast::ModuleFunction {
            visibility,
            name,
            generic_params,
            args,
            args_span,
            ret_ty,
            where_clause,
            attributes,
            span,
            doc,
            ..
        } = input.function;
        let kind = input.kind;
        // Create type and mutability variables for the arguments.
        // Note: the type quantifiers and constraints are left empty.
        // They will be filled in the second pass.
        // The effect quantifiers are filled with the output effect variable.
        if let Some(trait_ctx) = &trait_ctx {
            if !generic_params.is_empty() {
                let generic_span = generic_params
                    .type_params()
                    .first()
                    .or_else(|| generic_params.effect_params().first())
                    .unwrap()
                    .1;
                return Err(internal_compilation_error!(Unsupported {
                    span: generic_span,
                    reason: format!(
                        "Explicit generic parameters on trait impl methods are not supported yet: method `{}` in impl of trait `{}`",
                        name.0, trait_ctx.trait_def.name
                    ),
                }));
            }
            if let Some(constraint) = where_clause.first() {
                return Err(internal_compilation_error!(Unsupported {
                    span: constraint.use_site(),
                    reason: format!(
                        "Method-local where clauses on trait impl methods are not supported yet: method `{}` in impl of trait `{}`",
                        name.0, trait_ctx.trait_def.name
                    ),
                }));
            }
        }
        let mut annotation_subst: InstSubst = impl_annotation_subst.clone().unwrap_or_default();
        let explicit_root_tys = generic_params
            .type_params()
            .iter()
            .enumerate()
            .map(|(index, _)| {
                let source_var = TypeVar::new((outer_annotation_var_count + index) as u32);
                let fresh_ty = ty_inf.fresh_type_var_ty();
                annotation_subst.0.insert(source_var, fresh_ty);
                fresh_ty
            })
            .collect::<Vec<_>>();
        for (index, _) in generic_params.effect_params().iter().enumerate() {
            let source_var = EffectVar::new((outer_annotation_eff_var_count + index) as u32);
            let fresh_eff = ty_inf.fresh_effect_var_ty();
            annotation_subst.1.insert(source_var, fresh_eff);
        }
        let args_ty = args
            .iter()
            .map(|arg| {
                if let Some((mut_ty, ty, _)) = &arg.ty {
                    let mut mapper =
                        AnnotationTypeMapper::new(&mut ty_inf, Some(&annotation_subst));
                    let mut_ty = match mut_ty {
                        Some(mut_ty) => mapper.map_mut_type(*mut_ty),
                        None => MutType::constant(),
                    };
                    let ty = ty.map(&mut mapper);
                    FnArgType::new(ty, mut_ty)
                } else {
                    ty_inf.fresh_fn_arg()
                }
            })
            .collect();
        let ret_ty_ty = if let Some((ret_ty, _)) = ret_ty {
            ret_ty.map(&mut AnnotationTypeMapper::new(
                &mut ty_inf,
                Some(&annotation_subst),
            ))
        } else {
            ty_inf.fresh_type_var_ty()
        };
        let mut mapper = BitmapInstantiationMapper::new(&annotation_subst);
        for constraint in where_clause {
            ty_inf.add_pub_constraint(constraint.map(&mut mapper));
        }
        let attrs =
            validate_function_attributes(attributes, name.0, output.module_id() == STD_MODULE_ID)?;
        let effects = ty_inf.fresh_effect_var_ty();
        let return_convention = kind.return_convention();
        let fn_type = FnType::new(args_ty, ret_ty_ty, effects.clone());

        // If we are emitting a trait implementation, make sure this function conforms to it.
        if let Some(trait_ctx) = &trait_ctx {
            let index = trait_ctx.trait_def.method_index(name.0).unwrap();
            let (method_name, raw_method_def) = trait_ctx.trait_def.method(index);
            let instantiated_method_def =
                &instantiated_trait_method_defs.as_ref().unwrap()[index.as_index()];
            if args.len() != raw_method_def.ty_scheme.ty.args.len() {
                return Err(internal_compilation_error!(TraitMethodArgCountMismatch {
                    trait_ref: trait_ctx.trait_id,
                    method_index: index.as_index(),
                    method_name: *method_name,
                    expected: raw_method_def.ty_scheme.ty.args.len(),
                    got: args.len(),
                    args_span: *args_span,
                }));
            }
            // TODO: get span from the trait method definition, when available
            // Note: we use the variant without effects because trait impl effects are validated
            // separately after type inference (they must be a subset of trait definition effects).
            ty_inf.add_same_fn_type_constraint_without_effects(
                &fn_type,
                *span,
                &instantiated_method_def.ty_scheme.ty,
                *span,
            );
        }

        // Create dummy code.
        let arg_names: Vec<_> = args.iter().map(|arg| arg.name.0).collect();

        // Assemble the spans and the description
        let spans = ModuleFunctionSpans {
            name: name.1,
            args: args
                .iter()
                .map(DModuleFunctionArg::locations_and_ty_concreteness)
                .collect(),
            args_span: *args_span,
            ret_ty: ret_ty.map(|ret_ty| (ret_ty.1, ret_ty.0.is_constant())),
            span: *span,
        };
        let ty_scheme = TypeScheme::new_just_type(fn_type);
        let definition = CallableDefinition::new_with_generic_params_and_attributes(
            ty_scheme,
            generic_params.type_params().to_vec(),
            generic_params.effect_params().to_vec(),
            arg_names,
            doc.clone(),
            attributes.clone(),
        )
        .with_result_convention(return_convention);
        let descr = ModuleFunction::placeholder(definition, Some(spans));
        let id = if let Some(placeholder_ids) = trait_ctx
            .as_ref()
            .and_then(|tc| tc.stub_data.as_ref().map(|tys| &tys.method_ids))
        {
            // Reuse the pre-allocated stub slot so existing StaticApply nodes remain valid.
            let placeholder_id = placeholder_ids[local_fns.len()];
            output.functions[placeholder_id.as_index()] = descr;
            placeholder_id
        } else if trait_ctx.is_some() || kind.force_anonymous() {
            output.add_function_anonymous(descr)
        } else {
            output.add_function_with_visibility(name.0, descr, *visibility)
        };
        local_fns.push(id);
        function_annotation_substs.push(annotation_subst);
        function_explicit_root_tys.push(explicit_root_tys);
        function_attrs.push(attrs);
        function_kinds.push(kind);
        subscript_attachments.push(input.subscript_attachments.to_vec());
    }

    for (attachment, id) in subscript_attachments.iter().zip(local_fns.iter()) {
        for attachment in attachment {
            super::emit_subscripts::attach_subscript_member(
                output,
                attachment.subscript_id,
                *id,
                attachment.is_mut_member,
                attachment.provenance,
                attachment.span,
            )?;
        }
    }

    // Associated lambdas for functions emitted while lowering closure expressions.
    let mut associated_lambdas: FxHashMap<LocalFunctionId, Vec<LocalFunctionId>> =
        FxHashMap::default();
    let mut pending_functions = PendingModuleFunctions::default();

    let recursive_function_ids = ast_functions()
        .zip(local_fns.iter())
        .filter_map(|(input, id)| {
            recursive_function_names
                .contains(&input.function.name.0)
                .then_some(FunctionId::new(output.module_id(), *id))
        })
        .collect::<FxHashSet<_>>();

    // Second pass, infer types and emit function bodies.
    for ((((input, id), annotation_subst), attrs), kind) in ast_functions()
        .zip(local_fns.iter())
        .zip(function_annotation_substs.iter())
        .zip(function_attrs.iter())
        .zip(function_kinds.iter().copied())
    {
        let function = input.function;
        let descr = output.get_function_by_id(*id).unwrap();
        let module_env = ModuleEnv::new(output, others);
        let mut new_deps = FxHashSet::default();
        let expected_ret_ty = descr.definition.ty_scheme.ty.ret;
        let expected_span = descr.spans.as_ref().unwrap().args_span;
        let mut lambda_functions = vec![];
        let mut locals = descr.gen_locals_no_bounds();
        let mut fn_arena = NodeArena::default();
        LocalDecl::assign_sequential_slots(&mut locals);
        let cur_locals = (0..locals.len()).map(LocalDeclId::from_index).collect();
        let mut ty_env = TypingEnv::new(
            &mut locals,
            cur_locals,
            &mut new_deps,
            module_env,
            Some((expected_ret_ty, expected_span)),
            descr.definition.result_convention,
            (!annotation_subst.0.is_empty() || !annotation_subst.1.is_empty())
                .then_some(annotation_subst),
            vec![],
            !attrs.no_fuel_check,
            &mut lambda_functions,
            output.functions.len() as u32,
            desugared_arena,
            &mut fn_arena,
        );
        ty_env.function_name = Some(function.name.0);
        if let EmitFunctionKind::SubscriptMember { subscript_name, .. } = kind {
            ty_env.subscript_member = Some(SubscriptMemberTypingContext {
                name: subscript_name,
                requires_mutable_place: kind.requires_mutable_place(),
            });
        }
        ty_env.compilation_capabilities = capabilities;
        if descr.definition.result_convention.requires_yield_driver() {
            ty_env.yield_context = Some(crate::types::typing_env::YieldTypingContext::new(
                expected_ret_ty,
                expected_span,
                kind.requires_mutable_yield(),
            ));
        }
        let mut fn_node_id = ty_inf.check_expr(
            &mut ty_env,
            function.body,
            kind.body_expected_ty(descr.definition.ty_scheme.ty.ret),
            MutType::constant(),
            expected_span,
        )?;
        let yield_node_id =
            ty_env
                .yield_context
                .take()
                .and_then(|ctx| match ctx.yielded_nodes.as_slice() {
                    [node] => Some(*node),
                    _ => None,
                });
        if descr.definition.result_convention.requires_yield_driver() && yield_node_id.is_none() {
            return Err(internal_compilation_error!(InvalidSubscriptDefinition {
                subject: match kind {
                    EmitFunctionKind::SubscriptMember { subscript_name, .. } => {
                        SubscriptDefinitionSubject::SubscriptMember(subscript_name)
                    }
                    EmitFunctionKind::Normal => {
                        SubscriptDefinitionSubject::AddressorFunction(Some(function.name.0))
                    }
                },
                kind: InvalidSubscriptDefinitionKind::ScopedMemberMustYieldExactlyOnce,
                span: function.span,
            }));
        }
        if let Some(yield_node_id) = yield_node_id
            && !yield_path_is_block_structured(&fn_arena, fn_node_id, yield_node_id)
        {
            return Err(internal_compilation_error!(UnsupportedSubscriptFeature {
                kind: UnsupportedSubscriptFeatureKind::YieldInNonBlockStructuredControlFlow,
                span: fn_arena[yield_node_id].span,
            }));
        }
        fn_node_id = wrap_body_with_call_depth_check_if_recursive(
            &mut ty_inf,
            &mut fn_arena,
            fn_node_id,
            &recursive_function_ids,
            descr.definition.ty_scheme.ty.ret,
            function.name.1,
            expected_span,
        );
        lambda_functions.drain(..).for_each(|function| {
            let lambda_id =
                add_pending_function_anonymous(output, &mut pending_functions, function);
            output.name_function_with_visibility(
                lambda_id,
                format!("{GENERATED_LAMBDA_PREFIX}{}", lambda_id.as_index()).into(),
                Visibility::Module,
            );
            associated_lambdas.entry(*id).or_default().push(lambda_id);
        });
        let descr = output.get_function_by_id_mut(*id).unwrap();
        descr.definition.ty_scheme.ty.effects = ty_inf.unify_effects(
            &fn_arena[fn_node_id].effects,
            &descr.definition.ty_scheme.ty.effects,
        );
        let mut pending = PendingModuleFunction::from_body_with_name(
            Some(function.name.0),
            descr.definition.clone(),
            PendingFunctionBody::new(fn_arena, fn_node_id).with_yield_node_id(yield_node_id),
            descr.definition.arg_names.len(),
            descr.spans.clone(),
            locals,
        );
        if let EmitFunctionKind::SubscriptMember { subscript_name, .. } = kind {
            pending = pending.with_subscript_member_name(subscript_name);
        }
        set_pending_function(output, &mut pending_functions, *id, pending);
        output.deps.extend(new_deps);
    }
    let module_env = ModuleEnv::new(output, others);
    ty_inf.log_debug_constraints(module_env);

    if let (Some(trait_ctx), Some(trait_output)) = (&trait_ctx, &trait_output) {
        let trait_effect_subst = trait_ctx
            .trait_def
            .effect_param_subst_for_effs(&trait_output.output_effs);
        for (method_index, id) in local_fns.iter().enumerate() {
            let method_index = TraitMethodIndex::from_index(method_index);
            let descr = output.get_function_by_id(*id).unwrap();
            let (method_name, trait_method_def) = trait_ctx.trait_def.method(method_index);
            let trait_effects = trait_method_def
                .ty_scheme
                .ty
                .effects
                .instantiate(&trait_effect_subst);
            let impl_effects = &descr.definition.ty_scheme.ty.effects;
            let span = descr
                .spans
                .as_ref()
                .map_or(trait_ctx.span, |spans| spans.span);
            ty_inf.add_effect_dep_constraint_with_origin(
                impl_effects,
                span,
                &trait_effects,
                trait_ctx.span,
                EffectConstraintOrigin::TraitMethodImpl {
                    trait_id: trait_ctx.trait_id,
                    method_name: *method_name,
                    impl_span: span,
                },
            )?;
        }
    }

    // Third pass, perform the unification.
    let mut solver = trait_solver_from_module!(output, others);
    let mut ty_inf = ty_inf.unify(&mut solver, solver_arena)?;
    let generated = solver.commit(
        &mut output.functions,
        &mut output.def_table,
        &mut pending_functions,
    );
    elaborate_generated_functions(output, others, &mut pending_functions, generated)?;
    let module_env = ModuleEnv::new(output, others);
    ty_inf.log_debug_substitution_tables(module_env);
    ty_inf.log_debug_constraints(module_env);

    // Resolve local-storage decisions before defaulting so only finalized ownership semantics add `Value`.
    let value_trait_id =
        module_env.expect_std_trait_id(crate::std::core_traits_names::VALUE_TRAIT_NAME);
    for id in local_fns.iter() {
        for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
            let descr = pending_functions
                .get_mut(&function_id)
                .expect("expected pending function body");
            ty_inf.resolve_local_storage_and_activate_value_constraints(
                &descr.code.arena,
                descr.code.entry_node_id,
                &mut descr.locals,
                value_trait_id,
            );
        }
    }

    // Fourth pass: default orphan constraints and substitute types.
    if let Some(mut trait_output) = trait_output {
        // Default orphan constraints for the trait implementation into the unification tables.
        {
            let input_tys = ty_inf.substitute_in_types(&trait_output.input_tys);
            let output_tys = ty_inf.substitute_in_types(&trait_output.output_tys);
            let mut head_tys = input_tys.clone();
            head_tys.extend(output_tys.iter().copied());
            let head_quantifiers = collect_ty_vars(&head_tys);
            ty_inf.normalize_remaining_constraints();
            let head_boundary =
                ConstraintBoundary::from_seed_ty_vars(head_quantifiers.iter().copied());
            let orphan_constraints =
                head_boundary.owned_inaccessible_constraints(ty_inf.remaining_constraints());
            let scope = DefaultingScope::from_constraints(&orphan_constraints);
            let mut solver = trait_solver_from_module!(output, others);
            ty_inf.resolve_defaults_to_fixed_point(&scope, &mut solver, solver_arena)?;
            let generated = solver.commit(
                &mut output.functions,
                &mut output.def_table,
                &mut pending_functions,
            );
            elaborate_generated_functions(output, others, &mut pending_functions, generated)?;

            ty_inf.finalize_effect_dependencies()?;

            // Check for remaining orphans.
            ty_inf.normalize_remaining_constraints();
            let input_tys = ty_inf.substitute_in_types(&trait_output.input_tys);
            let output_tys = ty_inf.substitute_in_types(&trait_output.output_tys);
            let mut head_tys = input_tys.clone();
            head_tys.extend(output_tys.iter().copied());
            let head_quantifiers = collect_ty_vars(&head_tys);
            let head_boundary =
                ConstraintBoundary::from_seed_ty_vars(head_quantifiers.iter().copied());
            let module_env = ModuleEnv::new(output, others);
            let remaining_orphans: Vec<_> = head_boundary
                .inaccessible_constraints(ty_inf.remaining_constraints())
                .into_iter()
                .filter(|c| !c.is_type_has_variant())
                .filter(|c| !is_compiler_provided_value_constraint(c, module_env))
                .collect();
            if !remaining_orphans.is_empty() {
                let fake_current =
                    new_module_using_std(ModuleId(0), crate::module::Path::single_str("$debug"));
                let env = ModuleEnv::new(&fake_current, others);
                return Err(internal_compilation_error!(Internal {
                    error: format!(
                        "Orphan constraints found in trait impl: {}",
                        remaining_orphans.format_with(&env)
                    ),
                    span: remaining_orphans[0].use_site(),
                }));
            }
        }

        // Substitute everything using ty_inf (single pass, includes all defaults).
        substitute_and_canonicalize_functions(
            output,
            &mut pending_functions,
            &associated_lambdas,
            &local_fns,
            &mut ty_inf,
        );
        default_output_effects_in_functions(
            output,
            &mut pending_functions,
            &associated_lambdas,
            &local_fns,
        );

        // Resolve input and output types and output effects.
        ty_inf.substitute_in_types_in_place(&mut trait_output.input_tys);
        ty_inf.substitute_in_types_in_place(&mut trait_output.output_tys);
        let output_eff_slot_roots = trait_output
            .output_effs
            .iter()
            .map(|eff| {
                eff.to_single_variable()
                    .map(|var| ty_inf.effect_var_root(var))
            })
            .collect::<Vec<_>>();
        ty_inf.substitute_in_effect_types_in_place(&mut trait_output.output_effs);
        match explicit_trait_impl
            .as_ref()
            .map(|(_, _, explicit_output_effs, _)| explicit_output_effs.as_slice())
        {
            Some(explicit_output_effs) if !explicit_output_effs.is_empty() => {
                let explicit_output_effs = ty_inf.substitute_in_effect_types(explicit_output_effs);
                trait_output.output_effs = trait_output
                    .output_effs
                    .iter()
                    .zip(explicit_output_effs)
                    .zip(output_eff_slot_roots)
                    .map(|((slot_eff, mut explicit_eff), slot_root)| {
                        // The explicit associated output-effect expression is
                        // the impl head. Trait output slots are inference
                        // placeholders used while checking method bodies; keep
                        // real inferred lower bounds, but do not leak the slot
                        // placeholder itself into the public impl output.
                        for effect in slot_eff.iter() {
                            if matches!(effect, Effect::Variable(var) if Some(var) == slot_root) {
                                continue;
                            }
                            explicit_eff.insert(effect);
                        }
                        explicit_eff
                    })
                    .collect();
            }
            _ => {
                // Without explicit output-effect bindings, any output effect
                // slot left unconstrained by the methods resolves to empty.
                for eff in &mut trait_output.output_effs {
                    *eff = EffType::multiple_primitive(&eff.inner_non_vars());
                }
            }
        }

        // Take final substituted constraints.
        ty_inf.normalize_remaining_constraints();
        let all_constraints = ty_inf.take_constraints();

        // Validate that each method's effects are a subset of the trait definition's effects,
        // and override them with the trait's effects.
        // This ensures ABI consistency: the calling convention is determined by the trait definition.
        let trait_ctx = trait_ctx.unwrap();
        let trait_id = trait_ctx.trait_id;
        let trait_def = &trait_ctx.trait_def;
        let trait_effect_subst = trait_def.effect_param_subst_for_effs(&trait_output.output_effs);
        for (i, id) in local_fns.iter().enumerate() {
            let i = TraitMethodIndex::from_index(i);
            let descr = &mut output.functions[id.as_index()];
            let (_, trait_method_def) = trait_def.method(i);
            let trait_effects = &trait_method_def
                .ty_scheme
                .ty
                .effects
                .instantiate(&trait_effect_subst);
            // Override the function's effects with the trait's effects for ABI consistency.
            descr.definition.ty_scheme.ty.effects = trait_effects.clone();
        }

        // Store the functions in the trait output.
        trait_output.functions = local_fns.clone();

        // Compute quantifiers from input types and constraints.
        let mut head_tys = trait_output.input_tys.clone();
        head_tys.extend(trait_output.output_tys.iter().copied());
        let input_quantifiers = collect_ty_vars(&head_tys);
        let head_boundary =
            ConstraintBoundary::from_seed_ty_vars(input_quantifiers.iter().copied());
        let related_constraints = head_boundary.accessible_constraints(&all_constraints);
        let mut quantifiers = input_quantifiers.to_vec();
        let mut collector = TyVarsCollector(&mut quantifiers);
        for constraint in related_constraints.iter() {
            constraint.visit(&mut collector);
        }
        quantifiers = quantifiers.into_iter().unique().collect();

        // Detect unbound type variables in the code and return error if not in unused variants only.
        let mut unbound_subst = FxHashMap::default();
        for id in local_fns.iter() {
            let pending = pending_functions
                .get(id)
                .expect("expected pending function body");
            let unbound = hir::all_unbound_ty_vars(&pending.code.arena, pending.code.entry_node_id);
            let env = ModuleEnv::new(output, others);
            let uninstantiated_unbound = check_unbounds(unbound, &quantifiers, &env)?;
            unbound_subst.extend(
                uninstantiated_unbound
                    .into_iter()
                    .map(|ty_var| (ty_var, Type::never())),
            );
        }

        // Update quantifiers and constraints with unbound substitution.
        quantifiers.retain(|ty_var| !unbound_subst.contains_key(ty_var));
        trait_output.ty_var_count = quantifiers.len() as u32;
        let mut subst = (unbound_subst, FxHashMap::default());
        let subst_size = subst.0.len();
        let mut solver = trait_solver_from_module!(output, others);
        trait_output.constraints = all_constraints
            .iter()
            .filter_map(|constraint| {
                constraint
                    .instantiate_and_drop_if_solved(&mut subst, &mut solver, solver_arena)
                    .transpose()
            })
            .collect::<Result<_, _>>()?;
        let generated = solver.commit(
            &mut output.functions,
            &mut output.def_table,
            &mut pending_functions,
        );
        elaborate_generated_functions(output, others, &mut pending_functions, generated)?;
        // Make sure substitution is not due to constraint processing.
        assert_eq!(subst_size, subst.0.len());

        // Apply unbound substitution to code and types.
        if !subst.0.is_empty() {
            let mut mapper = BitmapInstantiationMapper::new(&subst);
            instantiate_types_in_place(&mut trait_output.input_tys, &mut mapper);
            instantiate_types_in_place(&mut trait_output.output_tys, &mut mapper);
            for id in local_fns.iter() {
                for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                    let descr = &mut output.functions[function_id.as_index()];
                    descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
                    let pending = pending_functions
                        .get_mut(&function_id)
                        .expect("expected pending function body");
                    pending.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.clone();
                    instantiate_function_descr_in_place(pending, &mut mapper);
                }
            }
        }

        let mut effect_quantifiers = FxHashSet::default();
        for ty in &trait_output.input_tys {
            ty.fill_with_inner_effect_vars(&mut effect_quantifiers);
        }
        for ty in &trait_output.output_tys {
            ty.fill_with_inner_effect_vars(&mut effect_quantifiers);
        }
        for eff in &trait_output.output_effs {
            eff.fill_with_inner_effect_vars(&mut effect_quantifiers);
        }
        let mut effect_quantifiers = effect_quantifiers.into_iter().sorted().collect::<Vec<_>>();
        trait_output.eff_var_count = effect_quantifiers.len() as u32;

        // Fifth pass, normalize the input types/effects, substitute the types in the functions and input/output types.
        let subst = (
            normalize_types(&mut quantifiers),
            normalize_effect_vars(&mut effect_quantifiers),
        );
        let mut mapper = BitmapInstantiationMapper::new(&subst);
        instantiate_types_in_place(&mut trait_output.input_tys, &mut mapper);
        instantiate_types_in_place(&mut trait_output.output_tys, &mut mapper);
        for eff in &mut trait_output.output_effs {
            *eff = mapper.map_effect_type(eff);
        }
        instantiate_types_in_place(&mut trait_output.constraints, &mut mapper);
        for (method_index, id) in local_fns.iter().enumerate() {
            let method_index = TraitMethodIndex::from_index(method_index);
            for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                let descr = &mut output.functions[function_id.as_index()];
                descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
                descr.definition.ty_scheme.ty_quantifiers = quantifiers.clone();
                let eff_quantifiers = descr.definition.ty_scheme.ty.input_effect_vars();
                descr.definition.ty_scheme.eff_quantifiers = eff_quantifiers;
                descr.definition.ty_scheme.constraints = trait_output.constraints.clone();
                let pending = pending_functions
                    .get_mut(&function_id)
                    .expect("expected pending function body");
                pending.definition = descr.definition.clone();
                instantiate_function_descr_in_place(pending, &mut mapper);
            }

            // Name the function
            let qualified_name_env = QualifiedNameEnv::new_from_module(output, others);
            let name = qualified_name_env
                .disambiguated_impl_method_name(
                    trait_id,
                    trait_def,
                    method_index,
                    &trait_output.input_tys,
                    &trait_output.output_tys,
                    &trait_output.output_effs,
                    trait_output.ty_var_count,
                    trait_output.eff_var_count,
                    &trait_output.constraints,
                )
                .into();
            output.name_function(*id, name);
        }

        // Sixth pass, run the borrow checker and elaborate into the final HIR arena.
        let dicts = extra_parameters_from_constraints(
            &trait_output.constraints,
            ModuleEnv::new(output, others),
        );
        let mut module_inst_data = FxHashMap::default();
        for id in local_fns.iter() {
            insert_inst_data_for_function_and_lambdas(
                &mut module_inst_data,
                &associated_lambdas,
                *id,
                dicts.clone(),
            );
        }
        for id in local_fns.iter() {
            borrow_check_and_elaborate_dict(
                output,
                others,
                &mut pending_functions,
                &associated_lambdas,
                &dicts,
                &module_inst_data,
                id,
            )?;
        }

        refresh_debug_info_for_functions(output, &associated_lambdas, &local_fns);
        Ok(Some(trait_output))
    } else {
        // We are emitting normal module functions.

        // Default orphan constraints for each function into the unification tables.
        for (id, explicit_root_tys) in local_fns.iter().zip(function_explicit_root_tys.iter()) {
            let descr = &output.functions[id.as_index()];
            let fn_ty = ty_inf.substitute_in_fn_type(&descr.definition.ty_scheme.ty);
            let mut sig_ty_vars = fn_ty.inner_ty_vars();
            sig_ty_vars.extend(
                explicit_root_tys
                    .iter()
                    .flat_map(|ty| ty_inf.substitute_in_type(*ty).inner_ty_vars().into_iter())
                    .collect::<Vec<_>>(),
            );
            sig_ty_vars = sig_ty_vars.into_iter().unique().collect();
            ty_inf.normalize_remaining_constraints();
            let sig_boundary = ConstraintBoundary::from_seed_ty_vars(sig_ty_vars.iter().copied());
            let orphan_constraints =
                sig_boundary.owned_inaccessible_constraints(ty_inf.remaining_constraints());
            let mut solver = trait_solver_from_module!(output, others);
            // If the signature still exposes type variables, it defines the boundary for
            // defaulting and body-local `None`/unit evidence must not bias it.
            // Only functions with no remaining signature boundary can use their body root
            // to seed the narrow unit-constructor fallback.
            let unit_variant_seed_tys = if sig_ty_vars.is_empty() {
                pending_functions
                    .get(id)
                    .map(|function| {
                        UnifiedTypeInference::collect_unit_variant_seed_types(
                            &function.code.arena,
                            function.code.entry_node_id,
                        )
                    })
                    .unwrap_or_default()
            } else {
                Vec::new()
            };
            let scope = DefaultingScope::from_constraints(&orphan_constraints)
                .with_unit_variant_seed_tys(unit_variant_seed_tys);
            ty_inf.resolve_defaults_to_fixed_point(&scope, &mut solver, solver_arena)?;
            let generated = solver.commit(
                &mut output.functions,
                &mut output.def_table,
                &mut pending_functions,
            );
            elaborate_generated_functions(output, others, &mut pending_functions, generated)?;
        }
        for (id, explicit_root_tys) in local_fns.iter().zip(function_explicit_root_tys.iter()) {
            let descr = &output.functions[id.as_index()];
            let fn_ty = ty_inf.substitute_in_fn_type(&descr.definition.ty_scheme.ty);
            let mut sig_ty_vars = fn_ty.inner_ty_vars();
            sig_ty_vars.extend(
                explicit_root_tys
                    .iter()
                    .flat_map(|ty| ty_inf.substitute_in_type(*ty).inner_ty_vars().into_iter())
                    .collect::<Vec<_>>(),
            );
            sig_ty_vars = sig_ty_vars.into_iter().unique().collect();
            ty_inf.normalize_remaining_constraints();
            let sig_boundary = ConstraintBoundary::from_seed_ty_vars(sig_ty_vars.iter().copied());
            let module_env = ModuleEnv::new(output, others);
            let remaining_orphans: Vec<_> = sig_boundary
                .inaccessible_constraints(ty_inf.remaining_constraints())
                .into_iter()
                .filter(|c| !c.is_type_has_variant())
                .filter(|c| !is_compiler_provided_value_constraint(c, module_env))
                .collect();
            if !remaining_orphans.is_empty() {
                let fake_current =
                    new_module_using_std(ModuleId(0), crate::module::Path::single_str("$debug"));
                let env = ModuleEnv::new(&fake_current, others);
                return Err(internal_compilation_error!(Internal {
                    error: format!(
                        "Orphan constraints found in module fn: {}",
                        remaining_orphans.format_with(&env)
                    ),
                    span: remaining_orphans[0].use_site(),
                }));
            }
        }

        ty_inf.finalize_effect_dependencies()?;

        // Substitute everything using ty_inf (single pass, includes all defaults).
        substitute_and_canonicalize_functions(
            output,
            &mut pending_functions,
            &associated_lambdas,
            &local_fns,
            &mut ty_inf,
        );

        // Recursive-return defaulting inspects the final constraints.
        ty_inf.normalize_remaining_constraints();
        default_unconstrained_diverging_returns_to_never(
            output,
            &mut ty_inf,
            DivergingReturnDefaultingInputs {
                ast_functions: ast_functions(),
                local_fns: &local_fns,
                function_explicit_root_tys: &function_explicit_root_tys,
                recursive_function_ids: &recursive_function_ids,
                associated_lambdas: &associated_lambdas,
                pending_functions: &mut pending_functions,
            },
        );
        // Take final substituted constraints.
        let all_constraints = ty_inf.take_constraints();

        // For each function: filter constraints, check unbounds, finalize type scheme.
        let mut used_constraints: FxHashSet<PubTypeConstraintPtr> = FxHashSet::default();
        for ((input, id), explicit_root_tys) in ast_functions()
            .zip(local_fns.iter())
            .zip(function_explicit_root_tys.iter())
        {
            let function = input.function;
            let descr = &output.functions[id.as_index()];
            let pending = pending_functions
                .get(id)
                .expect("expected pending function body");

            // Find constraints related to this function's signature.
            let mut sig_ty_vars = descr.definition.ty_scheme.ty.inner_ty_vars();
            let explicit_ty_vars = explicit_root_tys
                .iter()
                .flat_map(|ty| ty_inf.substitute_in_type(*ty).inner_ty_vars().into_iter())
                .collect::<Vec<_>>();
            sig_ty_vars.extend(explicit_ty_vars.iter().copied());
            sig_ty_vars = sig_ty_vars.into_iter().unique().collect();
            let sig_boundary = ConstraintBoundary::from_seed_ty_vars(sig_ty_vars.iter().copied());
            let related_constraints = sig_boundary.accessible_constraints(&all_constraints);
            let related_ptrs: FxHashSet<PubTypeConstraintPtr> = related_constraints
                .iter()
                .map(|c| constraint_ptr(c))
                .collect();
            for ptr in &related_ptrs {
                used_constraints.insert(*ptr);
            }

            // Compute quantifiers.
            let mut quantifiers = TypeScheme::list_ty_vars(
                &descr.definition.ty_scheme.ty,
                related_constraints.iter().copied(),
            );
            quantifiers.extend(explicit_ty_vars.iter().copied());
            quantifiers = quantifiers.into_iter().unique().collect();

            // Check for unbound type variables.
            let unbound = hir::all_unbound_ty_vars(&pending.code.arena, pending.code.entry_node_id);
            let env = ModuleEnv::new(output, others);
            let uninstantiated_unbound = check_unbounds(unbound, &quantifiers, &env)?;

            // Apply unbound→Never fixup if needed.
            if !uninstantiated_unbound.is_empty() {
                let fixup_subst: (TypeInstSubst, FxHashMap<_, _>) = (
                    uninstantiated_unbound
                        .iter()
                        .map(|v| (*v, Type::never()))
                        .collect(),
                    FxHashMap::default(),
                );
                let mut mapper = BitmapInstantiationMapper::new(&fixup_subst);
                for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                    let pending = pending_functions
                        .get_mut(&function_id)
                        .expect("expected pending function body");
                    instantiate_function_descr_in_place(pending, &mut mapper);
                }
                quantifiers.retain(|v| !uninstantiated_unbound.contains(v));
            }

            // Filter and finalize constraints.
            let mut solver = trait_solver_from_module!(output, others);
            let mut drop_subst = (FxHashMap::default(), FxHashMap::default());
            let constraints: Vec<_> = all_constraints
                .iter()
                .filter(|c| related_ptrs.contains(&constraint_ptr(c)))
                .filter_map(|constraint| {
                    constraint
                        .instantiate_and_drop_if_solved(&mut drop_subst, &mut solver, solver_arena)
                        .transpose()
                })
                .collect::<Result<_, _>>()?;
            let generated = solver.commit(
                &mut output.functions,
                &mut output.def_table,
                &mut pending_functions,
            );
            elaborate_generated_functions(output, others, &mut pending_functions, generated)?;

            // Write the final type scheme.
            let explicit_ty_vars = explicit_ty_vars
                .iter()
                .copied()
                .unique()
                .collect::<Vec<_>>();
            quantifiers = explicit_ty_vars
                .iter()
                .copied()
                .chain(
                    quantifiers
                        .into_iter()
                        .filter(|ty_var| !explicit_ty_vars.contains(ty_var)),
                )
                .collect();
            for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                let descr = &mut output.functions[function_id.as_index()];
                descr.definition.ty_scheme.ty_quantifiers = quantifiers.clone();
                descr.definition.ty_scheme.eff_quantifiers =
                    descr.definition.ty_scheme.ty.input_effect_vars();
                descr.definition.ty_scheme.constraints = constraints.clone();
                descr.definition.generic_params = function.generic_params.type_params().to_vec();
                descr.definition.generic_effect_params =
                    function.generic_params.effect_params().to_vec();
                pending_functions
                    .get_mut(&function_id)
                    .expect("expected pending function body")
                    .definition = descr.definition.clone();
            }

            // Log dropped constraints.
            if log_enabled!(log::Level::Debug) {
                let module_env = ModuleEnv::new(output, others);
                let retained_ptrs: FxHashSet<PubTypeConstraintPtr> =
                    constraints.iter().map(constraint_ptr).collect();
                log_dropped_constraints_module(
                    function.name.0,
                    &all_constraints,
                    &related_ptrs,
                    &retained_ptrs,
                    module_env,
                );
            }
        }

        default_output_effects_in_functions(
            output,
            &mut pending_functions,
            &associated_lambdas,
            &local_fns,
        );

        // Safety check: make sure that there are no unused constraints.
        let module_env = ModuleEnv::new(output, others);
        let unused_constraints = all_constraints
            .iter()
            .filter(|c| {
                !used_constraints.contains(&constraint_ptr(c))
                    && !c.is_type_has_variant()
                    && !is_compiler_provided_value_constraint(c, module_env)
            })
            .collect::<Vec<_>>();
        if !unused_constraints.is_empty() {
            let module_env = ModuleEnv::new(output, others);
            let constraints = unused_constraints
                .iter()
                .map(|c| c.format_with(&module_env))
                .join(" ∧ ");
            return Err(internal_compilation_error!(Internal {
                error: format!("Unused constraints in module compilation: {}", constraints),
                span: unused_constraints[0].use_site(),
            }));
        }

        // Fifth pass, normalize the type schemes, substitute the types in the functions.
        for id in local_fns.iter() {
            let descr = &mut output.functions[id.as_index()];
            let subst = descr.definition.ty_scheme.normalize();
            let normalized_scheme = descr.definition.ty_scheme.clone();
            for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                let descr = &mut output.functions[function_id.as_index()];
                let mut mapper = BitmapInstantiationMapper::new(&subst);
                if function_id != *id {
                    descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
                    descr.definition.ty_scheme.ty_quantifiers =
                        normalized_scheme.ty_quantifiers.clone();
                    descr.definition.ty_scheme.eff_quantifiers =
                        normalized_scheme.eff_quantifiers.clone();
                    descr.definition.ty_scheme.constraints = normalized_scheme.constraints.clone();
                }
                let pending = pending_functions
                    .get_mut(&function_id)
                    .expect("expected pending function body");
                pending.definition = descr.definition.clone();
                instantiate_function_descr_in_place(pending, &mut mapper);
                default_body_only_effects_in_function_descr(pending);
            }
        }

        // Sixth pass, run the borrow checker and elaborate into the final HIR arena.
        let mut module_inst_data = FxHashMap::default();
        for id in local_fns.iter() {
            let descr = &output.functions[id.as_index()];
            let dicts = descr
                .definition
                .ty_scheme
                .extra_parameters(ModuleEnv::new(output, others));
            insert_inst_data_for_function_and_lambdas(
                &mut module_inst_data,
                &associated_lambdas,
                *id,
                dicts,
            );
        }
        for id in local_fns.iter() {
            let dicts = module_inst_data.get(id).unwrap();
            borrow_check_and_elaborate_dict(
                output,
                others,
                &mut pending_functions,
                &associated_lambdas,
                dicts,
                &module_inst_data,
                id,
            )?;
        }

        refresh_debug_info_for_functions(output, &associated_lambdas, &local_fns);
        Ok(None)
    }
}

/// Check all unbound variables from unbound that are not in bounds,
/// and if they are not only seen in variants, return an error.
pub(super) fn check_unbounds(
    unbound: IndexMap<TypeVar, hir::UnboundTyCtxs>,
    bounds: &[TypeVar],
    env: &ModuleEnv<'_>,
) -> Result<FxHashSet<TypeVar>, InternalCompilationError> {
    let mut uninstantiated_unbound = FxHashSet::default();
    for (ty_var, ctxs) in unbound {
        if !bounds.contains(&ty_var) {
            if ctxs.seen_only_in_variants(ty_var, env) {
                uninstantiated_unbound.insert(ty_var);
            } else {
                let (ty, span) = ctxs.first();
                return Err(internal_compilation_error!(UnboundTypeVar {
                    ty_var,
                    ty,
                    span
                }));
            }
        }
    }
    Ok(uninstantiated_unbound)
}
