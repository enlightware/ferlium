// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{borrow::Cow, cell::Cell, cmp::min, collections::hash_map::Entry, slice};

use indexmap::IndexMap;
use itertools::Itertools;
use log::log_enabled;
use ustr::Ustr;

use super::emit_subscripts::attach_subscript_member;
use crate::{
    FxHashMap, FxHashSet, Location, Modules,
    ast::{self, DExprArena, DModuleFunctionArg},
    compiler::{
        CompilationCapabilities,
        diagnostics::CompilationWarning,
        error::{
            AttributeTarget, CompilationErrorImpl, GenericParamsOwner, InternalCompilationError,
            InvalidAttributeKind, InvalidGenericParamsKind, InvalidSubscriptDefinitionKind,
            InvalidTraitDefinitionKind, MissingRequirement, SubscriptDefinitionSubject,
            UnsafeFeature, UnsupportedSubscriptFeatureKind,
        },
        lints::report_needless_returns_in_tail,
    },
    format::FormatWith,
    hir::{
        self, NodeArena,
        dictionary::LateFunctionInstData,
        elaboration::elaborate_generated_functions,
        emit_hir::{
            ImplStubData, PendingModuleFunctions, PubTypeConstraintPtr,
            add_pending_function_anonymous, borrow_check_and_elaborate_dict, constraint_ptr,
            default_body_only_effects_in_function_descr, default_output_effects_in_functions,
            default_unconstrained_types_to_never, first_unbound_type_in_constraints,
            function_and_associated_lambdas, insert_inst_data_for_function_and_lambdas,
            instantiate_function_descr_in_place, is_compiler_provided_value_constraint,
            log_dropped_constraints_module, refresh_debug_info_for_functions, set_pending_function,
            substitute_and_canonicalize_functions,
        },
        function::{CallableDefinition, arg_conventions_for_args},
        hir_syn,
    },
    internal_compilation_error,
    module::{
        DictionaryEntryRequirements, FunctionId, GENERATED_LAMBDA_PREFIX, ImplGenericNames,
        LocalDecl, LocalDeclId, LocalFunctionId, LocalSubscriptId, Module, ModuleCheckpoint,
        ModuleEnv, ModuleFunction, ModuleFunctionSpans, PendingFunctionBody, PendingModuleFunction,
        ProjectionKey, QualifiedNameEnv, SubscriptMemberFunctionKind, SubscriptMemberKind,
        SubscriptSignature, TraitId, Visibility, YieldProvenance, id::Id,
    },
    std::core_traits_names::VALUE_TRAIT_NAME,
    types::{
        effect_polarity::trait_output_effect_polarities,
        effects::{EffType, Effect, EffectVar, EffectsInstSubst},
        mutability::MutType,
        r#trait::{Trait, TraitDefaultMethod, TraitMethodIndex},
        trait_solver::{EvidencePlan, TraitSolver, trait_solver_from_module},
        r#type::{
            CallResultConvention, FnArgType, FnType, Type, TypeDisplayEnv, TypeInstSubst, TypeVar,
        },
        type_constraints::named_type_constraints_in_types,
        type_inference::{
            defaulting::{ConstraintBoundary, DefaultingScope},
            effect_solver::EffectConstraintOrigin,
            expr::{AnnotationTypeMapper, TypeInference},
            signature::check_declared_signature,
            substitution::InstSubst,
            unify::UnifiedTypeInference,
        },
        type_like::{TypeLike, instantiate_types_in_place},
        type_mapper::{BitmapInstantiationMapper, EffectErasingMapper, TypeMapper},
        type_scheme::{
            PubTypeConstraint, TypeScheme, extra_parameters_from_constraints, normalize_types,
        },
        type_visitor::{TyVarsCollector, collect_ty_vars},
        typing_env::{SubscriptMemberTypingContext, TypingEnv, YieldTypingContext},
    },
};

/// Context passed to emit_functions when a trait implementation is being emitted.
pub(super) struct EmitTraitCtx<'a> {
    pub(super) trait_id: TraitId,
    pub(super) trait_def: Trait,
    pub(super) span: Location,
    pub(super) stub_data: Option<&'a ImplStubData>,
    pub(super) generic_type_params: &'a [ast::UstrSpan],
    pub(super) generic_effect_param_names: Vec<Ustr>,
    pub(super) for_trait: Option<&'a ast::DTraitImplFor>,
    pub(super) impl_constraints: &'a [PubTypeConstraint],
}

pub(crate) struct EmitTraitOutput {
    pub(crate) evidence_plan: EvidencePlan,
    pub(crate) input_tys: Vec<Type>,
    pub(crate) output_tys: Vec<Type>,
    pub(crate) output_effs: Vec<EffType>,
    pub(crate) ty_var_count: u32,
    pub(crate) eff_var_count: u32,
    pub(crate) constraints: Vec<PubTypeConstraint>,
    pub(crate) functions: Vec<LocalFunctionId>,
    pub(crate) method_requirements: Vec<DictionaryEntryRequirements>,
    pub(crate) generic_names: ImplGenericNames,
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
        subscript_id: LocalSubscriptId,
        subscript_name: Ustr,
        projection_key: Option<ProjectionKey>,
        member_function_kind: SubscriptMemberFunctionKind,
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
    pub(super) trait_default: Option<(TraitId, TraitMethodIndex)>,
    pub(super) forward_default: Option<FunctionId>,
    pub(super) subscript: Option<&'a ast::DSubscriptDefinition>,
    pub(super) subscript_attachments: &'a [SubscriptMemberAttachment],
}

impl<'a> EmitFunctionInput<'a> {
    pub(super) fn normal(function: &'a ast::DModuleFunction) -> Self {
        Self {
            function,
            kind: EmitFunctionKind::Normal,
            trait_default: None,
            forward_default: None,
            subscript: None,
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
            } => CallResultConvention::YIELDED_ONCE,
            EmitFunctionKind::SubscriptMember {
                provenance: YieldProvenance::AddressorPlace,
                ..
            } => CallResultConvention::ADDRESSOR_PLACE,
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
    unsafe_allowed: bool,
) -> Result<FunctionAttributes, InternalCompilationError> {
    let mut no_fuel_check = false;
    let mut inline = false;
    for attribute in attributes {
        let attr_name = attribute.path.0;
        match attr_name.as_str() {
            "no_fuel_check" => {
                if !unsafe_allowed {
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
            "inline" => {
                if inline {
                    return Err(internal_compilation_error!(InvalidAttribute {
                        attribute_name: attr_name,
                        target: AttributeTarget::Function {
                            name: function_name,
                        },
                        kind: InvalidAttributeKind::Duplicate,
                        span: attribute.span,
                    }));
                }
                if attribute.items.is_empty() {
                    return Err(internal_compilation_error!(InvalidAttribute {
                        attribute_name: attr_name,
                        target: AttributeTarget::Function {
                            name: function_name,
                        },
                        kind: InvalidAttributeKind::MissingArguments,
                        span: attribute.span,
                    }));
                }
                if !matches!(
                    attribute.items.as_slice(),
                    [ast::MetaItem::Flag(value)] if value.0 == "never"
                ) {
                    return Err(internal_compilation_error!(InvalidAttribute {
                        attribute_name: attr_name,
                        target: AttributeTarget::Function {
                            name: function_name,
                        },
                        kind: InvalidAttributeKind::UnsupportedArguments,
                        span: attribute.span,
                    }));
                }
                inline = true;
            }
            _ => continue,
        }
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

fn map_annotation_type(ty_inf: &mut TypeInference, ty: Type, annotation_subst: &InstSubst) -> Type {
    ty.map(&mut AnnotationTypeMapper::new(
        ty_inf,
        Some(annotation_subst),
    ))
}

fn map_subscript_return_type(
    ty_inf: &mut TypeInference,
    ret_ty: Option<(Type, Location)>,
    annotation_subst: &InstSubst,
) -> Type {
    // An omitted return is a fresh variable, exactly like a function's; an explicit
    // annotation (including `_`, which desugars to a variable above all generics) is
    // mapped normally so `-> T` stays enforced.
    match ret_ty {
        None => ty_inf.fresh_type_var_ty(),
        Some((ret_ty, _)) => map_annotation_type(ty_inf, ret_ty, annotation_subst),
    }
}

fn map_annotation_mut_type(
    ty_inf: &mut TypeInference,
    mut_ty: MutType,
    annotation_subst: &InstSubst,
) -> MutType {
    AnnotationTypeMapper::new(ty_inf, Some(annotation_subst)).map_mut_type(mut_ty)
}

fn subscript_signature_from_source(
    ty_inf: &mut TypeInference,
    subscript: &ast::DSubscriptDefinition,
    annotation_subst: &InstSubst,
) -> SubscriptSignature {
    let (args, arg_names) = if let Some((receiver_ty, _)) = subscript.projection_receiver {
        (
            vec![FnArgType::new_by_val(map_annotation_type(
                ty_inf,
                receiver_ty,
                annotation_subst,
            ))],
            vec![
                subscript
                    .args
                    .first()
                    .expect("projection receiver binding should be validated")
                    .name
                    .0,
            ],
        )
    } else {
        (
            subscript
                .args
                .iter()
                .map(|arg| {
                    if let Some((mut_ty, ty, _)) = arg.ty {
                        let mut_ty = mut_ty
                            .map(|mut_ty| map_annotation_mut_type(ty_inf, mut_ty, annotation_subst))
                            .unwrap_or_else(MutType::constant);
                        FnArgType::new(map_annotation_type(ty_inf, ty, annotation_subst), mut_ty)
                    } else {
                        ty_inf.fresh_fn_arg()
                    }
                })
                .collect(),
            subscript.args.iter().map(|arg| arg.name.0).collect(),
        )
    };
    let mut mapper = BitmapInstantiationMapper::new(annotation_subst);
    let constraints = subscript
        .where_clause
        .iter()
        .map(|constraint| constraint.map(&mut mapper))
        .collect();
    SubscriptSignature {
        args,
        ret: map_subscript_return_type(ty_inf, subscript.ret_ty, annotation_subst),
        generic_params: subscript.generic_params.type_params().to_vec(),
        generic_effect_params: subscript.generic_params.effect_params().to_vec(),
        arg_names,
        constraints,
        doc: subscript.doc.clone(),
    }
}

fn update_subscript_signature_from_member_definition(
    output: &mut Module,
    subscript_id: LocalSubscriptId,
    projection_receiver: bool,
    member_definition: &CallableDefinition,
) {
    let mut signature = SubscriptSignature::from_callable_definition(member_definition);
    if projection_receiver {
        signature.normalize_projection_receiver();
    }
    let subscript = &mut output.subscripts[subscript_id.as_index()];
    subscript.set_resolved_signature(signature);
}

struct SharedSubscriptSignature {
    signature: SubscriptSignature,
    annotation_subst: InstSubst,
    explicit_root_tys: Vec<Type>,
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
    let defaults = unconstrained_diverging_returns(
        output,
        ty_inf,
        inputs.ast_functions,
        inputs.local_fns,
        inputs.function_explicit_root_tys,
        inputs.recursive_function_ids,
        inputs.pending_functions,
    );
    for (id, ret_var) in defaults {
        let subst: (TypeInstSubst, FxHashMap<_, _>) = (
            FxHashMap::from_iter([(ret_var, Type::never())]),
            FxHashMap::default(),
        );
        let mut mapper = BitmapInstantiationMapper::new(&subst);
        for function_id in function_and_associated_lambdas(&id, inputs.associated_lambdas) {
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

/// The functions whose return is an unconstrained variable that only diverges, either because the
/// body is `never` or because it only recurses into the group, with that variable.
fn unconstrained_diverging_returns<'func>(
    output: &Module,
    ty_inf: &mut UnifiedTypeInference,
    ast_functions: impl Iterator<Item = EmitFunctionInput<'func>>,
    local_fns: &[LocalFunctionId],
    function_explicit_root_tys: &[Vec<Type>],
    recursive_function_ids: &FxHashSet<FunctionId>,
    pending_functions: &PendingModuleFunctions,
) -> Vec<(LocalFunctionId, TypeVar)> {
    let mut defaults = Vec::new();
    for ((input, id), explicit_root_tys) in ast_functions
        .zip(local_fns.iter())
        .zip(function_explicit_root_tys.iter())
    {
        let function = input.function;
        if function.ret_ty.is_some() {
            continue;
        }

        let Some(pending) = pending_functions.get(id) else {
            continue;
        };

        // The body may not be substituted yet, as when a group's contracts are discovered.
        let body_is_never = ty_inf
            .substitute_in_type(pending.code.arena[pending.code.entry_node_id].ty)
            == Type::never();
        let unproductive_recursive = recursive_function_ids
            .contains(&FunctionId::new(output.module_id(), *id))
            && node_references_any_function(
                &pending.code.arena,
                pending.code.entry_node_id,
                recursive_function_ids,
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
        defaults.push((*id, ret_var));
    }
    defaults
}

/// `subst` extended for the requirements of a declaration: an output effect left unwritten in
/// one is inferred, so it gets a variable of its own. The annotations of the bodies keep `subst`,
/// in which no such effect has a variable.
fn with_unwritten_requirement_effects<'a>(
    mut subst: Cow<'a, InstSubst>,
    requirements: &[PubTypeConstraint],
    ty_inf: &mut TypeInference,
) -> Cow<'a, InstSubst> {
    for requirement in requirements {
        for var in requirement.inner_effect_vars().into_iter().sorted() {
            if !subst.1.contains_key(&var) {
                subst.to_mut().1.insert(var, ty_inf.fresh_effect_var_ty());
            }
        }
    }
    subst
}

/// The fixed signature of a function of a recursive group of functions.
#[derive(Debug, Clone)]
pub(super) struct GroupContract {
    scheme: TypeScheme<FnType>,
    /// The number of written effect generics: the `i`-th is the contract's variable `i`.
    written_count: usize,
    /// The contract's variable for each written type generic.
    written_types: Vec<TypeVar>,
    /// For each requirement of the scheme of a contract that a round read, its rank: 0 if the
    /// function makes it itself, and otherwise one more than the rank of the requirement of
    /// which it is an instance, in the contract of a function that this one names. Where
    /// several chains of references give one requirement, the rank is of the shortest. Empty
    /// for a shape.
    ranks: Vec<usize>,
}

impl GroupContract {
    /// The contract of a function that calls nothing, from its shape: an effect that it
    /// receives is any effect, and one that it only produces is none, as when a scheme is
    /// published.
    fn bottom(shape: &Self) -> Self {
        let subst = (
            FxHashMap::default(),
            shape
                .scheme
                .ty
                .positive_only_effect_vars()
                .into_iter()
                .map(|var| (var, EffType::empty()))
                .collect(),
        );
        let ty = shape
            .scheme
            .ty
            .map(&mut BitmapInstantiationMapper::new(&subst));
        Self {
            scheme: TypeScheme {
                ty_quantifiers: shape.scheme.ty_quantifiers.clone(),
                eff_quantifiers: ty.inner_effect_vars(),
                ty,
                constraints: Vec::new(),
            },
            written_count: shape.written_count,
            written_types: shape.written_types.clone(),
            ranks: Vec::new(),
        }
    }

    /// The requirements of the contract, each with its rank.
    fn ranked_requirements(&self) -> impl Iterator<Item = (&PubTypeConstraint, usize)> {
        self.scheme
            .constraints
            .iter()
            .zip(self.ranks.iter().copied())
    }

    /// Whether two contracts of one function, numbered alike, say the same: the same
    /// signature, and the same requirements at the same ranks.
    fn is_same_as(&self, other: &Self) -> bool {
        self.scheme.ty == other.scheme.ty
            && self.scheme.constraints.len() == other.scheme.constraints.len()
            && self.ranked_requirements().all(|requirement| {
                other
                    .ranked_requirements()
                    .any(|other| other == requirement)
            })
    }
}

/// What [`emit_functions`] produced.
enum Emitted {
    /// The functions of a group, in the module.
    Functions,
    /// The methods of a trait implementation, in the module, and what its impl is made of.
    TraitImpl(Box<EmitTraitOutput>),
    /// The shapes of the functions of a group; what the module got is to be undone.
    Shapes(Vec<GroupContract>),
}

/// How [`emit_functions`] treats a group.
pub(super) enum GroupMode<'a> {
    /// Infer the group jointly and emit it: a function that is not recursive, the methods of
    /// an implementation, or a recursive group with a default method of a trait or a member of
    /// a subscript.
    Normal,
    /// Infer jointly for types alone, effects being ignored, and only produce the shapes.
    Discover,
    /// Infer the bodies of a group jointly, once, against its shapes, each reference to one of
    /// its functions having effects of its own. Then settle the contracts of the group over
    /// copies of that inference, and emit its functions in the slots reserved for them.
    Settle {
        shapes: &'a [GroupContract],
        slots: &'a [LocalFunctionId],
        /// Whether a function of the group is public.
        exported: bool,
    },
}

impl GroupMode<'_> {
    /// Whether the types of the signatures are known before the bodies are inferred.
    fn has_fixed_types(&self) -> bool {
        matches!(self, Self::Settle { .. })
    }
}

/// The scheme through which the bodies of a group name one of its functions while they are
/// inferred jointly: its shape, with the effect it performs as one more row. Each reference
/// instantiates it, and so has the types of the group and rows of its own.
fn reference_scheme(shape: &GroupContract) -> TypeScheme<FnType> {
    let performed = shape
        .scheme
        .eff_quantifiers
        .iter()
        .map(|var| var.name() + 1)
        .max()
        .unwrap_or(0)
        .max(shape.written_count as u32);
    let performed = EffectVar::new(performed);
    let mut ty = shape.scheme.ty.clone();
    ty.effects = EffType::single_variable(performed);
    let mut eff_quantifiers = shape.scheme.eff_quantifiers.clone();
    eff_quantifiers.insert(performed);
    TypeScheme {
        ty_quantifiers: shape.scheme.ty_quantifiers.clone(),
        eff_quantifiers,
        ty,
        constraints: Vec::new(),
    }
}

/// The signature of a body of a group whose bodies are inferred jointly against their shapes:
/// the group's instance of the types of its shape, its written effect generics, and its other
/// rows to infer. `group_instance` is the instance of each type variable of the shapes met so
/// far, which this extends.
fn baseline_signature(
    shape: &GroupContract,
    group_instance: &mut FxHashMap<TypeVar, Type>,
    explicit_root_tys: &[Type],
    written_effects: &[EffectVar],
    span: Location,
    ty_inf: &mut TypeInference,
) -> FnType {
    for (root, var) in explicit_root_tys.iter().zip(&shape.written_types) {
        match group_instance.entry(*var) {
            Entry::Vacant(instance) => {
                instance.insert(*root);
            }
            Entry::Occupied(instance) => {
                ty_inf.add_same_type_constraint(*instance.get(), *root, span)
            }
        }
    }
    for var in &shape.scheme.ty_quantifiers {
        group_instance
            .entry(*var)
            .or_insert_with(|| ty_inf.fresh_type_var_ty());
    }
    ty_inf.add_declared_generics(
        shape
            .scheme
            .ty_quantifiers
            .iter()
            .map(|var| group_instance[var]),
    );
    assert_eq!(shape.written_count, written_effects.len());
    let mut eff_subst = written_effects
        .iter()
        .enumerate()
        .map(|(param, var)| (EffectVar::new(param as u32), EffType::single_variable(*var)))
        .collect::<EffectsInstSubst>();
    for var in shape.scheme.eff_quantifiers.iter().sorted() {
        eff_subst
            .entry(*var)
            .or_insert_with(|| ty_inf.fresh_effect_var_ty());
    }
    let ty_subst = shape
        .scheme
        .ty_quantifiers
        .iter()
        .map(|var| (*var, group_instance[var]))
        .collect::<TypeInstSubst>();
    let subst = (ty_subst, eff_subst);
    shape
        .scheme
        .ty
        .map(&mut BitmapInstantiationMapper::new(&subst))
}

/// A reference between two functions of a group: the index of the function whose body makes
/// it, the index of the function it names, the type that function has there, and the site.
type GroupReferenceIn = (usize, usize, FnType, Location);

/// The settling of the contracts of a group over one joint inference of its bodies.
///
/// A round starts from a copy of that inference, gives each reference an instance of the
/// contract of the function it names, and reads the next contract of every function. The
/// contracts of a round approximate those of the group unrolled once more. A round that gives
/// every contract again is the last: every body confirmed the contracts that it assumed, its
/// own included, which is the rule for typing recursive definitions.
///
/// The contracts of a round are provisional, and so are the requirements that follow from
/// them. Around a cycle of references, an instance of a requirement that no function makes
/// any more would give itself again at every round. The ranks tell it apart: it has no chain
/// from a requirement that a function makes, so its rank grows at every round, and no round
/// gives its contract again. As the instances along a chain are requirements that differ only
/// by effects, a rank is below the number of such requirements in the settled contracts, and
/// a requirement whose rank is not is given no instance. This cut guides the search and proves
/// nothing about the round it is made in; the settled round makes none. So each requirement
/// of the settled contracts is made by its function, or is the instance of one of a function
/// that it names, by a finite chain that starts at a requirement that a function makes. That
/// these contracts are the least or the most general ones is not claimed.
struct Settlement {
    /// The inference after the bodies and the passes that determine types.
    baseline: UnifiedTypeInference,
    /// The bodies as they are in the baseline.
    pending_functions: PendingModuleFunctions,
    /// The functions of the module that a round writes.
    written_functions: Vec<LocalFunctionId>,
    warning_count: usize,
    /// The signature of each function in the baseline.
    signatures: Vec<FnType>,
    /// The requirements of each function in the baseline: those that its types reach, but for
    /// those that only other functions make.
    own_requirements: Vec<Vec<PubTypeConstraint>>,
    /// The requirements of each function in the round in progress, as they are when the round
    /// starts: its own, and an instance of those of each function that it names.
    requirements: Vec<Vec<PubTypeConstraint>>,
    /// The rank of each of these requirements.
    requirement_ranks: Vec<Vec<usize>>,
    /// The contract of each function: the types and the requirements of the baseline, with the
    /// effects of a round. So a type that a round makes the same as another does not reach the
    /// next round.
    contracts: Vec<GroupContract>,
    references: Vec<GroupReferenceIn>,
    /// The number of rounds that ended.
    rounds_done: usize,
    /// The number of rounds that may change a contract.
    round_bound: usize,
    /// The module before the round in progress.
    checkpoint: Option<ModuleCheckpoint>,
    /// For each function, the error for which the round in progress leaves it out: it gets
    /// no instance of a contract, and what follows from the effects of the round is not drawn
    /// for it.
    left_out: Vec<Option<InternalCompilationError>>,
    /// For each function, its name, its written type generics and their types.
    written_types: Vec<(ast::UstrSpan, Vec<ast::UstrSpan>, Vec<Type>)>,
    /// For each reference, the effect that the round in progress gave to each effect variable
    /// of the contract of the function that it names.
    reference_effects: Vec<EffectsInstSubst>,
    /// The number of trait applications that the baseline answered other than by a given.
    answered_applications: usize,
    /// For each requirement of the contracts of the round in progress, effects left out, the
    /// number of requirements of these contracts that differ from it only by effects.
    alike: FxHashMap<PubTypeConstraint, usize>,
}

impl Settlement {
    /// Starts a round: the state goes back to the baseline, and each reference gets an
    /// instance of the contract of its function, whose requirements become requirements of
    /// the function that makes the reference.
    ///
    /// The contracts of a round are provisional: callees that still look pure can make two
    /// trait applications one that later rounds keep apart. So the instances are given function
    /// by function. A function whose instances cannot be given, or change a type of the group,
    /// is left out of the round, which then starts again: the group has one instance of its
    /// types, so the other functions would fail with it. Returns whether the round started.
    #[allow(clippy::too_many_arguments)]
    fn start_round(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        pending_functions: &mut PendingModuleFunctions,
        output: &mut Module,
        others: &Modules,
        warnings: &mut Vec<CompilationWarning>,
        functions: &[LocalFunctionId],
        solver_arena: &mut NodeArena,
    ) -> Result<bool, InternalCompilationError> {
        if let Some(checkpoint) = self.checkpoint.take() {
            output.restore(checkpoint);
            warnings.truncate(self.warning_count);
            *ty_inf = self.baseline.clone();
            *pending_functions = self.pending_functions.clone();
        }
        self.checkpoint = Some(output.checkpoint(&self.written_functions));
        self.requirements = self.own_requirements.clone();
        self.requirement_ranks = self
            .own_requirements
            .iter()
            .map(|requirements| vec![0; requirements.len()])
            .collect();
        self.reference_effects = vec![EffectsInstSubst::default(); self.references.len()];
        self.alike.clear();
        for contract in &self.contracts {
            for requirement in &contract.scheme.constraints {
                *self
                    .alike
                    .entry(requirement.map(&mut EffectErasingMapper))
                    .or_default() += 1;
            }
        }
        for (index, function) in functions.iter().enumerate() {
            if self.left_out[index].is_some() {
                continue;
            }
            let given = self
                .give_instances(
                    index,
                    *function,
                    ty_inf,
                    pending_functions,
                    output,
                    others,
                    solver_arena,
                )
                .and_then(|()| self.keeps_types(ty_inf));
            if let Err(error) = given {
                self.left_out[index] = Some(error);
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Gives each reference that the function at `index` makes an instance of the contract of
    /// the function that it names, and solves the requirements again.
    #[allow(clippy::too_many_arguments)]
    fn give_instances(
        &mut self,
        index: usize,
        function: LocalFunctionId,
        ty_inf: &mut UnifiedTypeInference,
        pending_functions: &mut PendingModuleFunctions,
        output: &mut Module,
        others: &Modules,
        solver_arena: &mut NodeArena,
    ) -> Result<(), InternalCompilationError> {
        for (reference, (owner, callee, fn_ty, span)) in self.references.iter().enumerate() {
            if *owner != index {
                continue;
            }
            let contract = &self.contracts[*callee];
            let ranks = &contract.ranks;
            let contract = &contract.scheme;
            // One substitution for the whole contract keeps what relates its rows.
            let subst = (
                TypeInstSubst::default(),
                contract
                    .eff_quantifiers
                    .iter()
                    .sorted()
                    .map(|var| (*var, EffType::single_variable(ty_inf.fresh_effect_var())))
                    .collect::<EffectsInstSubst>(),
            );
            self.reference_effects[reference] = subst.1.clone();
            let mut mapper = BitmapInstantiationMapper::new(&subst);
            let instance = contract.ty.map(&mut mapper);
            ty_inf.unify_same_type(
                Type::function_type(fn_ty.clone()),
                *span,
                Type::function_type(instance),
                *span,
            )?;
            let mut ty_inf = ty_inf.constraint_owner_scope(function);
            for (constraint, rank) in contract.constraints.iter().zip(ranks) {
                // No chain from a requirement that a function makes is this long.
                if *rank >= self.alike[&constraint.map(&mut EffectErasingMapper)] {
                    continue;
                }
                let requirement = constraint
                    .map(&mut mapper)
                    .instantiate_location_cloned(*span);
                self.requirements[index].push(requirement.clone());
                self.requirement_ranks[index].push(rank + 1);
                ty_inf.add_requirement(requirement);
            }
        }
        let mut solver = trait_solver_from_module!(output, others);
        ty_inf.solve_requirements(&mut solver, solver_arena)?;
        let generated = solver.finish().commit(
            &mut output.functions,
            &mut output.def_table,
            pending_functions,
        );
        elaborate_generated_functions(output, others, pending_functions, generated)?;
        // The evidence of the baseline is kept: a requirement that it left to the callers
        // stays theirs, whatever the effects of a round.
        if ty_inf.answered_applications() != self.answered_applications {
            let (name, ..) = &self.written_types[index];
            return Err(internal_compilation_error!(RecursiveGroupBodyDoesNotFit {
                function: name.0,
                span: name.1,
            }));
        }
        Ok(())
    }

    /// The effects that each reference of the settled group gives to the effect quantifiers of
    /// the function that it names, in their order, by the function that makes the reference
    /// and the site of the reference.
    ///
    /// `numbered` are the effect variables of each function in the order of the numbers of its
    /// contract, and `normalized` is what each effect variable is in the published scheme of
    /// each function. A reference is left out if its effects cannot be told, or if another
    /// reference of the same site has other effects. Nothing else tells its effects, so its
    /// elaboration then fails.
    fn recorded_reference_effects(
        &self,
        numbered: &[Vec<EffectVar>],
        normalized: &[EffectsInstSubst],
        quantifier_counts: &[usize],
        ty_inf: &mut UnifiedTypeInference,
    ) -> Vec<FxHashMap<Location, Vec<EffType>>> {
        let mut recorded = vec![FxHashMap::default(); numbered.len()];
        let mut ambiguous = FxHashSet::default();
        for ((owner, callee, _, span), given) in self.references.iter().zip(&self.reference_effects)
        {
            let effects = (0..quantifier_counts[*callee] as u32)
                .map(|quantifier| {
                    let quantifier = EffType::single_variable(EffectVar::new(quantifier));
                    let number = numbered[*callee]
                        .iter()
                        .position(|var| normalized[*callee].get(var) == Some(&quantifier))?;
                    let row = ty_inf
                        .substitute_in_effect_type(given.get(&EffectVar::new(number as u32))?);
                    // In the variables of the caller's scheme: an effect that it does not
                    // retain is none.
                    let mut effects = EffType::empty();
                    for effect in row.iter() {
                        match effect {
                            Effect::Variable(var) => {
                                if let Some(row) = normalized[*owner].get(&var) {
                                    effects = effects.union(row);
                                }
                            }
                            effect => effects.insert(effect),
                        }
                    }
                    Some(effects)
                })
                .collect::<Option<Vec<_>>>();
            let Some(effects) = effects else {
                continue;
            };
            if ambiguous.contains(&(*owner, *span)) {
                continue;
            }
            let previous = recorded[*owner].insert(*span, effects.clone());
            if previous.is_some_and(|previous| previous != effects) {
                recorded[*owner].remove(span);
                ambiguous.insert((*owner, *span));
            }
        }
        recorded
    }

    /// Checks that the round in progress kept the types of the baseline: a round can make two
    /// unknown types one, when effects make two trait applications one, and nothing more, as
    /// the types of the bodies were decided without it. So an unknown type is still unknown,
    /// and the written type generics of each function are still apart.
    fn keeps_types(
        &self,
        ty_inf: &mut UnifiedTypeInference,
    ) -> Result<(), InternalCompilationError> {
        for (((name, params, roots), signature), requirements) in self
            .written_types
            .iter()
            .zip(&self.signatures)
            .zip(&self.own_requirements)
        {
            let resolved_roots = roots
                .iter()
                .map(|root| ty_inf.substitute_in_type(*root))
                .collect::<Vec<_>>();
            distinct_written_type_vars(params, resolved_roots, || GenericParamsOwner::Function {
                name: name.0,
            })?;
            let unknown_types = signature
                .inner_ty_vars()
                .into_iter()
                .chain(requirements.iter().flat_map(|r| r.inner_ty_vars()));
            for var in unknown_types {
                let ty = ty_inf.substitute_in_type(Type::variable(var));
                if ty.data().as_variable().is_none() {
                    return Err(internal_compilation_error!(RecursiveGroupBodyDoesNotFit {
                        function: name.0,
                        span: name.1,
                    }));
                }
            }
        }
        Ok(())
    }

    /// Ends a round, from the effects that it found. If every function gave its contract again,
    /// returns the effect variables of each signature in the order that its contract numbers
    /// them. If not, the contracts are those of this round.
    ///
    /// `errors` has the error of each function for which the round failed, to which those of
    /// the functions that the round left out are added. Such a function keeps its contract: the
    /// effects of a round are provisional, so its error counts only once the contracts have
    /// settled, and is then the error of the group.
    fn end_round(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        written_effects: &[Vec<EffectVar>],
        first: &ast::DModuleFunction,
        mut errors: Vec<Option<InternalCompilationError>>,
    ) -> Result<Option<Vec<Vec<EffectVar>>>, InternalCompilationError> {
        for (error, left_out) in errors.iter_mut().zip(&mut self.left_out) {
            if let Some(left_out) = left_out.take() {
                *error = Some(left_out);
            }
        }
        let mut next = Vec::new();
        let mut numbered = Vec::new();
        for (index, error) in errors.iter().enumerate() {
            let (contract, effects) = round_contract(
                &self.signatures[index],
                &self.requirements[index],
                &self.requirement_ranks[index],
                &written_effects[index],
                ty_inf,
            );
            next.push(if error.is_some() {
                self.contracts[index].clone()
            } else {
                contract
            });
            numbered.push(effects);
        }
        if next
            .iter()
            .zip(&self.contracts)
            .all(|(next, contract)| next.is_same_as(contract))
        {
            return match errors.into_iter().flatten().next() {
                Some(error) => Err(error),
                None => Ok(Some(numbered)),
            };
        }
        self.rounds_done += 1;
        if self.rounds_done > self.round_bound {
            // The errors of this round are of contracts that did not settle.
            return Err(self.does_not_settle(&next, first, ty_inf));
        }
        self.contracts = next;
        Ok(None)
    }

    /// The error of a group whose contracts still changed in the last round that the bound
    /// allows, `next` being the contracts that this round read. It names a requirement that the
    /// round gave a function at more effects than it had, if there is one. This is what the
    /// last round did, not a proof that the contracts cannot settle: contracts can grow without
    /// end, an output of one requirement being an input of the next, and a later round can
    /// also make such effects one.
    fn does_not_settle(
        &self,
        next: &[GroupContract],
        first: &ast::DModuleFunction,
        ty_inf: &mut UnifiedTypeInference,
    ) -> InternalCompilationError {
        let without_effects = |contract: &GroupContract| {
            let requirements = contract.scheme.constraints.iter();
            requirements
                .map(|requirement| requirement.map(&mut EffectErasingMapper))
                .collect::<Vec<_>>()
        };
        let growing = next
            .iter()
            .zip(&self.contracts)
            .zip(&self.written_types)
            .find_map(|((next, contract), (_, params, roots))| {
                let (before, after) = (without_effects(contract), without_effects(next));
                let count =
                    |all: &[PubTypeConstraint], one| all.iter().filter(|r| *r == one).count();
                let position = after
                    .iter()
                    .position(|one| count(&after, one) > count(&before, one))?;
                // A contract has the types of the baseline, which the written generics name.
                let names = roots
                    .iter()
                    .zip(params)
                    .filter_map(|(root, param)| {
                        let root = ty_inf.substitute_in_type(*root);
                        Some((*root.data().as_variable()?, param.0))
                    })
                    .collect::<FxHashMap<_, _>>();
                Some((next.scheme.constraints[position].clone(), names))
            });
        let (growing, type_names) = growing.unzip();
        internal_compilation_error!(RecursiveGroupDoesNotSettle {
            function: first.name.0,
            rounds: self.rounds_done,
            growing,
            type_names: type_names.unwrap_or_default(),
            span: first.name.1,
        })
    }
}

/// The signature and the requirements of each function of a group in the baseline, the state
/// of the joint inference of its bodies once types are determined.
///
/// The requirements of a function are those that its types reach, but for those that only
/// other functions make. If the group is `exported`, they are given their public form here, as
/// this can determine types: the requirements that name something private are replaced, in the
/// inference too, by the public ones that give their evidence, and the bodies record how.
#[allow(clippy::too_many_arguments)]
fn baseline_requirements<'a>(
    output: &mut Module,
    others: &Modules,
    inputs: impl Iterator<Item = EmitFunctionInput<'a>>,
    functions: &[LocalFunctionId],
    written_roots: &[Vec<Type>],
    exported: bool,
    pending_functions: &mut PendingModuleFunctions,
    associated_lambdas: &FxHashMap<LocalFunctionId, Vec<LocalFunctionId>>,
    ty_inf: &mut UnifiedTypeInference,
    solver_arena: &mut NodeArena,
) -> Result<(Vec<FnType>, Vec<Vec<PubTypeConstraint>>), InternalCompilationError> {
    let signatures = |output: &Module, ty_inf: &mut UnifiedTypeInference| {
        functions
            .iter()
            .map(|id| {
                let ty = &output.functions[id.as_index()].definition.ty_scheme.ty;
                ty_inf.substitute_in_fn_type(ty)
            })
            .collect::<Vec<_>>()
    };
    ty_inf.normalize_remaining_constraints();
    let mut own_requirements = Vec::new();
    for ((id, signature), roots) in functions
        .iter()
        .zip(signatures(output, ty_inf))
        .zip(written_roots)
    {
        let mut seeds = signature.inner_ty_vars();
        for root in roots {
            seeds.extend(ty_inf.substitute_in_type(*root).inner_ty_vars());
        }
        own_requirements.push(
            ConstraintBoundary::from_seed_ty_vars(seeds)
                .accessible_constraints(ty_inf.remaining_constraints())
                .into_iter()
                .filter(|requirement| !ty_inf.is_requirement_of_others(requirement, *id))
                .cloned()
                .collect::<Vec<_>>(),
        );
    }
    if !exported {
        return Ok((signatures(output, ty_inf), own_requirements));
    }

    // The requirements that were replaced, and for each function those that replace them.
    let mut replaced = FxHashSet::default();
    let mut added = vec![Vec::new(); functions.len()];
    for ((((input, id), roots), requirements), added) in inputs
        .zip(functions)
        .zip(written_roots)
        .zip(&mut own_requirements)
        .zip(&mut added)
    {
        let signature = &output.functions[id.as_index()].definition.ty_scheme.ty;
        let rigid = ty_inf
            .substitute_in_fn_type(signature)
            .args
            .iter()
            .map(|arg| arg.ty)
            .chain(roots.iter().copied())
            .collect::<Vec<_>>();
        let Some(reduced) = public_requirements(
            requirements,
            &rigid,
            input.function,
            roots,
            *id,
            output,
            others,
            pending_functions,
            associated_lambdas,
            ty_inf,
            solver_arena,
        )?
        else {
            continue;
        };
        added.extend(
            reduced
                .iter()
                .filter(|requirement| !requirements.contains(requirement))
                .cloned(),
        );
        replaced.extend(
            requirements
                .drain(..)
                .filter(|requirement| !reduced.contains(requirement)),
        );
        *requirements = reduced;
    }
    if !replaced.is_empty() {
        // The inference holds the public form too, each new requirement being of its function.
        let kept = ty_inf
            .remaining_constraints()
            .iter()
            .filter(|requirement| !replaced.contains(*requirement))
            .cloned()
            .collect();
        ty_inf.replace_remaining_constraints(kept);
        for (id, added) in functions.iter().zip(added) {
            let mut ty_inf = ty_inf.constraint_owner_scope(*id);
            for requirement in added {
                let requirement = ty_inf.substitute_in_constraint(&requirement);
                ty_inf.add_requirement(requirement);
            }
        }
        ty_inf.normalize_remaining_constraints();
        for requirements in &mut own_requirements {
            for requirement in requirements.iter_mut() {
                *requirement = ty_inf.substitute_in_constraint(requirement);
            }
        }
    }
    Ok((signatures(output, ty_inf), own_requirements))
}

/// Gives the types and the requirements of the baseline the effects that a round found, and
/// nothing else of the round: the types stay as they are.
struct RoundEffects<'a>(&'a mut UnifiedTypeInference);

impl TypeMapper for RoundEffects<'_> {
    fn map_type(&mut self, ty: Type) -> Type {
        ty
    }

    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
        mut_ty
    }

    fn map_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        self.0.substitute_in_effect_type(eff_ty)
    }
}

/// The contract that a function has after a round: its signature and its requirements in the
/// baseline, with the effects that the round found, numbered, the written generics first.
///
/// Also returns the effect variables of the signature in the order of their numbers.
fn round_contract(
    signature: &FnType,
    requirements: &[PubTypeConstraint],
    requirement_ranks: &[usize],
    written_effects: &[EffectVar],
    ty_inf: &mut UnifiedTypeInference,
) -> (GroupContract, Vec<EffectVar>) {
    let mut effects = RoundEffects(ty_inf);
    let ty = signature.map(&mut effects);
    let requirements = requirements
        .iter()
        .map(|requirement| requirement.map(&mut effects))
        .collect::<Vec<_>>();
    let mut variables = ContractEffects {
        numbers: written_effects
            .iter()
            .enumerate()
            .map(|(param, var)| (*var, EffectVar::new(param as u32)))
            .collect(),
    };
    let ty = ty.map(&mut variables);
    let mut constraints = Vec::new();
    let mut ranks = Vec::new();
    for (requirement, rank) in requirements.iter().zip(requirement_ranks) {
        let constraint = requirement.map(&mut variables);
        match constraints.iter().position(|known| *known == constraint) {
            Some(known) => ranks[known] = min(ranks[known], *rank),
            None => {
                constraints.push(constraint);
                ranks.push(*rank);
            }
        }
    }
    let eff_quantifiers = TypeScheme::<FnType>::list_eff_vars(&ty, constraints.iter());
    let contract = GroupContract {
        scheme: TypeScheme {
            ty_quantifiers: Vec::new(),
            eff_quantifiers,
            ty,
            constraints,
        },
        written_count: written_effects.len(),
        written_types: Vec::new(),
        ranks,
    };
    let numbered = variables
        .numbers
        .into_iter()
        .sorted_by_key(|(_, number)| *number)
        .map(|(var, _)| var)
        .collect();
    (contract, numbered)
}

/// What joint inference of a group remembers about the declaration of one of its functions.
struct GroupFunctionDeclaration {
    /// The function's name.
    name: Ustr,
    type_params: Vec<ast::UstrSpan>,
    /// The parameter index of the variable standing for each written effect generic.
    written_vars: FxHashMap<EffectVar, usize>,
}

/// Whether a row of a signature is one the source wrote: it has no variables at all, or a
/// variable that a written generic stands for.
fn is_written_row(row: &EffType, written: &FxHashMap<EffectVar, usize>) -> bool {
    let vars = row.inner_vars();
    vars.is_empty() || vars.iter().any(|var| written.contains_key(var))
}

/// Calls `visit(row, written)` for every effect row of a signature, looking through the type
/// variables that pass 1 solved. Rows found through a solved variable were inferred.
struct RowWalker<'a, V: FnMut(&mut UnifiedTypeInference, &EffType, bool) -> EffType> {
    ty_inf: &'a mut UnifiedTypeInference,
    written_vars: &'a FxHashMap<EffectVar, usize>,
    in_solved: bool,
    visit: V,
}

impl<V: FnMut(&mut UnifiedTypeInference, &EffType, bool) -> EffType> TypeMapper
    for RowWalker<'_, V>
{
    fn map_type(&mut self, ty: Type) -> Type {
        if !ty.data().is_variable() {
            return ty;
        }
        let solved = self.ty_inf.substitute_in_type(ty);
        if solved == ty {
            return ty;
        }
        let was_in_solved = self.in_solved;
        self.in_solved = true;
        let mapped = solved.map(self);
        self.in_solved = was_in_solved;
        mapped
    }

    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
        let solved = self.ty_inf.substitute_in_mut_type(mut_ty);
        if solved.as_variable().is_some() {
            MutType::constant()
        } else {
            solved
        }
    }

    fn map_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        let written = !self.in_solved && is_written_row(eff_ty, self.written_vars);
        (self.visit)(self.ty_inf, eff_ty, written)
    }
}

fn walk_signature<V: FnMut(&mut UnifiedTypeInference, &EffType, bool) -> EffType>(
    fn_ty: &FnType,
    ty_inf: &mut UnifiedTypeInference,
    written_vars: &FxHashMap<EffectVar, usize>,
    visit: V,
) -> FnType {
    fn_ty.map(&mut RowWalker {
        ty_inf,
        written_vars,
        in_solved: false,
        visit,
    })
}

/// A written row of a signature, in the variables of its contract.
fn written_row(declaration: &GroupFunctionDeclaration, row: &EffType) -> EffType {
    let subst = declaration
        .written_vars
        .iter()
        .map(|(var, param)| {
            (
                *var,
                EffType::single_variable(EffectVar::new(*param as u32)),
            )
        })
        .collect();
    row.instantiate(&subst)
}

/// The shape of a function of a group: the types of its signature as the joint inference found
/// them, with the written rows as written, and every other row a variable of its own, which
/// marks the place of an effect to infer. The effect it performs and its requirements are left
/// out: each body finds them when it is inferred alone.
fn shape_scheme(
    fn_ty: &FnType,
    written_types: &[TypeVar],
    declaration: &GroupFunctionDeclaration,
    ty_inf: &mut UnifiedTypeInference,
) -> TypeScheme<FnType> {
    let written = &declaration.written_vars;
    let next = Cell::new(declaration.written_vars.len() as u32);
    let signature_row = |row: &EffType, is_written: bool| {
        if is_written {
            written_row(declaration, row)
        } else {
            next.set(next.get() + 1);
            EffType::single_variable(EffectVar::new(next.get() - 1))
        }
    };
    let args = fn_ty
        .args
        .iter()
        .map(|arg| {
            walk_signature(
                &FnType::new(vec![*arg], Type::unit(), EffType::empty()),
                ty_inf,
                written,
                |_, row, is_written| signature_row(row, is_written),
            )
            .args[0]
        })
        .collect::<Vec<_>>();
    let ret = walk_signature(
        &FnType::new(vec![], fn_ty.ret, EffType::empty()),
        ty_inf,
        written,
        |_, row, is_written| signature_row(row, is_written),
    )
    .ret;
    let ty = FnType::new(args, ret, EffType::empty());
    let no_constraints: [PubTypeConstraint; 0] = [];
    let ty_quantifiers = written_types
        .iter()
        .copied()
        .chain(TypeScheme::list_ty_vars(&ty, no_constraints.iter()))
        .unique()
        .collect();
    TypeScheme {
        ty_quantifiers,
        eff_quantifiers: ty.inner_effect_vars(),
        ty,
        constraints: Vec::new(),
    }
}

/// Numbers the effect variables of a contract: the written generics first, then the others as
/// they are met.
struct ContractEffects {
    /// The contract's effect variable for each one met so far, so that the next one is
    /// numbered by the size of the map.
    numbers: FxHashMap<EffectVar, EffectVar>,
}

impl TypeMapper for ContractEffects {
    fn map_type(&mut self, ty: Type) -> Type {
        ty
    }

    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
        mut_ty
    }

    fn map_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        let mut result = EffType::empty();
        for effect in eff_ty.iter() {
            let Effect::Variable(var) = effect else {
                result.insert(effect);
                continue;
            };
            let next = EffectVar::new(self.numbers.len() as u32);
            let number = *self.numbers.entry(var).or_insert(next);
            result.insert(Effect::Variable(number));
        }
        result
    }
}

/// The variables of written type generics, given the types their roots resolved to: a written
/// generic stands for every type, so it must have stayed a variable of its own.
fn distinct_written_type_vars(
    params: &[ast::UstrSpan],
    resolved_roots: impl IntoIterator<Item = Type>,
    owner: impl Fn() -> GenericParamsOwner,
) -> Result<Vec<TypeVar>, InternalCompilationError> {
    let mut vars = Vec::new();
    for (resolved, (name, span)) in resolved_roots.into_iter().zip(params) {
        match resolved.data().as_variable() {
            Some(var) if !vars.contains(var) => vars.push(*var),
            _ => {
                return Err(internal_compilation_error!(InvalidGenericParams {
                    owner: owner(),
                    kind: InvalidGenericParamsKind::RestrictedTypeParameter { name: *name },
                    span: *span,
                }));
            }
        }
    }
    Ok(vars)
}

/// The shapes of the functions of a group, from the types that its joint inference found.
fn group_shapes(
    fn_tys: &[FnType],
    declarations: &[GroupFunctionDeclaration],
    written_type_roots: &[Vec<Type>],
    ty_inf: &mut UnifiedTypeInference,
) -> Result<Vec<GroupContract>, InternalCompilationError> {
    let mut shapes = Vec::new();
    for ((fn_ty, declaration), roots) in fn_tys.iter().zip(declarations).zip(written_type_roots) {
        let resolved_roots = roots
            .iter()
            .map(|root| ty_inf.substitute_in_type(*root))
            .collect::<Vec<_>>();
        let written_types =
            distinct_written_type_vars(&declaration.type_params, resolved_roots, || {
                GenericParamsOwner::Function {
                    name: declaration.name,
                }
            })?;
        let scheme = shape_scheme(fn_ty, &written_types, declaration, ty_inf);
        shapes.push(GroupContract {
            scheme,
            written_count: declaration.written_vars.len(),
            written_types,
            ranks: Vec::new(),
        });
    }
    Ok(shapes)
}

/// The exit of discovery: the shapes of the functions of a group, from their joint inference.
#[allow(clippy::too_many_arguments)]
fn discovered_shapes<'func>(
    output: &Module,
    ty_inf: &mut UnifiedTypeInference,
    ast_functions: impl Iterator<Item = EmitFunctionInput<'func>>,
    local_fns: &[LocalFunctionId],
    function_explicit_root_tys: &[Vec<Type>],
    recursive_function_ids: &FxHashSet<FunctionId>,
    pending_functions: &PendingModuleFunctions,
    group_declarations: &[GroupFunctionDeclaration],
) -> Result<Vec<GroupContract>, InternalCompilationError> {
    // A return that only diverges becomes `never` here, where the whole group is seen: a body
    // inferred alone must keep the types of its shape.
    for (id, ret_var) in unconstrained_diverging_returns(
        output,
        ty_inf,
        ast_functions,
        local_fns,
        function_explicit_root_tys,
        recursive_function_ids,
        pending_functions,
    ) {
        let span = output.functions[id.as_index()]
            .spans
            .as_ref()
            .map_or(Location::new_synthesized(), |spans| spans.span);
        ty_inf.unify_same_type(Type::variable(ret_var), span, Type::never(), span)?;
    }
    let fn_tys = local_fns
        .iter()
        .map(|id| {
            output.functions[id.as_index()]
                .definition
                .ty_scheme
                .ty
                .clone()
        })
        .collect::<Vec<_>>();
    group_shapes(
        &fn_tys,
        group_declarations,
        function_explicit_root_tys,
        ty_inf,
    )
}

/// Checks the inferred body of a default method against the signature that its trait declares
/// for it, and returns the requirements of its scheme: the declared ones, after those that the
/// body needs besides.
fn fit_declared_signature(
    declared: &TypeScheme<FnType>,
    mut constraints: Vec<PubTypeConstraint>,
    input: EmitFunctionInput<'_>,
    output: &Module,
    others: &Modules,
    ty_inf: &mut UnifiedTypeInference,
) -> Result<Vec<PubTypeConstraint>, InternalCompilationError> {
    let function = input.function;
    let checked_constraints = constraints.iter().filter(|constraint| {
        !is_compiler_provided_value_constraint(constraint, ModuleEnv::new(output, others))
    });
    let checked = check_declared_signature(declared, checked_constraints, ty_inf);
    if let Err((reason, missing)) = checked {
        let (trait_id, index) = input
            .trait_default
            .expect("only a default method has a declared signature");
        let trait_def = output.trait_def(trait_id);
        let missing_constraint = missing.and_then(|constraint| {
            let env = ModuleEnv::new(output, others);
            let scheme = trait_def
                .default_method_scheme(trait_id, index, env, function.span)
                .ok()?;
            missing_requirement(&constraint, trait_def, &scheme, declared, ty_inf, &env)
        });
        return Err(internal_compilation_error!(InvalidTraitDefinition {
            trait_name: trait_def.name,
            kind: InvalidTraitDefinitionKind::InvalidDefaultMethod {
                method_name: trait_def.method(index).0,
                reason,
                missing_constraint,
            },
            span: function.span,
        }));
    }
    constraints.extend(
        declared
            .constraints
            .iter()
            .map(|constraint| ty_inf.substitute_in_constraint(constraint)),
    );
    Ok(constraints.into_iter().unique().collect())
}

/// Whether a recursive group gets contracts: it holds functions alone, neither a default method
/// of a trait, whose signature is declared, nor a member of a subscript.
fn group_gets_contracts<'a, I: Iterator<Item = EmitFunctionInput<'a>>>(mut inputs: I) -> bool {
    inputs.all(|input| input.trait_default.is_none() && input.subscript.is_none())
}

/// The public form of the requirements `constraints` of function `id`: those that name
/// something private are replaced by the public ones that give their evidence, and the body
/// records how. `None` if all are public already. `rigid` are the types that the requirements
/// must not determine, and `written_roots` the written type generics of the function.
#[allow(clippy::too_many_arguments)]
fn public_requirements(
    constraints: &[PubTypeConstraint],
    rigid: &[Type],
    function: &ast::DModuleFunction,
    written_roots: &[Type],
    id: LocalFunctionId,
    output: &mut Module,
    others: &Modules,
    pending_functions: &mut PendingModuleFunctions,
    associated_lambdas: &FxHashMap<LocalFunctionId, Vec<LocalFunctionId>>,
    ty_inf: &mut UnifiedTypeInference,
    solver_arena: &mut NodeArena,
) -> Result<Option<Vec<PubTypeConstraint>>, InternalCompilationError> {
    let mut solver = trait_solver_from_module!(output, others);
    if constraints.iter().all(|c| solver.requirement_is_public(c)) {
        return Ok(None);
    }
    let reduced = solver
        .reduce_public_requirements(constraints.to_vec(), rigid, ty_inf, solver_arena)
        .map_err(|error| {
            error.with_private_requirement_names(
                function
                    .generic_params
                    .type_params()
                    .iter()
                    .zip(written_roots)
                    .filter_map(|(name, root)| {
                        let root = ty_inf.substitute_in_type(*root);
                        Some((*root.data().as_variable()?, name.0))
                    }),
            )
        })?;
    let generated = solver.finish().commit(
        &mut output.functions,
        &mut output.def_table,
        pending_functions,
    );
    elaborate_generated_functions(output, others, pending_functions, generated)?;
    for function_id in function_and_associated_lambdas(&id, associated_lambdas) {
        pending_functions
            .get_mut(&function_id)
            .expect("pending function body")
            .evidence_plan = reduced.evidence.clone();
    }
    Ok(Some(reduced.requirements))
}

/// Whether a group publishes requirements: one of its functions is public.
fn group_is_exported<'a, I: Iterator<Item = EmitFunctionInput<'a>>>(mut inputs: I) -> bool {
    inputs.any(|input| input.function.visibility.is_public() && input.trait_default.is_none())
}

/// Emit the functions of one group of the module's call graph.
#[allow(clippy::too_many_arguments)]
pub(super) fn emit_function_group<'a, F, I>(
    output: &mut Module,
    solver_arena: &mut NodeArena,
    ast_functions: F,
    desugared_arena: &DExprArena,
    others: &Modules,
    recursive_function_names: &FxHashSet<Ustr>,
    capabilities: CompilationCapabilities,
    warnings: &mut Vec<CompilationWarning>,
) -> Result<(), InternalCompilationError>
where
    I: Iterator<Item = EmitFunctionInput<'a>>,
    F: Fn() -> I,
{
    if recursive_function_names.is_empty() || !group_gets_contracts(ast_functions()) {
        emit_functions(
            output,
            solver_arena,
            &ast_functions,
            desugared_arena,
            others,
            None,
            recursive_function_names,
            capabilities,
            warnings,
            GroupMode::Normal,
        )?;
        return Ok(());
    }
    let checkpoint = output.checkpoint(&[]);
    let warning_count = warnings.len();
    let discovered = emit_functions(
        output,
        solver_arena,
        &ast_functions,
        desugared_arena,
        others,
        None,
        recursive_function_names,
        capabilities,
        warnings,
        GroupMode::Discover,
    );
    // Also when discovery fails: it leaves the module deciding traits by structure.
    output.restore(checkpoint);
    warnings.truncate(warning_count);
    let Emitted::Shapes(shapes) = discovered? else {
        unreachable!("discovery produces shapes");
    };

    // Each function has its slot before the bodies are inferred against the shapes.
    let mut ids = Vec::new();
    let bottoms = shapes.iter().map(GroupContract::bottom).collect::<Vec<_>>();
    for (input, contract) in ast_functions().zip(&bottoms) {
        let function = input.function;
        let definition = CallableDefinition::new_with_generic_params_and_attributes(
            contract.scheme.clone(),
            function.generic_params.type_params().to_vec(),
            function.generic_params.effect_params().to_vec(),
            function.args.iter().map(|arg| arg.name.0).collect(),
            function.doc.clone(),
            function.attributes.clone(),
        )
        .with_result_convention(input.kind.return_convention());
        let descr = ModuleFunction::placeholder(definition, Some(function_spans(function)));
        ids.push(output.add_function_with_visibility(function.name.0, descr, function.visibility));
    }
    // A group behaves as its unrolling: its bodies are inferred once against these shapes, and
    // its contracts settle from those of functions that call nothing, until none changes.
    emit_functions(
        output,
        solver_arena,
        &ast_functions,
        desugared_arena,
        others,
        None,
        recursive_function_names,
        capabilities,
        warnings,
        GroupMode::Settle {
            shapes: &shapes,
            slots: &ids,
            exported: group_is_exported(ast_functions()),
        },
    )?;
    Ok(())
}

/// A bound on the rounds that the contracts of a group take to settle.
///
/// A round that is not the last changes a contract. A row of a contract, which is the effect
/// at one place of its types, or the effect that the function performs, changes in few ways:
/// it gains one of the primitive effects, its variable is merged with that of another row, or
/// it is bounded by a restriction. Besides, a requirement comes with a row of the types or with
/// a type variable. So the bound is the number of rows of the shapes, times these ways, plus
/// their type variables, and one more round that finds nothing to change. It is a limit of
/// work, not a proof that contracts settle within it.
///
/// A group whose contracts do not settle within the bound is refused. Its requirements can keep
/// growing, when an output of a requirement is an input of the one that the next round adds.
fn max_refinement_rounds(shapes: &[GroupContract]) -> usize {
    const PRIMITIVE_EFFECTS: usize = 3;
    const WAYS_TO_WEAKEN_A_ROW: usize = PRIMITIVE_EFFECTS + 2;
    let changes = shapes
        .iter()
        .map(|shape| {
            // A shape has a variable for each row of its types.
            let rows = shape.scheme.eff_quantifiers.len() + 1;
            rows * WAYS_TO_WEAKEN_A_ROW + shape.scheme.ty_quantifiers.len()
        })
        .sum::<usize>();
    1 + changes
}

fn function_spans(function: &ast::DModuleFunction) -> ModuleFunctionSpans {
    ModuleFunctionSpans {
        name: function.name.1,
        args: function
            .args
            .iter()
            .map(DModuleFunctionArg::locations_and_ty_concreteness)
            .collect(),
        args_span: function.args_span,
        ret_ty: function
            .ret_ty
            .map(|ret_ty| (ret_ty.1, ret_ty.0.is_constant())),
        span: function.span,
    }
}

/// Emit the methods of a trait implementation.
#[allow(clippy::too_many_arguments)]
pub(super) fn emit_impl_methods<'a, F, I>(
    output: &mut Module,
    solver_arena: &mut NodeArena,
    ast_functions: F,
    desugared_arena: &DExprArena,
    others: &Modules,
    trait_ctx: EmitTraitCtx,
    recursive_function_names: &FxHashSet<Ustr>,
    capabilities: CompilationCapabilities,
    warnings: &mut Vec<CompilationWarning>,
) -> Result<EmitTraitOutput, InternalCompilationError>
where
    I: Iterator<Item = EmitFunctionInput<'a>>,
    F: Fn() -> I,
{
    let result = emit_functions(
        output,
        solver_arena,
        &ast_functions,
        desugared_arena,
        others,
        Some(trait_ctx),
        recursive_function_names,
        capabilities,
        warnings,
        GroupMode::Normal,
    )?;
    match result {
        Emitted::TraitImpl(output) => Ok(*output),
        _ => unreachable!("emitting a trait implementation produces its output"),
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_functions<'a, F, I>(
    output: &mut Module,
    solver_arena: &mut NodeArena,
    ast_functions: &F,
    desugared_arena: &DExprArena,
    others: &Modules,
    trait_ctx: Option<EmitTraitCtx>,
    recursive_function_names: &FxHashSet<Ustr>,
    capabilities: CompilationCapabilities,
    warnings: &mut Vec<CompilationWarning>,
    mode: GroupMode<'_>,
) -> Result<Emitted, InternalCompilationError>
where
    I: Iterator<Item = EmitFunctionInput<'a>>,
    F: Fn() -> I,
{
    // First pass, populate the function table and allocate fresh mono type variables.
    let mut ty_inf = TypeInference::default();
    if matches!(mode, GroupMode::Discover) {
        // The shapes are types, which effects do not decide: an effect that does not fit is
        // found when the bodies are inferred alone. The caller undoes this with the rest of
        // what this pass does to the module.
        ty_inf.ignore_effects();
        output.impls.ignores_effects = true;
    }
    let mut group_declarations = Vec::new();
    let mut body_tys: Vec<FnType> = Vec::new();
    // When the bodies of a group are inferred jointly against their shapes: the group's
    // instance of the type variables of the shapes, the scheme through which each function is
    // named, and the references that each body makes, as a range of those of the inference.
    let mut group_instance: FxHashMap<TypeVar, Type> = FxHashMap::default();
    let mut reference_schemes: Vec<TypeScheme<FnType>> = Vec::new();
    let mut body_references = Vec::new();
    if matches!(mode, GroupMode::Settle { .. }) {
        ty_inf.track_requirement_owners();
        ty_inf.set_applications_per_function();
    }
    let mut impl_annotation_subst = None;
    let mut outer_annotation_var_count = 0;
    let mut outer_annotation_eff_var_count = 0;
    let mut explicit_trait_impl = None;
    let module_env = ModuleEnv::new(output, others);

    // If we are emitting a trait implementation, create generics for the trait input and output types
    // and add the constraints from the trait definition to the type inference.
    let mut self_given = None;
    let trait_output = if let Some(trait_ctx) = &trait_ctx {
        let trait_def = &trait_ctx.trait_def;
        let input_tys = ty_inf.fresh_type_var_tys(trait_def.input_type_count() as usize);
        let output_tys = ty_inf.fresh_type_var_tys(trait_def.output_type_count() as usize);
        let output_effs = (0..trait_def.output_effect_count())
            .map(|_| ty_inf.fresh_effect_var_ty())
            .collect::<Vec<_>>();
        let explicit_quantifiers = if !trait_ctx.generic_type_params.is_empty() {
            (0..trait_ctx.generic_type_params.len())
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
        let explicit_eff_quantifiers = &trait_ctx.generic_effect_param_names;
        outer_annotation_eff_var_count = explicit_eff_quantifiers.len();
        if !explicit_quantifiers.is_empty() || !explicit_eff_quantifiers.is_empty() {
            let eff_subst = explicit_eff_quantifiers
                .iter()
                .enumerate()
                .map(|(index, name)| {
                    (
                        EffectVar::new(index as u32),
                        ty_inf.fresh_rigid_effect_var_ty(Some(*name)),
                    )
                })
                .collect();
            let ty_subst = ty_inf.fresh_type_var_subst(&explicit_quantifiers);
            // Variables of a header without generic parameters are holes to infer.
            if !trait_ctx.generic_type_params.is_empty() {
                ty_inf.add_declared_generics(ty_subst.values().copied());
            }
            impl_annotation_subst = Some((ty_subst, eff_subst));
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
        let mut trait_subst = trait_def.param_subst_for(&input_tys, &output_tys, &output_effs);
        for constraint in trait_def
            .parent_constraints
            .iter()
            .chain(&trait_def.constraints)
        {
            for var in constraint.inner_ty_vars() {
                trait_subst
                    .0
                    .entry(var)
                    .or_insert_with(|| ty_inf.fresh_type_var_ty());
            }
            for var in constraint.inner_effect_vars().into_iter().sorted() {
                trait_subst
                    .1
                    .entry(var)
                    .or_insert_with(|| ty_inf.fresh_effect_var_ty());
            }
        }
        for constraint in trait_def
            .parent_constraints
            .iter()
            .chain(&trait_def.constraints)
        {
            ty_inf.add_pub_constraint(
                constraint
                    .instantiate_simple(&trait_subst)
                    .instantiate_location_cloned(trait_ctx.span),
            );
        }
        let subst = with_unwritten_requirement_effects(
            impl_annotation_subst
                .as_ref()
                .map_or_else(Default::default, Cow::Borrowed),
            trait_ctx.impl_constraints,
            &mut ty_inf,
        );
        let mut mapper = BitmapInstantiationMapper::new(&subst);
        for constraint in trait_ctx.impl_constraints {
            ty_inf.add_pub_constraint(constraint.map(&mut mapper));
        }
        self_given = Some(
            ty_inf.add_given_constraint(PubTypeConstraint::new_have_trait(
                trait_ctx.trait_id,
                input_tys.clone(),
                output_tys.clone(),
                output_effs.clone(),
                trait_ctx.span,
            )),
        );
        Some(EmitTraitOutput {
            evidence_plan: Default::default(),
            input_tys,
            output_tys,
            output_effs,
            ty_var_count: 0,
            eff_var_count: 0,
            constraints: vec![],
            functions: vec![],
            method_requirements: vec![],
            generic_names: ImplGenericNames::default(),
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
    let mut declared_signatures = Vec::new();
    let mut function_explicit_root_tys = Vec::new();
    // The variable of each written effect generic of each function.
    let mut function_written_effects: Vec<Vec<EffectVar>> = Vec::new();
    let mut function_attrs = Vec::new();
    let mut function_kinds = Vec::new();
    let mut subscript_signatures: FxHashMap<LocalSubscriptId, SharedSubscriptSignature> =
        FxHashMap::default();
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
        let cached_subscript_signature = match kind {
            EmitFunctionKind::SubscriptMember { subscript_id, .. } => {
                subscript_signatures.get(&subscript_id)
            }
            _ => None,
        };
        let mut annotation_subst = cached_subscript_signature
            .map(|shared| shared.annotation_subst.clone())
            .unwrap_or_else(|| impl_annotation_subst.clone().unwrap_or_default());
        let mut explicit_root_tys = if let Some(shared) = cached_subscript_signature {
            shared.explicit_root_tys.clone()
        } else {
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
            let mut written_vars = FxHashMap::default();
            for (index, (name, _)) in generic_params.effect_params().iter().enumerate() {
                let source_var = EffectVar::new((outer_annotation_eff_var_count + index) as u32);
                let eff = ty_inf.fresh_rigid_effect_var_ty(Some(*name));
                written_vars.insert(eff.to_single_variable().unwrap(), index);
                annotation_subst.1.insert(source_var, eff);
            }
            group_declarations.push(GroupFunctionDeclaration {
                name: name.0,
                type_params: generic_params.type_params().to_vec(),
                written_vars,
            });
            explicit_root_tys
        };
        let mut args_ty = args
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
        let mut ret_ty_ty = if let Some((ret_ty, _)) = ret_ty {
            ret_ty.map(&mut AnnotationTypeMapper::new(
                &mut ty_inf,
                Some(&annotation_subst),
            ))
        } else {
            ty_inf.fresh_type_var_ty()
        };
        if let EmitFunctionKind::SubscriptMember {
            subscript_id,
            projection_key,
            requires_mutable_yield,
            ..
        } = kind
        {
            let subscript = input
                .subscript
                .expect("subscript member emission should carry its source bundle");
            let shared_signature = subscript_signatures.entry(subscript_id).or_insert_with(|| {
                let signature =
                    subscript_signature_from_source(&mut ty_inf, subscript, &annotation_subst);
                SharedSubscriptSignature {
                    signature,
                    annotation_subst: annotation_subst.clone(),
                    explicit_root_tys: explicit_root_tys.clone(),
                }
            });
            annotation_subst = shared_signature.annotation_subst.clone();
            explicit_root_tys = shared_signature.explicit_root_tys.clone();
            let signature = shared_signature.signature.clone();
            output.subscripts[subscript_id.as_index()].set_resolved_signature(signature.clone());
            let member_kind = if requires_mutable_yield {
                SubscriptMemberKind::Mut
            } else {
                SubscriptMemberKind::Ref
            };
            args_ty = signature.member_args(projection_key.is_some(), member_kind);
            ret_ty_ty = signature.ret;
        }
        let subst = with_unwritten_requirement_effects(
            Cow::Borrowed(&annotation_subst),
            where_clause,
            &mut ty_inf,
        );
        let mut mapper = BitmapInstantiationMapper::new(&subst);
        let declared_requirements = ty_inf.constraint_scope_start();
        for constraint in where_clause {
            ty_inf.add_pub_constraint(constraint.map(&mut mapper));
        }
        if let GroupMode::Settle { slots, .. } = &mode {
            // A declared requirement is of its function, as those that its body makes.
            ty_inf.own_constraints_since(declared_requirements, slots[local_fns.len()]);
        }
        let attrs = validate_function_attributes(
            attributes,
            name.0,
            capabilities.allows_unsafe(output.module_id()),
        )?;
        let effects = ty_inf.fresh_effect_var_ty();
        let return_convention = kind.return_convention();
        let mut fn_type = FnType::new(args_ty, ret_ty_ty, effects.clone());
        // Read from the substitution, as the accessors of a subscript share the one of the first.
        let written_effects: Vec<EffectVar> = (0..generic_params.effect_params().len())
            .map(|index| {
                let source_var = EffectVar::new((outer_annotation_eff_var_count + index) as u32);
                annotation_subst.1[&source_var]
                    .to_single_variable()
                    .expect("a written effect generic maps to a variable")
            })
            .collect();
        if let GroupMode::Settle { shapes, .. } = &mode {
            // The shape gives the types, and the places of the effects to infer.
            let shape = &shapes[local_fns.len()];
            let signature = baseline_signature(
                shape,
                &mut group_instance,
                &explicit_root_tys,
                &written_effects,
                *span,
                &mut ty_inf,
            );
            fn_type = FnType::new(signature.args, signature.ret, effects.clone());
            body_tys.push(fn_type.clone());
            reference_schemes.push(reference_scheme(shape));
        }

        let declared_signature = input
            .trait_default
            .map(|(trait_id, index)| {
                let env = ModuleEnv::new(output, others);
                let scheme = env
                    .trait_def(trait_id)
                    .default_method_scheme(trait_id, index, env, *span)?;
                // The contract also quantifies unnamed variables introduced by parent/where
                // constraints. They must be fresh in this inference batch, just like named ones.
                let mut subst = annotation_subst.clone();
                for var in &scheme.ty_quantifiers {
                    subst
                        .0
                        .entry(*var)
                        .or_insert_with(|| ty_inf.fresh_type_var_ty());
                }
                for var in scheme.eff_quantifiers.iter().sorted() {
                    subst
                        .1
                        .entry(*var)
                        .or_insert_with(|| ty_inf.fresh_rigid_effect_var_ty(None));
                }
                ty_inf.add_declared_generics(scheme.ty_quantifiers.iter().map(|var| subst.0[var]));
                Ok::<_, InternalCompilationError>(scheme.instantiate_simple(&subst))
            })
            .transpose()?;
        if let Some(declared) = &declared_signature {
            ty_inf.add_fn_subtype_constraint_without_effects(&fn_type, *span, &declared.ty, *span);
            for constraint in &declared.constraints {
                ty_inf.add_given_constraint(constraint.clone());
            }
        }
        declared_signatures.push(declared_signature);

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
            ty_inf.add_fn_subtype_constraint_without_effects(
                &fn_type,
                *span,
                &instantiated_method_def.ty_scheme.ty,
                *span,
            );
        }

        // Create dummy code.
        let arg_names: Vec<_> = args.iter().map(|arg| arg.name.0).collect();

        let spans = function_spans(input.function);
        // Other bodies see the contract, and instantiate it at each call.
        let ty_scheme = if let Some(scheme) = reference_schemes.last() {
            scheme.clone()
        } else {
            TypeScheme::new_just_type(fn_type)
        };
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
        let id = if let GroupMode::Settle { slots, .. } = &mode {
            let id = slots[local_fns.len()];
            output.functions[id.as_index()] = descr;
            id
        } else if let Some(placeholder_ids) = trait_ctx
            .as_ref()
            .and_then(|tc| tc.stub_data.as_ref().map(|tys| &tys.method_ids))
        {
            // Reuse the pre-allocated stub slot so existing StaticApply nodes remain valid.
            let placeholder_id = placeholder_ids[local_fns.len()];
            output.functions[placeholder_id.as_index()] = descr;
            placeholder_id
        } else if trait_ctx.is_some() || kind.force_anonymous() || input.trait_default.is_some() {
            output.add_function_anonymous(descr)
        } else {
            output.add_function_with_visibility(name.0, descr, *visibility)
        };
        if let Some((trait_id, index)) = input.trait_default {
            output.traits[trait_id.index.as_index()].default_methods[index.as_index()] =
                Some(TraitDefaultMethod {
                    function: FunctionId::new(output.module_id(), id),
                });
            output.name_function_with_visibility(id, name.0, *visibility);
        }
        local_fns.push(id);
        function_annotation_substs.push(annotation_subst);
        ty_inf.add_declared_generics(explicit_root_tys.iter().copied());
        function_explicit_root_tys.push(explicit_root_tys);
        function_written_effects.push(written_effects);
        function_attrs.push(attrs);
        function_kinds.push(kind);
        subscript_attachments.push(input.subscript_attachments.to_vec());
    }

    if let GroupMode::Settle { shapes, .. } = &mode {
        // Every reference to a function of the group has the group's instance of its types.
        let instances = local_fns
            .iter()
            .zip(shapes.iter())
            .map(|(id, shape)| {
                let tys = shape
                    .scheme
                    .ty_quantifiers
                    .iter()
                    .map(|var| group_instance[var])
                    .collect();
                (FunctionId::new(output.module_id(), *id), tys)
            })
            .collect();
        ty_inf.set_group_type_instances(instances);
    }

    for (attachment, id) in subscript_attachments.iter().zip(local_fns.iter()) {
        for attachment in attachment {
            attach_subscript_member(
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
    for (function_index, ((((input, id), annotation_subst), attrs), kind)) in ast_functions()
        .zip(local_fns.iter())
        .zip(function_annotation_substs.iter())
        .zip(function_attrs.iter())
        .zip(function_kinds.iter().copied())
        .enumerate()
    {
        let constraint_scope = ty_inf.constraint_scope_start();
        let first_reference = ty_inf.group_references().len();
        let function = input.function;
        let body_descr = body_tys.get(function_index).map(|ty| {
            let mut descr = output.get_function_by_id(*id).unwrap().clone();
            descr.definition.ty_scheme = TypeScheme::new_just_type(ty.clone());
            descr
        });
        let descr = body_descr
            .as_ref()
            .unwrap_or_else(|| output.get_function_by_id(*id).unwrap());
        let module_env = ModuleEnv::new(output, others).with_capabilities(capabilities);
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
            warnings,
        );
        ty_env.function_name = Some(function.name.0);
        if let EmitFunctionKind::SubscriptMember {
            subscript_name,
            projection_key,
            ..
        } = kind
        {
            ty_env.subscript_member = Some(SubscriptMemberTypingContext {
                name: subscript_name,
                requires_mutable_place: kind.requires_mutable_place(),
                projection_key,
            });
        }
        ty_env.compilation_capabilities = capabilities;
        if descr.definition.result_convention.requires_yield_driver() {
            ty_env.yield_context = Some(YieldTypingContext::new(
                expected_ret_ty,
                expected_span,
                kind.requires_mutable_yield(),
            ));
        }
        let fn_node_id = if let Some(default_id) = input.forward_default {
            let default = &module_env
                .module_by_id(default_id.module)
                .unwrap()
                .functions[default_id.function.as_index()]
            .definition;
            let (ty, inst_data, _) = default.ty_scheme.instantiate_with_fresh_vars(
                &mut ty_inf,
                function.span,
                None,
                module_env,
            );
            // The forwarder calls the default, so the default must be usable as the forwarder.
            ty_inf.add_fn_subtype_constraint_without_effects(
                &ty,
                function.span,
                &descr.definition.ty_scheme.ty,
                function.span,
            );
            let arguments: Vec<_> = ty
                .args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    ty_env.ir_arena.alloc(hir::Node::new(
                        hir_syn::load_local(LocalDeclId::from_index(index)),
                        arg.ty,
                        EffType::empty(),
                        function.span,
                    ))
                })
                .collect();
            let mut call = hir_syn::static_apply_with_argument_passing(
                default_id,
                ty.clone(),
                arguments,
                arg_conventions_for_args(&ty.args),
                function.span,
            );
            if let hir::NodeKind::StaticApply(app) = &mut call {
                app.inst_data = inst_data;
                app.argument_names = default.arg_names.clone();
            }
            if default_id.module != output.module_id() {
                ty_env.new_deps.insert(default_id.module);
            }
            ty_env.ir_arena.alloc(hir::Node::new(
                call,
                ty.ret,
                ty.effects.clone(),
                function.span,
            ))
        } else if matches!(
            kind,
            EmitFunctionKind::SubscriptMember {
                provenance: YieldProvenance::AddressorPlace,
                ..
            }
        ) {
            ty_inf.check_implicit_addressor_return_expr(
                &mut ty_env,
                function.body,
                descr.definition.ty_scheme.ty.ret,
                expected_span,
            )?
        } else {
            ty_inf.check_expr(
                &mut ty_env,
                function.body,
                kind.body_expected_ty(descr.definition.ty_scheme.ty.ret),
                MutType::constant(),
                expected_span,
            )?
        };
        report_needless_returns_in_tail(ty_env.ast_arena, function.body, ty_env.warnings);
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
        let mut body_descr = body_descr;
        if let Some(body_descr) = &body_descr {
            // A contract's effects are fixed: the body must fit them.
            ty_inf.add_effect_inclusion_constraint_with_origin(
                &fn_arena[fn_node_id].effects,
                function.span,
                &body_descr.definition.ty_scheme.ty.effects,
                function.span,
                EffectConstraintOrigin::Inference,
            )?;
        }
        let descr = match &mut body_descr {
            Some(descr) => descr,
            None => {
                let descr = output.get_function_by_id_mut(*id).unwrap();
                descr.definition.ty_scheme.ty.effects = ty_inf.unify_effects(
                    &fn_arena[fn_node_id].effects,
                    &descr.definition.ty_scheme.ty.effects,
                    function.span,
                )?;
                descr
            }
        };
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
        if let Some(scheme) = reference_schemes.get(function_index) {
            // The bodies that follow still name this function through its shape.
            output.functions[id.as_index()].definition.ty_scheme = scheme.clone();
        }
        output.deps.extend(new_deps);
        ty_inf.own_constraints_since(constraint_scope, *id);
        body_references.push(first_reference..ty_inf.group_references().len());
    }
    // The references between the functions of the group, by the indices of these functions.
    let group_references = body_references
        .iter()
        .enumerate()
        .flat_map(|(owner, references)| {
            ty_inf.group_references()[references.clone()]
                .iter()
                .map(move |reference| (owner, reference))
        })
        .filter_map(|(owner, reference)| {
            let callee = local_fns
                .iter()
                .position(|id| reference.function.function == *id)?;
            Some((owner, callee, reference.fn_ty.clone(), reference.span))
        })
        .collect::<Vec<GroupReferenceIn>>();
    // From here on, each function is its body's rigid instance, as in ordinary emission.
    for (id, ty) in local_fns.iter().zip(&body_tys) {
        output.functions[id.as_index()].definition.ty_scheme =
            TypeScheme::new_just_type(ty.clone());
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
            ty_inf.add_effect_inclusion_constraint_with_origin(
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

    for ((input, id), declared) in ast_functions().zip(&local_fns).zip(&declared_signatures) {
        if let (Some(declared), Some((trait_id, index))) = (declared, input.trait_default) {
            ty_inf.add_effect_inclusion_constraint_with_origin(
                &output.functions[id.as_index()]
                    .definition
                    .ty_scheme
                    .ty
                    .effects,
                input.function.span,
                &declared.ty.effects,
                input.function.span,
                EffectConstraintOrigin::TraitMethodImpl {
                    trait_id,
                    method_name: output.trait_def(trait_id).method(index).0,
                    impl_span: input.function.span,
                },
            )?;
        }
    }

    // Third pass, perform the unification.
    let mut solver = trait_solver_from_module!(output, others);
    let mut ty_inf = ty_inf.unify(&mut solver, solver_arena)?;
    ty_inf.set_publication_inputs(
        local_fns
            .iter()
            .flat_map(|id| {
                output.functions[id.as_index()]
                    .definition
                    .ty_scheme
                    .ty
                    .args
                    .iter()
                    .map(|arg| arg.ty)
            })
            .chain(function_explicit_root_tys.iter().flatten().copied()),
    );
    ty_inf.prepare_type_bounds()?;
    let generated = solver.finish().commit(
        &mut output.functions,
        &mut output.def_table,
        &mut pending_functions,
    );
    elaborate_generated_functions(output, others, &mut pending_functions, generated)?;
    let module_env = ModuleEnv::new(output, others);
    ty_inf.log_debug_substitution_tables(module_env);
    ty_inf.log_debug_constraints(module_env);

    // Resolve local-storage decisions before defaulting so only finalized ownership semantics add `Value`.
    let value_trait_id = module_env.expect_std_trait_id(VALUE_TRAIT_NAME);
    for id in local_fns.iter() {
        let mut ty_inf = ty_inf.constraint_owner_scope(*id);
        for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
            let descr = pending_functions
                .get_mut(&function_id)
                .expect("expected pending function body");
            ty_inf.resolve_local_storage_and_activate_value_constraints(
                &descr.code.arena,
                descr.code.entry_node_id,
                &mut descr.locals,
                value_trait_id,
                module_env,
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
            let head_boundary = ty_inf.constraint_boundary(head_quantifiers.iter().copied());
            let orphan_constraints =
                head_boundary.owned_inaccessible_constraints(ty_inf.remaining_constraints());
            let scope = DefaultingScope::from_constraints(&orphan_constraints);
            let mut solver = trait_solver_from_module!(output, others);
            ty_inf.resolve_defaults_to_fixed_point(&scope, &mut solver, solver_arena)?;
            ty_inf.finalize_type_bounds(&mut solver, solver_arena)?;
            let generated = solver.finish().commit(
                &mut output.functions,
                &mut output.def_table,
                &mut pending_functions,
            );
            elaborate_generated_functions(output, others, &mut pending_functions, generated)?;
            // Publication can reveal product layouts that were unknown during
            // the pre-defaulting ownership pass. Activate their evidence now.
            let module_env = ModuleEnv::new(output, others);
            for id in &local_fns {
                let mut ty_inf = ty_inf.constraint_owner_scope(*id);
                for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                    let descr = pending_functions
                        .get_mut(&function_id)
                        .expect("pending function body");
                    ty_inf.resolve_local_storage_and_activate_value_constraints(
                        &descr.code.arena,
                        descr.code.entry_node_id,
                        &mut descr.locals,
                        value_trait_id,
                        module_env,
                    );
                }
            }
            let mut solver = trait_solver_from_module!(output, others);
            ty_inf.finalize_type_bounds(&mut solver, solver_arena)?;
            ty_inf.resolve_defaults_to_fixed_point(&scope, &mut solver, solver_arena)?;
            ty_inf.finalize_type_bounds(&mut solver, solver_arena)?;
            let generated = solver.finish().commit(
                &mut output.functions,
                &mut output.def_table,
                &mut pending_functions,
            );
            elaborate_generated_functions(output, others, &mut pending_functions, generated)?;

            // A type variable of the methods that nothing determines defaults to `never`; the head
            // and the method types are protected.
            let mut protected = Vec::new();
            for ty in trait_output
                .input_tys
                .iter()
                .chain(&trait_output.output_tys)
            {
                protected.extend(ty_inf.substitute_in_type(*ty).inner_ty_vars());
            }
            for id in &local_fns {
                let fn_ty = &output.functions[id.as_index()].definition.ty_scheme.ty;
                protected.extend(ty_inf.substitute_in_fn_type(fn_ty).inner_ty_vars());
            }
            default_unconstrained_types_to_never(
                &mut ty_inf,
                function_bodies(&local_fns, &associated_lambdas, &pending_functions),
                protected,
                ModuleEnv::new(output, others),
            )?;

            let mut head_effect_vars = trait_output
                .input_tys
                .iter()
                .chain(&trait_output.output_tys)
                .flat_map(|ty| ty_inf.substitute_in_type(*ty).inner_effect_vars())
                .collect::<FxHashSet<_>>();
            for eff in &trait_output.output_effs {
                ty_inf
                    .substitute_in_effect_type(eff)
                    .fill_with_inner_effect_vars(&mut head_effect_vars);
            }
            // Implementation methods are quantified over the head only, so their own effect
            // variables, such as that of a callback parameter written without effects, are fixed.
            minimize_body_effects(output, &[], head_effect_vars, &mut ty_inf)?;
            ty_inf.finalize_effects()?;

            // Body inference may not specialize written generics. Context reduction below may
            // determine output-only variables from functional dependencies; its input roots
            // remain rigid throughout.
            let impl_ctx = trait_ctx.as_ref().expect("impl context");
            let resolved_roots = (0..impl_ctx.generic_type_params.len())
                .map(|index| {
                    let ty = impl_annotation_subst
                        .as_ref()
                        .and_then(|(subst, _)| subst.get(&TypeVar::new(index as u32)))
                        .expect("a written impl generic has a type variable");
                    ty_inf.substitute_in_type(*ty)
                })
                .collect::<Vec<_>>();
            distinct_written_type_vars(impl_ctx.generic_type_params, resolved_roots, || {
                GenericParamsOwner::TraitImpl {
                    trait_name: impl_ctx.trait_def.name,
                }
            })?;

            let input_tys = ty_inf.substitute_in_types(&trait_output.input_tys);
            if output.is_trait_impl_exportable(
                trait_ctx.as_ref().expect("impl context").trait_id,
                &input_tys,
                others,
            ) {
                ty_inf.normalize_remaining_constraints();
                let constraints = ty_inf.remaining_constraints().to_vec();
                let mut solver = trait_solver_from_module!(output, others);
                let constraints = solver
                    .reduce_public_requirements(constraints, &input_tys, &mut ty_inf, solver_arena)
                    .map_err(|error| {
                        error.with_private_requirement_names(
                            impl_ctx.generic_type_params.iter().enumerate().filter_map(
                                |(index, name)| {
                                    let root = *impl_annotation_subst
                                        .as_ref()?
                                        .0
                                        .get(&TypeVar::new(index as u32))?;
                                    let root = ty_inf.substitute_in_type(root);
                                    Some((*root.data().as_variable()?, name.0))
                                },
                            ),
                        )
                    })?;
                trait_output.evidence_plan = constraints.evidence;
                for id in &local_fns {
                    for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                        pending_functions
                            .get_mut(&function_id)
                            .expect("pending impl body")
                            .evidence_plan = trait_output.evidence_plan.clone();
                    }
                }
                ty_inf.replace_remaining_constraints(constraints.requirements);
                ty_inf.finalize_effects()?;
                let generated = solver.finish().commit(
                    &mut output.functions,
                    &mut output.def_table,
                    &mut pending_functions,
                );
                elaborate_generated_functions(output, others, &mut pending_functions, generated)?;
            }

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
                return Err(internal_compilation_error!(UnresolvedConstraints {
                    constraints: remaining_orphans.iter().map(|c| (*c).clone()).collect(),
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
        check_declared_effects_not_combined(output, &associated_lambdas, &local_fns, &mut ty_inf)?;
        // The impl constraints are not yet part of the method schemes, but they determine the
        // effects of the methods' calls to their evidence, so these effects must be retained.
        let impl_constraint_effect_vars = {
            ty_inf.normalize_remaining_constraints();
            let mut head_tys = ty_inf.substitute_in_types(&trait_output.input_tys);
            head_tys.extend(ty_inf.substitute_in_types(&trait_output.output_tys));
            let head_boundary = ConstraintBoundary::from_seed_ty_vars(collect_ty_vars(&head_tys));
            let mut vars = FxHashSet::default();
            for constraint in head_boundary.accessible_constraints(ty_inf.remaining_constraints()) {
                constraint.fill_with_inner_effect_vars(&mut vars);
            }
            vars
        };
        default_output_effects_in_functions(
            output,
            &mut pending_functions,
            &associated_lambdas,
            &local_fns,
            &impl_constraint_effect_vars,
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

        trait_output.evidence_plan.substitute(&mut ty_inf);
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
            let unbound = hir::all_unbound_ty_vars(function_bodies(
                slice::from_ref(id),
                &associated_lambdas,
                &pending_functions,
            ));
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
        let generated = solver.finish().commit(
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
            trait_output.evidence_plan.instantiate_in_place(&mut mapper);
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

        // Effect variables are quantified like type variables: those occurring only in the impl
        // constraints are determined by those constraints' output effects.
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
        trait_output
            .constraints
            .fill_with_inner_effect_vars(&mut effect_quantifiers);
        let mut effect_quantifiers = effect_quantifiers.into_iter().sorted().collect::<Vec<_>>();
        trait_output.eff_var_count = effect_quantifiers.len() as u32;

        // Evidence belongs to the method that uses it, including its nested lambdas.
        // Leaf methods keep their original ABI even when another slot uses a default.
        let methods_use_self = local_fns
            .iter()
            .map(|id| ty_inf.given_used_by(*id, self_given.expect("impl self evidence")))
            .collect::<Vec<_>>();
        let method_self_constraint = PubTypeConstraint::new_have_trait(
            trait_id,
            trait_output.input_tys.clone(),
            trait_output.output_tys.clone(),
            trait_output.output_effs.clone(),
            trait_ctx.span,
        );

        // The written name of each impl variable, at the position normalization gives it.
        if let Some((ty_subst, eff_subst)) = &impl_annotation_subst {
            for (index, (name, _)) in trait_ctx.generic_type_params.iter().enumerate() {
                let position = ty_subst
                    .get(&TypeVar::new(index as u32))
                    .map(|root| ty_inf.substitute_in_type(*root))
                    .and_then(|root| root.data().as_variable().copied())
                    .and_then(|var| quantifiers.iter().position(|quantifier| *quantifier == var));
                if let Some(position) = position {
                    trait_output
                        .generic_names
                        .tys
                        .insert(TypeVar::new(position as u32), *name);
                }
            }
            for (index, name) in trait_ctx.generic_effect_param_names.iter().enumerate() {
                let position = eff_subst
                    .get(&EffectVar::new(index as u32))
                    .and_then(|row| ty_inf.substitute_in_effect_type(row).to_single_variable())
                    .and_then(|var| {
                        effect_quantifiers
                            .iter()
                            .position(|quantifier| *quantifier == var)
                    });
                if let Some(position) = position {
                    trait_output
                        .generic_names
                        .effs
                        .insert(EffectVar::new(position as u32), *name);
                }
            }
        }

        // Fifth pass, normalize the input types/effects, substitute the types in the functions and input/output types.
        let ty_origins = quantifiers.clone();
        let effect_origins = effect_quantifiers.clone();
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
        trait_output.evidence_plan.instantiate_in_place(&mut mapper);
        for (method_index, id) in local_fns.iter().enumerate() {
            let uses_self = methods_use_self[method_index];
            let method_index = TraitMethodIndex::from_index(method_index);
            for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                let descr = &mut output.functions[function_id.as_index()];
                descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
                descr.definition.ty_scheme.ty_quantifiers = quantifiers.clone();
                descr.definition.ty_scheme.eff_quantifiers =
                    effect_quantifiers.iter().copied().collect();
                descr.definition.ty_scheme.constraints = trait_output.constraints.clone();
                if uses_self {
                    descr
                        .definition
                        .ty_scheme
                        .constraints
                        .push(method_self_constraint.map(&mut mapper));
                }
                debug_assert!(
                    TypeScheme::<FnType>::list_eff_vars(
                        &descr.definition.ty_scheme.ty,
                        descr.definition.ty_scheme.constraints.iter(),
                    )
                    .is_subset(&descr.definition.ty_scheme.eff_quantifiers),
                    "impl method mentions an effect variable the impl does not quantify"
                );
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
        let method_dicts = local_fns
            .iter()
            .map(|id| {
                extra_parameters_from_constraints(
                    &output.functions[id.as_index()]
                        .definition
                        .ty_scheme
                        .constraints,
                    ModuleEnv::new(output, others),
                )
            })
            .collect::<Vec<_>>();
        trait_output.method_requirements = method_dicts
            .iter()
            .map(|dicts| DictionaryEntryRequirements::from_callable(dicts.requirements.clone()))
            .collect();
        let mut module_inst_data = FxHashMap::default();
        for (id, dicts) in local_fns.iter().zip(&method_dicts) {
            // The methods of an implementation have its quantifiers, and are inferred jointly.
            insert_inst_data_for_function_and_lambdas(
                &mut module_inst_data,
                &associated_lambdas,
                *id,
                LateFunctionInstData {
                    requirements: dicts.clone(),
                    ty_origins: ty_origins.clone(),
                    effect_origins: effect_origins.clone(),
                    effects_per_reference: false,
                    reference_effects: FxHashMap::default(),
                },
            );
        }
        for (id, dicts) in local_fns.iter().zip(&method_dicts) {
            borrow_check_and_elaborate_dict(
                output,
                others,
                &mut pending_functions,
                &associated_lambdas,
                dicts,
                &module_inst_data,
                id,
                warnings,
            )?;
        }

        refresh_debug_info_for_functions(output, &associated_lambdas, &local_fns);
        for (input, id) in ast_functions().zip(&local_fns) {
            if input.forward_default.is_some() {
                output.functions[id.as_index()].spans = None;
            }
        }
        Ok(Emitted::TraitImpl(Box::new(trait_output)))
    } else {
        // We are emitting normal module functions.

        // Default orphan constraints for each function into the unification tables.
        for (id, explicit_root_tys) in local_fns.iter().zip(function_explicit_root_tys.iter()) {
            let scope = function_defaulting_scope(
                &mut ty_inf,
                &output.functions[id.as_index()].definition.ty_scheme.ty,
                pending_functions.get(id),
                explicit_root_tys,
            );
            let mut solver = trait_solver_from_module!(output, others);
            ty_inf.resolve_defaults_to_fixed_point(&scope, &mut solver, solver_arena)?;
            let generated = solver.finish().commit(
                &mut output.functions,
                &mut output.def_table,
                &mut pending_functions,
            );
            elaborate_generated_functions(output, others, &mut pending_functions, generated)?;
        }
        // All function scopes have had their eligible defaults applied before
        // any pending output component is conservatively published.
        {
            let mut solver = trait_solver_from_module!(output, others);
            ty_inf.finalize_type_bounds(&mut solver, solver_arena)?;
            let generated = solver.finish().commit(
                &mut output.functions,
                &mut output.def_table,
                &mut pending_functions,
            );
            elaborate_generated_functions(output, others, &mut pending_functions, generated)?;
            // Publication can reveal product layouts that were unknown during
            // the pre-defaulting ownership pass. Activate their evidence now.
            let module_env = ModuleEnv::new(output, others);
            for id in &local_fns {
                let mut ty_inf = ty_inf.constraint_owner_scope(*id);
                for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                    let descr = pending_functions
                        .get_mut(&function_id)
                        .expect("pending function body");
                    ty_inf.resolve_local_storage_and_activate_value_constraints(
                        &descr.code.arena,
                        descr.code.entry_node_id,
                        &mut descr.locals,
                        value_trait_id,
                        module_env,
                    );
                }
            }
            let mut solver = trait_solver_from_module!(output, others);
            ty_inf.finalize_type_bounds(&mut solver, solver_arena)?;
            // Publication can identify a pending output with its own input,
            // making an already-local numeric or unit default eligible. Retry
            // using current signature boundaries, then validate the choices.
            for (id, explicit_root_tys) in local_fns.iter().zip(&function_explicit_root_tys) {
                let scope = function_defaulting_scope(
                    &mut ty_inf,
                    &output.functions[id.as_index()].definition.ty_scheme.ty,
                    pending_functions.get(id),
                    explicit_root_tys,
                );
                if !scope.is_empty() {
                    ty_inf.resolve_defaults_to_fixed_point(&scope, &mut solver, solver_arena)?;
                }
            }
            ty_inf.finalize_type_bounds(&mut solver, solver_arena)?;
            let generated = solver.finish().commit(
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
                if let Some((ty_var, ty, span)) =
                    first_unbound_type_in_constraints(remaining_orphans.iter().copied())
                {
                    return Err(internal_compilation_error!(UnboundTypeVar {
                        ty_var,
                        ty,
                        span
                    }));
                }
                return Err(internal_compilation_error!(Internal {
                    error: format!(
                        "Orphan constraints found in module fn: {}",
                        remaining_orphans.format_with(&module_env)
                    ),
                    span: remaining_orphans[0].use_site(),
                }));
            }
        }

        if matches!(mode, GroupMode::Discover) {
            let shapes = discovered_shapes(
                output,
                &mut ty_inf,
                ast_functions(),
                &local_fns,
                &function_explicit_root_tys,
                &recursive_function_ids,
                &pending_functions,
                &group_declarations,
            )?;
            return Ok(Emitted::Shapes(shapes));
        }

        // A type variable of the bodies that nothing determines defaults to `never`; the
        // signatures of all functions of the group are protected.
        let mut protected = Vec::new();
        for (id, explicit_root_tys) in local_fns.iter().zip(&function_explicit_root_tys) {
            let fn_ty = &output.functions[id.as_index()].definition.ty_scheme.ty;
            protected.extend(ty_inf.substitute_in_fn_type(fn_ty).inner_ty_vars());
            for ty in explicit_root_tys {
                protected.extend(ty_inf.substitute_in_type(*ty).inner_ty_vars());
            }
        }
        default_unconstrained_types_to_never(
            &mut ty_inf,
            function_bodies(&local_fns, &associated_lambdas, &pending_functions),
            protected,
            ModuleEnv::new(output, others),
        )?;

        // Types are determined. The contracts of a group settle from here, over copies of this
        // state: the first round takes the contracts of functions that call nothing.
        let mut settlement = if let GroupMode::Settle {
            shapes, exported, ..
        } = &mode
        {
            let contracts = shapes
                .iter()
                .map(|shape| {
                    let mut bottom = GroupContract::bottom(shape);
                    let subst = (
                        shape
                            .scheme
                            .ty_quantifiers
                            .iter()
                            .map(|var| (*var, ty_inf.substitute_in_type(group_instance[var])))
                            .collect::<TypeInstSubst>(),
                        EffectsInstSubst::default(),
                    );
                    bottom.scheme.ty = bottom
                        .scheme
                        .ty
                        .map(&mut BitmapInstantiationMapper::new(&subst));
                    bottom.scheme.ty_quantifiers = Vec::new();
                    bottom
                })
                .collect();
            let (signatures, own_requirements) = baseline_requirements(
                output,
                others,
                ast_functions(),
                &local_fns,
                &function_explicit_root_tys,
                *exported,
                &mut pending_functions,
                &associated_lambdas,
                &mut ty_inf,
                solver_arena,
            )?;
            Some(Settlement {
                signatures,
                own_requirements,
                requirements: Vec::new(),
                requirement_ranks: Vec::new(),
                baseline: ty_inf.clone(),
                pending_functions: pending_functions.clone(),
                written_functions: local_fns
                    .iter()
                    .flat_map(|id| function_and_associated_lambdas(id, &associated_lambdas))
                    .collect(),
                warning_count: warnings.len(),
                contracts,
                references: group_references.clone(),
                rounds_done: 0,
                round_bound: max_refinement_rounds(shapes),
                checkpoint: None,
                left_out: local_fns.iter().map(|_| None).collect(),
                written_types: ast_functions()
                    .zip(&function_explicit_root_tys)
                    .map(|(input, roots)| {
                        let function = input.function;
                        let params = function.generic_params.type_params().to_vec();
                        (function.name, params, roots.clone())
                    })
                    .collect(),
                reference_effects: Vec::new(),
                answered_applications: ty_inf.answered_applications(),
                alike: FxHashMap::default(),
            })
        } else {
            None
        };
        let function_leading_effects = loop {
            if let Some(settlement) = &mut settlement {
                let started = settlement.start_round(
                    &mut ty_inf,
                    &mut pending_functions,
                    output,
                    others,
                    warnings,
                    &local_fns,
                    solver_arena,
                )?;
                if !started {
                    continue;
                }
            }

            // The applications of traits that the bodies leave to their callers, with those that
            // a declaration gives.
            let requirements = |ty_inf: &mut UnifiedTypeInference| {
                ty_inf.normalize_remaining_constraints();
                let mut applications = declared_signatures
                    .iter()
                    .flatten()
                    .flat_map(|declared| declared.constraints.iter())
                    .map(|constraint| ty_inf.substitute_in_constraint(constraint))
                    .collect::<Vec<_>>();
                applications.extend(ty_inf.remaining_constraints().iter().cloned());
                applications
            };
            // The written effect generics of a function that the round leaves out are not
            // judged: they are as its signature has them.
            let mut observable = FxHashSet::default();
            if let Some(settlement) = &settlement {
                for (written, left_out) in function_written_effects.iter().zip(&settlement.left_out)
                {
                    if left_out.is_some() {
                        observable.extend(written.iter().copied());
                    }
                }
            }
            if let Err(error) = minimize_body_effects(output, &local_fns, observable, &mut ty_inf) {
                // A written effect generic that no requirement determines in this round may be
                // determined by one that a later contract brings: its function is left out.
                let function = match &*error {
                    CompilationErrorImpl::AmbiguousEffectGeneric { span, .. } => ast_functions()
                        .position(|input| {
                            let function = input.function.span;
                            function.source_id() == span.source_id()
                                && function.start() <= span.start()
                                && span.end() <= function.end()
                        }),
                    _ => None,
                };
                match (&mut settlement, function) {
                    (Some(settlement), Some(index)) if settlement.left_out[index].is_none() => {
                        settlement.left_out[index] = Some(error);
                        continue;
                    }
                    _ => return Err(error),
                }
            }
            ty_inf.finalize_effects()?;

            // Effects are final: two applications of a trait that differed by an effect still to
            // infer, as the one a callback gets when it is passed on, may now be the same, and
            // then so are their outputs. This holds too between an application that a body needs
            // and one that its declaration gives.
            //
            // In a group that settles, the effects of a round are provisional: callees that
            // still look pure can make two applications one that later rounds keep apart. So
            // what follows from them is checked function by function, and a function for which
            // it fails keeps its contract for this round, see [`Settlement::end_round`].
            let mut round_errors: Vec<Option<InternalCompilationError>> =
                local_fns.iter().map(|_| None).collect();
            let is_left_out = |settlement: &Option<Settlement>, index: usize| {
                settlement
                    .as_ref()
                    .is_some_and(|settlement| settlement.left_out[index].is_some())
            };
            {
                let env = ModuleEnv::new(output, others);
                let polarities =
                    |id: TraitId| trait_output_effect_polarities(id, &|id| env.trait_def(id));
                if let Some(settlement) = &mut settlement {
                    // A function whose applications cannot be made one, or for which this
                    // changes a type of the group, is left out, and the round starts again:
                    // the group has one instance of its types, so the other functions would
                    // fail with it.
                    let mut left_out = None;
                    for (index, id) in local_fns.iter().enumerate() {
                        if settlement.left_out[index].is_some() {
                            continue;
                        }
                        let mut applications = requirements(&mut ty_inf)
                            .into_iter()
                            .filter(|application| {
                                !ty_inf.is_requirement_of_others(application, *id)
                            })
                            .collect::<Vec<_>>();
                        let mut coalesced =
                            ty_inf.coalesce_constraint_outputs(&mut applications, &polarities);
                        if coalesced.is_ok() {
                            coalesced = settlement.keeps_types(&mut ty_inf);
                        }
                        if let Err(error) = coalesced {
                            left_out = Some((index, error));
                            break;
                        }
                    }
                    if let Some((index, error)) = left_out {
                        settlement.left_out[index] = Some(error);
                        continue;
                    }
                } else {
                    let mut applications = requirements(&mut ty_inf);
                    ty_inf.coalesce_constraint_outputs(&mut applications, &polarities)?;
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
            for (index, (id, round_error)) in local_fns.iter().zip(&mut round_errors).enumerate() {
                if is_left_out(&settlement, index) {
                    continue;
                }
                let checked = check_declared_effects_not_combined(
                    output,
                    &associated_lambdas,
                    slice::from_ref(id),
                    &mut ty_inf,
                );
                match checked {
                    Err(error) if settlement.is_some() => {
                        round_error.get_or_insert(error);
                    }
                    checked => checked?,
                }
            }

            // Recursive-return defaulting inspects the final constraints. A contract already says
            // what its function returns.
            ty_inf.normalize_remaining_constraints();
            if !mode.has_fixed_types() {
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
            }
            // In a group that settles, a requirement that bodies make is of these bodies: each
            // function has its own instances of what the functions it names require.
            let requirements_of_others = local_fns
                .iter()
                .map(|id| {
                    ty_inf
                        .remaining_constraints()
                        .iter()
                        .map(|constraint| {
                            settlement.is_some() && ty_inf.is_requirement_of_others(constraint, *id)
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            // Take final substituted constraints.
            let all_constraints = ty_inf.take_constraints();
            let requirements_of_others = requirements_of_others
                .into_iter()
                .map(|of_others| {
                    all_constraints
                        .iter()
                        .zip(of_others)
                        .filter(|(_, of_others)| *of_others)
                        .map(|(constraint, _)| constraint_ptr(constraint))
                        .collect::<FxHashSet<PubTypeConstraintPtr>>()
                })
                .collect::<Vec<_>>();

            // The type variables of the signatures of the group.
            let group_signature_vars = local_fns
                .iter()
                .flat_map(|id| {
                    output.functions[id.as_index()]
                        .definition
                        .ty_scheme
                        .ty
                        .inner_ty_vars()
                })
                .collect::<FxHashSet<_>>();
            // For each function: filter constraints, check unbounds, finalize type scheme.
            let mut used_constraints: FxHashSet<PubTypeConstraintPtr> = FxHashSet::default();
            for (index, (((((input, id), explicit_root_tys), declared), of_others), round_error)) in
                ast_functions()
                    .zip(local_fns.iter())
                    .zip(function_explicit_root_tys.iter())
                    .zip(&declared_signatures)
                    .zip(&requirements_of_others)
                    .zip(&mut round_errors)
                    .enumerate()
            {
                if round_error.is_some() || is_left_out(&settlement, index) {
                    continue;
                }
                let published = (|| -> Result<(), InternalCompilationError> {
                    let function = input.function;
                    let descr = &output.functions[id.as_index()];
                    if declared.is_none() {
                        let resolved_roots = explicit_root_tys
                            .iter()
                            .map(|root| ty_inf.substitute_in_type(*root))
                            .collect::<Vec<_>>();
                        distinct_written_type_vars(
                            function.generic_params.type_params(),
                            resolved_roots,
                            || GenericParamsOwner::Function {
                                name: function.name.0,
                            },
                        )?;
                    }
                    // Find constraints related to this function's signature.
                    let mut sig_ty_vars = descr.definition.ty_scheme.ty.inner_ty_vars();
                    let explicit_ty_vars = explicit_root_tys
                        .iter()
                        .flat_map(|ty| ty_inf.substitute_in_type(*ty).inner_ty_vars().into_iter())
                        .collect::<Vec<_>>();
                    sig_ty_vars.extend(explicit_ty_vars.iter().copied());
                    sig_ty_vars = sig_ty_vars.into_iter().unique().collect();
                    let sig_boundary =
                        ConstraintBoundary::from_seed_ty_vars(sig_ty_vars.iter().copied());
                    let related_constraints = sig_boundary
                        .accessible_constraints(&all_constraints)
                        .into_iter()
                        .filter(|constraint| !of_others.contains(&constraint_ptr(constraint)))
                        .collect::<Vec<_>>();
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

                    // Check for unbound type variables, including in the function's lambdas.
                    let unbound = hir::all_unbound_ty_vars(function_bodies(
                        slice::from_ref(id),
                        &associated_lambdas,
                        &pending_functions,
                    ));
                    let env = ModuleEnv::new(output, others);
                    let uninstantiated_unbound = if settlement.is_some() {
                        // A type that the body does not observe and that is of the signature of
                        // another function of the group is `never` in this body, as it is at a
                        // call outside the group that does not determine it.
                        let (of_others, own): (IndexMap<_, _>, IndexMap<_, _>) =
                            unbound.into_iter().partition(|(ty_var, _)| {
                                !quantifiers.contains(ty_var)
                                    && group_signature_vars.contains(ty_var)
                            });
                        let mut unobserved = check_unbounds(own, &quantifiers, &env)?;
                        unobserved.extend(of_others.into_keys());
                        unobserved
                    } else {
                        check_unbounds(unbound, &quantifiers, &env)?
                    };

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
                        for function_id in function_and_associated_lambdas(id, &associated_lambdas)
                        {
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
                                .instantiate_and_drop_if_solved(
                                    &mut drop_subst,
                                    &mut solver,
                                    solver_arena,
                                )
                                .transpose()
                        })
                        .collect::<Result<_, _>>()?;
                    let generated = solver.finish().commit(
                        &mut output.functions,
                        &mut output.def_table,
                        &mut pending_functions,
                    );
                    elaborate_generated_functions(
                        output,
                        others,
                        &mut pending_functions,
                        generated,
                    )?;

                    let mut constraints = constraints;
                    if let Some(declared) = declared {
                        constraints = fit_declared_signature(
                            declared,
                            constraints,
                            input,
                            output,
                            others,
                            &mut ty_inf,
                        )?;
                        let declared_ty = ty_inf.substitute_in_fn_type(&declared.ty);
                        output.functions[id.as_index()].definition.ty_scheme.ty = declared_ty;
                    }

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
                        if declared.is_some() {
                            descr.definition.ty_scheme.eff_quantifiers =
                                TypeScheme::<FnType>::list_eff_vars(
                                    &descr.definition.ty_scheme.ty,
                                    constraints.iter(),
                                );
                        }
                        descr.definition.generic_params =
                            function.generic_params.type_params().to_vec();
                        descr.definition.generic_effect_params =
                            function.generic_params.effect_params().to_vec();
                        pending_functions
                            .get_mut(&function_id)
                            .expect("expected pending function body")
                            .definition = descr.definition.clone();
                    }

                    // Log dropped constraints.
                    if log_enabled!(log::Level::Trace) {
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
                    Ok(())
                })();
                match published {
                    Err(error) if settlement.is_some() => *round_error = Some(error),
                    published => published?,
                }
            }

            default_output_effects_in_functions(
                output,
                &mut pending_functions,
                &associated_lambdas,
                &local_fns,
                &FxHashSet::default(),
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
            // A function that failed in this round did not take its requirements.
            let all_published = round_errors.iter().all(Option::is_none)
                && (0..local_fns.len()).all(|index| !is_left_out(&settlement, index));
            if !unused_constraints.is_empty() && all_published {
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

            // Every member of an exported recursive group needs the public leaves of its
            // requirements: a private member cannot recover them backwards from a dictionary for the
            // unreduced private requirement. A group that settles has them already.
            let exports_group = group_is_exported(ast_functions());
            let mut published_requirements_changed = false;
            for ((input, id), explicit_roots) in ast_functions()
                .zip(&local_fns)
                .zip(&function_explicit_root_tys)
            {
                // A group that settles has the public form of its requirements already.
                if !exports_group || input.trait_default.is_some() || settlement.is_some() {
                    continue;
                }
                let scheme = output.functions[id.as_index()].definition.ty_scheme.clone();
                let rigid = scheme
                    .ty
                    .args
                    .iter()
                    .map(|arg| arg.ty)
                    .chain(explicit_roots.iter().copied())
                    .collect::<Vec<_>>();
                let Some(constraints) = public_requirements(
                    &scheme.constraints,
                    &rigid,
                    input.function,
                    explicit_roots,
                    *id,
                    output,
                    others,
                    &mut pending_functions,
                    &associated_lambdas,
                    &mut ty_inf,
                    solver_arena,
                )?
                else {
                    continue;
                };
                published_requirements_changed = true;
                for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                    output.functions[function_id.as_index()]
                        .definition
                        .ty_scheme
                        .constraints = constraints.clone();
                    pending_functions
                        .get_mut(&function_id)
                        .expect("pending function body")
                        .definition
                        .ty_scheme
                        .constraints = constraints.clone();
                }
            }
            if published_requirements_changed {
                ty_inf.finalize_effects()?;
                substitute_and_canonicalize_functions(
                    output,
                    &mut pending_functions,
                    &associated_lambdas,
                    &local_fns,
                    &mut ty_inf,
                );
                for id in &local_fns {
                    let scheme = &output.functions[id.as_index()].definition.ty_scheme;
                    let quantifiers = scheme
                        .ty_quantifiers
                        .iter()
                        .filter_map(|var| {
                            ty_inf
                                .substitute_in_type(Type::variable(*var))
                                .data()
                                .as_variable()
                                .copied()
                        })
                        .chain(TypeScheme::list_ty_vars(
                            &scheme.ty,
                            scheme.constraints.iter(),
                        ))
                        .unique()
                        .collect::<Vec<_>>();
                    for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                        output.functions[function_id.as_index()]
                            .definition
                            .ty_scheme
                            .ty_quantifiers = quantifiers.clone();
                        pending_functions
                            .get_mut(&function_id)
                            .expect("pending function body")
                            .definition
                            .ty_scheme
                            .ty_quantifiers = quantifiers.clone();
                    }
                }
            }

            // The effect variables that each published signature numbers first: its written generics.
            let mut function_leading_effects = function_written_effects.clone();
            if let Some(settlement) = &mut settlement {
                let first = ast_functions()
                    .next()
                    .expect("a group has a function")
                    .function;
                // The signatures number their effects as the contracts do.
                match settlement.end_round(
                    &mut ty_inf,
                    &function_written_effects,
                    first,
                    round_errors,
                )? {
                    Some(numbered) => function_leading_effects = numbered,
                    None => continue,
                }
            }
            break function_leading_effects;
        };

        // Fifth pass, normalize the type schemes, substitute the types in the functions.
        let mut function_ty_origins = Vec::new();
        let mut function_effect_substs = Vec::new();
        let mut function_effect_origins = Vec::new();
        for (((input, id), written_effects), leading_effects) in ast_functions()
            .zip(local_fns.iter())
            .zip(&function_written_effects)
            .zip(&function_leading_effects)
        {
            let descr = &mut output.functions[id.as_index()];
            function_ty_origins.push(descr.definition.ty_scheme.ty_quantifiers.clone());
            let subst = descr
                .definition
                .ty_scheme
                .normalize_with_leading_effects(leading_effects);
            function_effect_substs.push(subst.1.clone());
            function_effect_origins.push(
                subst
                    .1
                    .iter()
                    .filter_map(|(origin, row)| Some((row.to_single_variable()?, *origin)))
                    .sorted()
                    .map(|(_, origin)| origin)
                    .collect::<Vec<_>>(),
            );
            let normalized_scheme = descr.definition.ty_scheme.clone();
            // A written generic that the scheme does not retain leaves no name behind, so that
            // the retained ones keep theirs by position.
            let retained_effect_params = written_effects
                .iter()
                .zip(input.function.generic_params.effect_params())
                .filter(|(var, _)| subst.1.get(var).is_some_and(|row| !row.is_empty()))
                .map(|(_, name)| *name)
                .collect::<Vec<_>>();
            for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                let descr = &mut output.functions[function_id.as_index()];
                let mut mapper = BitmapInstantiationMapper::new(&subst);
                assert_eq!(
                    written_effects.len(),
                    descr.definition.generic_effect_params.len(),
                    "each written effect generic has its variable"
                );
                descr.definition.generic_effect_params = retained_effect_params.clone();
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
            if let EmitFunctionKind::SubscriptMember {
                subscript_id,
                subscript_name,
                projection_key,
                member_function_kind,
                provenance,
                ..
            } = input.kind
            {
                let definition = output.functions[id.as_index()].definition.clone();
                let generated_name = {
                    let qualified_name_env = QualifiedNameEnv::new_from_module(output, others);
                    let readable_subscript_name = projection_key.map_or_else(
                        || {
                            qualified_name_env
                                .qualified_named_subscript_name(output.module_id(), subscript_name)
                        },
                        |key| qualified_name_env.qualified_projection_subscript_name(key),
                    );
                    qualified_name_env.disambiguated_subscript_member_name(
                        &readable_subscript_name,
                        member_function_kind,
                        &definition,
                        provenance,
                    )
                };
                output.name_function_with_visibility(
                    *id,
                    generated_name.into(),
                    Visibility::Module,
                );
                update_subscript_signature_from_member_definition(
                    output,
                    subscript_id,
                    projection_key.is_some(),
                    &definition,
                );
            }
        }

        // Sixth pass, run the borrow checker and elaborate into the final HIR arena.
        // A group that settled knows the effects of each of its references.
        let reference_effects = match &settlement {
            Some(settlement) => {
                let quantifier_counts = local_fns
                    .iter()
                    .map(|id| {
                        let scheme = &output.functions[id.as_index()].definition.ty_scheme;
                        scheme.eff_quantifiers.len()
                    })
                    .collect::<Vec<_>>();
                settlement.recorded_reference_effects(
                    &function_leading_effects,
                    &function_effect_substs,
                    &quantifier_counts,
                    &mut ty_inf,
                )
            }
            None => vec![FxHashMap::default(); local_fns.len()],
        };
        let mut module_inst_data = FxHashMap::default();
        for (((id, ty_origins), effect_origins), reference_effects) in local_fns
            .iter()
            .zip(function_ty_origins)
            .zip(function_effect_origins)
            .zip(reference_effects)
        {
            let descr = &output.functions[id.as_index()];
            let requirements = descr
                .definition
                .ty_scheme
                .extra_parameters(ModuleEnv::new(output, others));
            insert_inst_data_for_function_and_lambdas(
                &mut module_inst_data,
                &associated_lambdas,
                *id,
                LateFunctionInstData {
                    requirements,
                    ty_origins,
                    effect_origins,
                    effects_per_reference: settlement.is_some(),
                    reference_effects,
                },
            );
        }
        for id in local_fns.iter() {
            let dicts = &module_inst_data.get(id).unwrap().requirements;
            borrow_check_and_elaborate_dict(
                output,
                others,
                &mut pending_functions,
                &associated_lambdas,
                dicts,
                &module_inst_data,
                id,
                warnings,
            )?;
        }

        refresh_debug_info_for_functions(output, &associated_lambdas, &local_fns);
        Ok(Emitted::Functions)
    }
}

/// The bodies of `functions` and of their lambdas.
fn function_bodies<'a>(
    functions: &'a [LocalFunctionId],
    associated_lambdas: &'a FxHashMap<LocalFunctionId, Vec<LocalFunctionId>>,
    pending_functions: &'a PendingModuleFunctions,
) -> impl Iterator<Item = (&'a NodeArena, hir::NodeId)> + 'a {
    functions
        .iter()
        .flat_map(|id| function_and_associated_lambdas(id, associated_lambdas))
        .map(|id| {
            let pending = &pending_functions[&id];
            (&pending.code.arena, pending.code.entry_node_id)
        })
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

/// Recompute locality after inference/publication: an explicit parameter or a
/// signature-connected variable must never become eligible for orphan defaults.
fn function_defaulting_scope(
    ty_inf: &mut UnifiedTypeInference,
    fn_ty: &FnType,
    pending_function: Option<&PendingModuleFunction>,
    explicit_root_tys: &[Type],
) -> DefaultingScope {
    let fn_ty = ty_inf.substitute_in_fn_type(fn_ty);
    let mut sig_ty_vars = fn_ty.inner_ty_vars();
    sig_ty_vars.extend(
        explicit_root_tys
            .iter()
            .flat_map(|ty| ty_inf.substitute_in_type(*ty).inner_ty_vars().into_iter())
            .collect::<Vec<_>>(),
    );
    sig_ty_vars = sig_ty_vars.into_iter().unique().collect();
    ty_inf.normalize_remaining_constraints();
    let sig_boundary = ty_inf.constraint_boundary(sig_ty_vars.iter().copied());
    let orphan_constraints =
        sig_boundary.owned_inaccessible_constraints(ty_inf.remaining_constraints());
    // If the signature still exposes type variables, it defines the boundary for
    // defaulting and body-local `None`/unit evidence must not bias it.
    // Only functions with no remaining signature boundary can use their body root
    // to seed the narrow unit-constructor fallback.
    let unit_variant_seed_tys = if sig_ty_vars.is_empty() {
        pending_function
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
    DefaultingScope::from_constraints(&orphan_constraints)
        .with_unit_variant_seed_tys(unit_variant_seed_tys)
}

/// Reject functions whose published types combine two declared effect variables in one effect.
/// The effect variables that neither the generalized `signatures`, the given `observable` variables
/// nor a published constraint can observe take their least solution, so values inside a body keep
/// the effects they were built with.
fn minimize_body_effects(
    output: &Module,
    signatures: &[LocalFunctionId],
    mut observable: FxHashSet<EffectVar>,
    ty_inf: &mut UnifiedTypeInference,
) -> Result<(), InternalCompilationError> {
    for id in signatures {
        let fn_ty = &output.functions[id.as_index()].definition.ty_scheme.ty;
        observable.extend(ty_inf.substitute_in_fn_type(fn_ty).inner_effect_vars());
    }
    ty_inf.minimize_unobservable_effects(observable)
}

fn check_declared_effects_not_combined(
    output: &Module,
    associated_lambdas: &FxHashMap<LocalFunctionId, Vec<LocalFunctionId>>,
    local_fns: &[LocalFunctionId],
    ty_inf: &mut UnifiedTypeInference,
) -> Result<(), InternalCompilationError> {
    for id in local_fns {
        // The function is shown by its name, a lambda as a whole.
        let span = output.functions[id.as_index()]
            .spans
            .as_ref()
            .map(|spans| spans.name);
        for function_id in function_and_associated_lambdas(id, associated_lambdas) {
            let descr = &output.functions[function_id.as_index()];
            let span = if function_id == *id {
                span
            } else {
                descr.spans.as_ref().map(|spans| spans.span).or(span)
            }
            .unwrap_or_else(Location::new_synthesized);
            ty_inf.check_declared_effects_not_combined(&descr.definition.ty_scheme.ty, span)?;
        }
    }
    Ok(())
}

/// How to report a requirement that a default method needs and its trait lacks, if its type
/// variables are all parameters of the trait. Names go through `scheme`, the declaration that
/// `declared` instantiates, because its quantifiers follow their use in the method's signature.
fn missing_requirement(
    constraint: &PubTypeConstraint,
    trait_def: &Trait,
    scheme: &TypeScheme<FnType>,
    declared: &TypeScheme<FnType>,
    ty_inf: &mut UnifiedTypeInference,
    env: &ModuleEnv<'_>,
) -> Option<MissingRequirement> {
    let parameter_names = trait_def
        .input_type_names
        .iter()
        .chain(&trait_def.output_type_names)
        .collect::<Vec<_>>();
    let names = scheme
        .ty_quantifiers
        .iter()
        .zip(&declared.ty_quantifiers)
        .filter_map(|(source_var, var)| {
            let name = **parameter_names.get(source_var.name() as usize)?;
            let root = ty_inf.substitute_in_type(Type::variable(*var));
            let root = *root.data().as_variable()?;
            Some((root, name))
        })
        .collect::<FxHashMap<_, _>>();
    if constraint
        .inner_ty_vars()
        .iter()
        .any(|var| !names.contains_key(var))
    {
        return None;
    }
    let rendered = constraint
        .format_with(&TypeDisplayEnv::new(env, &names))
        .to_string();
    let is_where_clause = matches!(constraint, PubTypeConstraint::HaveTrait { .. })
        && constraint.inner_effect_vars().is_empty();
    Some(if is_where_clause {
        MissingRequirement::WhereClause(rendered)
    } else {
        MissingRequirement::Description(rendered)
    })
}
