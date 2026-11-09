// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::iter::once;

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
            InvalidAttributeKind, InvalidDefaultMethodKind, InvalidGenericParamsKind,
            InvalidSubscriptDefinitionKind, InvalidTraitDefinitionKind, MissingRequirement,
            SubscriptDefinitionSubject, UnsafeFeature, UnsupportedSubscriptFeatureKind,
        },
        lints::report_needless_returns_in_tail,
    },
    format::FormatWith,
    hir::{
        self, NodeArena,
        elaboration::elaborate_generated_functions,
        emit_hir::{
            ImplStubData, PendingModuleFunctions, PubTypeConstraintPtr,
            add_pending_function_anonymous, borrow_check_and_elaborate_dict, constraint_ptr,
            default_body_only_effects_in_function_descr, default_output_effects_in_functions,
            first_unbound_type_in_constraints, function_and_associated_lambdas,
            insert_inst_data_for_function_and_lambdas, instantiate_function_descr_in_place,
            is_compiler_provided_value_constraint, log_dropped_constraints_module,
            refresh_debug_info_for_functions, set_pending_function,
            substitute_and_canonicalize_functions,
        },
        function::{CallableDefinition, arg_conventions_for_args},
        hir_syn,
    },
    internal_compilation_error,
    module::{
        DictionaryEntryRequirements, FunctionId, GENERATED_LAMBDA_PREFIX, LocalDecl, LocalDeclId,
        LocalFunctionId, LocalSubscriptId, Module, ModuleEnv, ModuleFunction, ModuleFunctionSpans,
        PendingFunctionBody, PendingModuleFunction, ProjectionKey, QualifiedNameEnv,
        SubscriptMemberFunctionKind, SubscriptMemberKind, SubscriptSignature, TraitId, Visibility,
        YieldProvenance, id::Id,
    },
    std::core_traits_names::VALUE_TRAIT_NAME,
    types::{
        effects::{EffType, Effect, EffectVar, EffectsInstSubst},
        mutability::MutType,
        r#trait::{Trait, TraitDefaultMethod, TraitMethodIndex},
        trait_solver::{TraitSolver, trait_solver_from_module},
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
        type_mapper::{BitmapInstantiationMapper, TypeMapper},
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
    pub(crate) input_tys: Vec<Type>,
    pub(crate) output_tys: Vec<Type>,
    pub(crate) output_effs: Vec<EffType>,
    pub(crate) ty_var_count: u32,
    pub(crate) eff_var_count: u32,
    pub(crate) constraints: Vec<PubTypeConstraint>,
    pub(crate) functions: Vec<LocalFunctionId>,
    pub(crate) method_requirements: Vec<DictionaryEntryRequirements>,
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

/// The fixed signature of a function of a recursive group with written effect generics.
#[derive(Debug, Clone)]
pub(super) struct GroupContract {
    scheme: TypeScheme<FnType>,
    /// The number of written effect generics: the `i`-th is the contract's variable `i`.
    written_count: usize,
    /// The contract's variable for each written type generic.
    written_types: Vec<TypeVar>,
}

/// How [`emit_functions`] treats a group.
pub(super) enum GroupMode<'a> {
    Normal,
    /// Infer jointly with flexible written effect generics, and only produce contracts.
    Discover(&'a mut Vec<GroupContract>),
    /// Check the body at `index` against its fixed contract, in the slot reserved for it.
    Validate {
        /// The contracts of the whole group, in the order of its functions.
        contracts: &'a [GroupContract],
        /// The slot reserved for each function of the group.
        slots: &'a [LocalFunctionId],
        index: usize,
    },
}

impl GroupMode<'_> {
    /// In validation, the contract of the body being checked and its slot.
    fn validated(&self) -> Option<(&GroupContract, LocalFunctionId)> {
        match self {
            Self::Validate {
                contracts,
                slots,
                index,
            } => Some((&contracts[*index], slots[*index])),
            _ => None,
        }
    }

    fn is_validation(&self) -> bool {
        matches!(self, Self::Validate { .. })
    }
}

/// What joint inference of a group remembers about the declaration of one of its functions.
struct GroupFunctionDeclaration {
    /// The function's name, with its span.
    name: ast::UstrSpan,
    type_params: Vec<ast::UstrSpan>,
    effect_names: Vec<Ustr>,
    /// The parameters' names, with their spans.
    args: Vec<ast::UstrSpan>,
    /// The parameter index of the variable standing for each written effect generic.
    written_vars: FxHashMap<EffectVar, usize>,
    /// The parameter index of the marker tracking each written effect generic.
    written_markers: FxHashMap<EffectVar, usize>,
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

/// Calls `visit(row, written)` for every effect row of a signature, without changing it.
fn visit_signature(
    fn_ty: &FnType,
    ty_inf: &mut UnifiedTypeInference,
    written_vars: &FxHashMap<EffectVar, usize>,
    mut visit: impl FnMut(&mut UnifiedTypeInference, &EffType, bool),
) {
    walk_signature(fn_ty, ty_inf, written_vars, |ty_inf, row, is_written| {
        visit(ty_inf, row, is_written);
        row.clone()
    });
}

/// The inferred effect rows of a function's signature, each as the markers reaching it.
struct SignatureRows {
    /// The rows of arguments, result and constraints: variables here belong to the contract's type.
    in_type: Vec<FxHashSet<EffectVar>>,
    /// The parameter, with its span, that each leading row of `in_type` belongs to.
    params: Vec<ast::UstrSpan>,
    /// The function's performed effect, without the markers confined to it.
    performed: FxHashSet<EffectVar>,
}

fn marker_set(ty_inf: &mut UnifiedTypeInference, row: &EffType) -> FxHashSet<EffectVar> {
    ty_inf
        .effect_provenance(row)
        .inner_vars()
        .into_iter()
        .collect()
}

fn read_signature_rows(
    fn_ty: &FnType,
    declaration: &GroupFunctionDeclaration,
    constraints: &[PubTypeConstraint],
    ty_inf: &mut UnifiedTypeInference,
) -> SignatureRows {
    let written = &declaration.written_vars;
    let mut in_type = Vec::new();
    let mut params = Vec::new();
    for (arg, arg_name) in fn_ty.args.iter().zip(&declaration.args) {
        visit_signature(
            &FnType::new(vec![*arg], Type::unit(), EffType::empty()),
            ty_inf,
            written,
            |ty_inf, row, is_written| {
                if !is_written {
                    in_type.push(marker_set(ty_inf, row));
                    params.push(*arg_name);
                }
            },
        );
    }
    visit_signature(
        &FnType::new(vec![], fn_ty.ret, EffType::empty()),
        ty_inf,
        written,
        |ty_inf, row, is_written| {
            if !is_written {
                in_type.push(marker_set(ty_inf, row));
            }
        },
    );
    for constraint in constraints {
        let _ = constraint.map(&mut RowWalker {
            ty_inf,
            written_vars: written,
            in_solved: true,
            visit: |ty_inf: &mut UnifiedTypeInference, row: &EffType, _: bool| {
                in_type.push(marker_set(ty_inf, row));
                row.clone()
            },
        });
    }
    // Equal trait applications are one application, so their output effects are equal.
    for (index, constraint) in constraints.iter().enumerate() {
        let PubTypeConstraint::HaveTrait {
            trait_id,
            input_tys,
            output_effs,
            ..
        } = constraint
        else {
            continue;
        };
        for other in &constraints[index + 1..] {
            let PubTypeConstraint::HaveTrait {
                trait_id: other_trait_id,
                input_tys: other_input_tys,
                output_effs: other_output_effs,
                ..
            } = other
            else {
                continue;
            };
            if trait_id == other_trait_id && input_tys == other_input_tys {
                for (first, second) in output_effs.iter().zip(other_output_effs) {
                    let mut row = marker_set(ty_inf, first);
                    row.extend(marker_set(ty_inf, second));
                    in_type.push(row);
                }
            }
        }
    }
    let mut performed = marker_set(ty_inf, &fn_ty.effects);
    performed.retain(|marker| {
        declaration.written_markers.contains_key(marker)
            || in_type.iter().any(|row| row.contains(marker))
    });
    SignatureRows {
        in_type,
        params,
        performed,
    }
}

/// The one mapping from markers to the variables of a contract, used for all of its rows.
struct ContractTranslation<'a> {
    /// Markers sharing a row, with the variable that stands for them. A marker in none of them is
    /// confined to the function's performed effect, and is dropped.
    classes: Vec<(FxHashSet<EffectVar>, EffectVar)>,
    declaration: &'a GroupFunctionDeclaration,
}

impl<'a> ContractTranslation<'a> {
    /// Merge the markers that share a row, as a row holds one variable, and give each class its
    /// variable: the written generic in it, or else a fresh quantifier. A class cannot hold two.
    fn new(
        rows: &SignatureRows,
        declaration: &'a GroupFunctionDeclaration,
    ) -> Result<Self, InternalCompilationError> {
        let own = &declaration.written_markers;
        let mut classes: Vec<FxHashSet<EffectVar>> = Vec::new();
        for row in rows.in_type.iter().chain(once(&rows.performed)) {
            let mut merged = row.clone();
            let mut index = 0;
            while index < classes.len() {
                if classes[index].is_disjoint(&merged) {
                    index += 1;
                } else {
                    merged.extend(classes.swap_remove(index));
                }
            }
            if !merged.is_empty() {
                classes.push(merged);
            }
        }
        let mut next = own.len() as u32;
        let mut assigned = Vec::new();
        for class in classes {
            let mut own_params = class
                .iter()
                .filter_map(|marker| own.get(marker).copied())
                .sorted();
            let var = match (own_params.next(), own_params.next()) {
                (Some(first), Some(second)) => {
                    return Err(combined_generics_error(rows, declaration, first, second));
                }
                (Some(param), None) => EffectVar::new(param as u32),
                _ => {
                    next += 1;
                    EffectVar::new(next - 1)
                }
            };
            assigned.push((class, var));
        }
        Ok(Self {
            classes: assigned,
            declaration,
        })
    }

    /// Translate an inferred row.
    fn inferred_row(&self, ty_inf: &mut UnifiedTypeInference, row: &EffType) -> EffType {
        let atoms = ty_inf.effect_provenance(row);
        let mut result = atoms.primitive_effects();
        for marker in atoms.inner_vars() {
            if let Some((_, var)) = self
                .classes
                .iter()
                .find(|(class, _)| class.contains(&marker))
            {
                result.extend(&EffType::single_variable(*var));
            }
        }
        result
    }

    /// Translate a row of the signature, keeping a written one.
    fn signature_row(
        &self,
        ty_inf: &mut UnifiedTypeInference,
        row: &EffType,
        is_written: bool,
    ) -> EffType {
        if !is_written {
            return self.inferred_row(ty_inf, row);
        }
        let subst = self
            .declaration
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

    /// Translate a signature and its constraints into a type scheme.
    fn scheme(
        &self,
        fn_ty: &FnType,
        constraints: &[PubTypeConstraint],
        written_types: &[TypeVar],
        ty_inf: &mut UnifiedTypeInference,
    ) -> TypeScheme<FnType> {
        let written = &self.declaration.written_vars;
        let args = fn_ty
            .args
            .iter()
            .map(|arg| {
                walk_signature(
                    &FnType::new(vec![*arg], Type::unit(), EffType::empty()),
                    ty_inf,
                    written,
                    |ty_inf, row, is_written| self.signature_row(ty_inf, row, is_written),
                )
                .args[0]
            })
            .collect::<Vec<_>>();
        let ret = walk_signature(
            &FnType::new(vec![], fn_ty.ret, EffType::empty()),
            ty_inf,
            written,
            |ty_inf, row, is_written| self.signature_row(ty_inf, row, is_written),
        )
        .ret;
        let effects = self.inferred_row(ty_inf, &fn_ty.effects);
        let constraints = constraints
            .iter()
            .map(|constraint| {
                constraint.map(&mut RowWalker {
                    ty_inf,
                    written_vars: written,
                    in_solved: true,
                    visit: |ty_inf: &mut UnifiedTypeInference, row: &EffType, _: bool| {
                        self.inferred_row(ty_inf, row)
                    },
                })
            })
            .unique()
            .collect::<Vec<_>>();
        let mut ty = FnType::new(args, ret, effects);
        // As in publication, a variable only in the function's own effect stands for nothing.
        let mut retained = ty.input_effect_vars();
        constraints.fill_with_inner_effect_vars(&mut retained);
        let output_only = ty
            .effects
            .inner_vars()
            .into_iter()
            .filter(|var| !retained.contains(var))
            .collect::<Vec<_>>();
        ty.effects = ty
            .effects
            .difference(&EffType::multiple_variable(&output_only));
        // Quantifiers follow the order publication will give them, as calls record them by position.
        let ty_quantifiers = written_types
            .iter()
            .copied()
            .chain(TypeScheme::list_ty_vars(&ty, constraints.iter()))
            .unique()
            .collect();
        let eff_quantifiers = TypeScheme::<FnType>::list_eff_vars(&ty, constraints.iter());
        TypeScheme {
            ty_quantifiers,
            eff_quantifiers,
            ty,
            constraints,
        }
    }
}

/// The error for two written generics of a function meeting in one class.
fn combined_generics_error(
    rows: &SignatureRows,
    declaration: &GroupFunctionDeclaration,
    first: usize,
    second: usize,
) -> InternalCompilationError {
    let marker_of = |wanted: usize| {
        declaration
            .written_markers
            .iter()
            .find(|(_, param)| **param == wanted)
            .unwrap()
            .0
    };
    let (first_marker, second_marker) = (marker_of(first), marker_of(second));
    let first = declaration.effect_names[first];
    let second = declaration.effect_names[second];
    let shared_row = rows
        .in_type
        .iter()
        .position(|row| row.contains(first_marker) && row.contains(second_marker));
    let (function, function_span) = declaration.name;
    match shared_row {
        Some(row) => {
            let parameter = rows.params.get(row).copied();
            internal_compilation_error!(AmbiguousEffectInRecursiveGroup {
                function,
                parameter: parameter.map(|(name, _)| name),
                first,
                second,
                span: parameter.map_or(function_span, |(_, span)| span),
            })
        }
        None => internal_compilation_error!(EffectVariablesCombined {
            first,
            second,
            span: function_span,
        }),
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

/// Build the contracts of a group from the solution of its joint inference.
///
/// Written rows are kept. Any other row is read from the markers that reach it: a function's own
/// generics stay, and other markers become a quantifier, merged per row because a row holds at
/// most one variable. Markers confined to the function's performed effect are dropped.
fn build_group_contracts(
    fn_tys: &[FnType],
    declarations: &[GroupFunctionDeclaration],
    written_type_roots: &[Vec<Type>],
    ty_inf: &mut UnifiedTypeInference,
) -> Result<Vec<GroupContract>, InternalCompilationError> {
    ty_inf.normalize_remaining_constraints();
    let constraints = ty_inf.remaining_constraints().to_vec();
    for constraint in &constraints {
        for var in constraint.inner_effect_vars().into_iter().sorted() {
            ty_inf.seed_effect_marker(var);
        }
    }
    // Seed a marker for each inferred row of an argument or result, in every function first.
    for (fn_ty, declaration) in fn_tys.iter().zip(declarations) {
        let mut vars = Vec::new();
        visit_signature(
            &FnType::new(fn_ty.args.clone(), fn_ty.ret, EffType::empty()),
            ty_inf,
            &declaration.written_vars,
            |_, row, is_written| {
                if !is_written {
                    vars.extend(row.inner_vars());
                }
            },
        );
        for var in vars.into_iter().unique() {
            ty_inf.seed_effect_marker(var);
        }
    }

    let mut contracts = Vec::new();
    for ((fn_ty, declaration), roots) in fn_tys.iter().zip(declarations).zip(written_type_roots) {
        let resolved_roots = roots
            .iter()
            .map(|root| ty_inf.substitute_in_type(*root))
            .collect::<Vec<_>>();
        let written_types =
            distinct_written_type_vars(&declaration.type_params, resolved_roots, || {
                GenericParamsOwner::Function {
                    name: declaration.name.0,
                }
            })?;
        // The requirements on this function's type variables are part of its contract.
        let mut seed_ty_vars = ty_inf.substitute_in_fn_type(fn_ty).inner_ty_vars();
        seed_ty_vars.extend(written_types.iter().copied());
        let boundary = ConstraintBoundary::from_seed_ty_vars(seed_ty_vars);
        let related_constraints = boundary
            .accessible_constraints(&constraints)
            .into_iter()
            .filter(|constraint| !constraint.inner_ty_vars().is_empty())
            .cloned()
            .collect::<Vec<_>>();

        let rows = read_signature_rows(fn_ty, declaration, &related_constraints, ty_inf);
        let translation = ContractTranslation::new(&rows, declaration)?;
        let scheme = translation.scheme(fn_ty, &related_constraints, &written_types, ty_inf);
        contracts.push(GroupContract {
            scheme,
            written_count: declaration.written_markers.len(),
            written_types,
        });
    }
    Ok(contracts)
}

/// Whether a group gets contracts: it is recursive and writes an effect generic.
fn group_needs_contracts<'a, I: Iterator<Item = EmitFunctionInput<'a>>>(inputs: I) -> bool {
    let mut any = false;
    for input in inputs {
        if input.trait_default.is_some() || input.subscript.is_some() {
            return false;
        }
        any |= !input.function.generic_params.effect_params().is_empty();
    }
    any
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
    if recursive_function_names.is_empty() || !group_needs_contracts(ast_functions()) {
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
    let mut contracts = Vec::new();
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
        GroupMode::Discover(&mut contracts),
    )?;
    output.restore(checkpoint);
    warnings.truncate(warning_count);

    // Every function is visible through its contract before any body is checked.
    let mut ids = Vec::new();
    for (input, contract) in ast_functions().zip(&contracts) {
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
    // Each body has its own inference: what one assumes about a trait application says nothing
    // about another, whose generics are different.
    for index in 0..contracts.len() {
        let single = || ast_functions().skip(index).take(1);
        emit_functions(
            output,
            solver_arena,
            &single,
            desugared_arena,
            others,
            None,
            recursive_function_names,
            capabilities,
            warnings,
            GroupMode::Validate {
                contracts: &contracts,
                slots: &ids,
                index,
            },
        )
        .map_err(|error| {
            let helper = ast_functions().find_map(|input| {
                has_inferred_parameter(input.function).then_some(input.function.name.0)
            });
            let name_spans = ast_functions()
                .map(|input| (input.function.span, input.function.name.1))
                .collect::<Vec<_>>();
            explain_conflict_with_inferred_signature(error, helper, &name_spans)
        })?;
    }
    Ok(())
}

/// Whether a function of a group lets the group infer the type of a parameter, or part of it.
/// An annotation that is not concrete can be written generics, unless the function has none.
fn has_inferred_parameter(function: &ast::DModuleFunction) -> bool {
    let has_written_generics = !function.generic_params.effect_params().is_empty();
    function
        .args
        .iter()
        .any(|arg| match arg.locations_and_ty_concreteness().1 {
            None => true,
            Some((_, concrete)) => !concrete && !has_written_generics,
        })
}

/// An effect conflict while checking a body against the contracts can come from the coarse
/// contract of a function whose signature was inferred: say that it can be written instead.
/// A span covering a whole function of the group stands for its signature, so it becomes the
/// span of its name, as given by `name_spans`.
fn explain_conflict_with_inferred_signature(
    error: InternalCompilationError,
    helper: Option<Ustr>,
    name_spans: &[(Location, Location)],
) -> InternalCompilationError {
    let name_span = |span: Location| {
        name_spans
            .iter()
            .find_map(|(whole, name)| (*whole == span).then_some(*name))
            .unwrap_or(span)
    };
    match (error.into_inner(), helper) {
        (
            CompilationErrorImpl::InvalidEffectInclusion {
                source,
                source_span,
                target,
                target_span,
                names,
            },
            Some(function),
        ) => internal_compilation_error!(EffectConflictWithInferredSignature {
            function,
            source,
            source_span: name_span(source_span),
            target,
            target_span: name_span(target_span),
            names,
        }),
        (error, _) => InternalCompilationError::new(error),
    }
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
    Ok(result.expect("emitting a trait implementation produces its output"))
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
    mut mode: GroupMode<'_>,
) -> Result<Option<EmitTraitOutput>, InternalCompilationError>
where
    I: Iterator<Item = EmitFunctionInput<'a>>,
    F: Fn() -> I,
{
    // First pass, populate the function table and allocate fresh mono type variables.
    let mut ty_inf = TypeInference::default();
    let mut group_declarations = Vec::new();
    let mut body_tys: Vec<FnType> = Vec::new();
    let mut contract_instance = None;
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
            input_tys,
            output_tys,
            output_effs,
            ty_var_count: 0,
            eff_var_count: 0,
            constraints: vec![],
            functions: vec![],
            method_requirements: vec![],
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
            let mut written_markers = FxHashMap::default();
            for (index, (name, _)) in generic_params.effect_params().iter().enumerate() {
                let source_var = EffectVar::new((outer_annotation_eff_var_count + index) as u32);
                let eff = if matches!(mode, GroupMode::Discover(_)) {
                    let (eff, marker) = ty_inf.fresh_provisional_effect_var_ty(*name);
                    written_vars.insert(eff.to_single_variable().unwrap(), index);
                    written_markers.insert(marker, index);
                    eff
                } else {
                    ty_inf.fresh_rigid_effect_var_ty(Some(*name))
                };
                annotation_subst.1.insert(source_var, eff);
            }
            group_declarations.push(GroupFunctionDeclaration {
                name: *name,
                type_params: generic_params.type_params().to_vec(),
                effect_names: generic_params
                    .effect_params()
                    .iter()
                    .map(|(name, _)| *name)
                    .collect(),
                args: args.iter().map(|arg| arg.name).collect(),
                written_vars,
                written_markers,
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
        // A contract already holds the written requirements, as givens.
        if !mode.is_validation() {
            let mut mapper = BitmapInstantiationMapper::new(&annotation_subst);
            for constraint in where_clause {
                ty_inf.add_pub_constraint(constraint.map(&mut mapper));
            }
        }
        let attrs = validate_function_attributes(
            attributes,
            name.0,
            capabilities.allows_unsafe(output.module_id()),
        )?;
        let effects = ty_inf.fresh_effect_var_ty();
        let return_convention = kind.return_convention();
        let mut fn_type = FnType::new(args_ty, ret_ty_ty, effects.clone());
        if let GroupMode::Validate {
            contracts: group_contracts,
            slots: group_ids,
            index,
        } = &mode
        {
            let contract = &group_contracts[*index];
            // The body is checked against the contract with its quantifiers rigid.
            let mut ty_subst = TypeInstSubst::default();
            for (root, var) in explicit_root_tys.iter().zip(&contract.written_types) {
                ty_subst.insert(*var, *root);
            }
            for var in &contract.scheme.ty_quantifiers {
                ty_subst
                    .entry(*var)
                    .or_insert_with(|| ty_inf.fresh_type_var_ty());
            }
            // Contracts share the variables of joint inference, which has one type instance per
            // group: calls in this body take the same instance, whichever function they call.
            let mut instance_of = ty_subst.clone();
            let instances = group_contracts
                .iter()
                .zip(group_ids.iter())
                .map(|(callee, callee_id)| {
                    let tys = callee
                        .scheme
                        .ty_quantifiers
                        .iter()
                        .map(|var| {
                            *instance_of
                                .entry(*var)
                                .or_insert_with(|| ty_inf.fresh_type_var_ty())
                        })
                        .collect();
                    (FunctionId::new(output.module_id(), *callee_id), tys)
                })
                .collect();
            ty_inf.set_group_type_instances(instances);
            let mut eff_subst = EffectsInstSubst::default();
            for param in 0..contract.written_count {
                let source_var = EffectVar::new((outer_annotation_eff_var_count + param) as u32);
                eff_subst.insert(
                    EffectVar::new(param as u32),
                    annotation_subst.1[&source_var].clone(),
                );
            }
            for var in contract.scheme.eff_quantifiers.iter().sorted() {
                eff_subst
                    .entry(*var)
                    .or_insert_with(|| ty_inf.fresh_rigid_effect_var_ty(None));
            }
            let instance_ty_vars = contract
                .scheme
                .ty_quantifiers
                .iter()
                .map(|var| *ty_subst[var].data().as_variable().unwrap())
                .collect::<Vec<_>>();
            let instance_eff_vars = contract
                .scheme
                .eff_quantifiers
                .iter()
                .map(|var| eff_subst[var].to_single_variable().unwrap())
                .collect();
            let subst = (ty_subst, eff_subst);
            let mut mapper = BitmapInstantiationMapper::new(&subst);
            fn_type = contract.scheme.ty.map(&mut mapper);
            let constraints = contract
                .scheme
                .constraints
                .iter()
                .map(|constraint| constraint.map(&mut mapper))
                .collect();
            body_tys.push(fn_type.clone());
            contract_instance = Some(TypeScheme {
                ty_quantifiers: instance_ty_vars,
                eff_quantifiers: instance_eff_vars,
                ty: fn_type.clone(),
                constraints,
            });
        }

        let declared_signature = contract_instance
            .take()
            .map(Ok)
            .or_else(|| {
                input.trait_default.map(|(trait_id, index)| {
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
                    ty_inf.add_declared_generics(
                        scheme.ty_quantifiers.iter().map(|var| subst.0[var]),
                    );
                    Ok::<_, InternalCompilationError>(scheme.instantiate_simple(&subst))
                })
            })
            .transpose()?;
        if mode.is_validation()
            && let Some(declared) = &declared_signature
        {
            ty_inf.add_declared_generics(
                declared
                    .ty_quantifiers
                    .iter()
                    .map(|var| Type::variable(*var)),
            );
        }
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
        let ty_scheme = if let Some((contract, _)) = mode.validated() {
            contract.scheme.clone()
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
        let id = if let Some((_, id)) = mode.validated() {
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
        function_attrs.push(attrs);
        function_kinds.push(kind);
        subscript_attachments.push(input.subscript_attachments.to_vec());
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
        if let Some((contract, _)) = mode.validated() {
            // Calls in this body, to itself, still instantiate the contract.
            output.functions[id.as_index()].definition.ty_scheme = contract.scheme.clone();
        }
        output.deps.extend(new_deps);
        ty_inf.own_constraints_since(constraint_scope, *id);
    }
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

        // Take final substituted constraints.
        ty_inf.normalize_remaining_constraints();
        let all_constraints = ty_inf.take_constraints();

        // Validate that each method's effects are a subset of the trait definition's effects,
        // and override them with the trait's effects.
        // This ensures ABI consistency: the calling convention is determined by the trait definition.
        let trait_ctx = trait_ctx.unwrap();
        let trait_id = trait_ctx.trait_id;
        let trait_def = &trait_ctx.trait_def;
        let resolved_roots = (0..trait_ctx.generic_type_params.len())
            .map(|index| {
                impl_annotation_subst
                    .as_ref()
                    .and_then(|(subst, _)| subst.get(&TypeVar::new(index as u32)))
                    .map(|ty| ty_inf.substitute_in_type(*ty))
                    .expect("a written impl generic has a type variable")
            })
            .collect::<Vec<_>>();
        distinct_written_type_vars(trait_ctx.generic_type_params, resolved_roots, || {
            GenericParamsOwner::TraitImpl {
                trait_name: trait_def.name,
            }
        })?;
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
            insert_inst_data_for_function_and_lambdas(
                &mut module_inst_data,
                &associated_lambdas,
                output,
                *id,
                dicts.clone(),
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
        Ok(Some(trait_output))
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

        if let GroupMode::Discover(contracts) = &mut mode {
            // A return that only diverges becomes `never` here, where the whole group is seen:
            // validation checks one body, and must keep its contract as it is.
            for (id, ret_var) in unconstrained_diverging_returns(
                output,
                &mut ty_inf,
                ast_functions(),
                &local_fns,
                &function_explicit_root_tys,
                &recursive_function_ids,
                &pending_functions,
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
            **contracts = build_group_contracts(
                &fn_tys,
                &group_declarations,
                &function_explicit_root_tys,
                &mut ty_inf,
            )?;
            return Ok(None);
        }

        minimize_body_effects(output, &local_fns, FxHashSet::default(), &mut ty_inf)?;
        ty_inf.finalize_effects()?;

        // Substitute everything using ty_inf (single pass, includes all defaults).
        substitute_and_canonicalize_functions(
            output,
            &mut pending_functions,
            &associated_lambdas,
            &local_fns,
            &mut ty_inf,
        );
        check_declared_effects_not_combined(output, &associated_lambdas, &local_fns, &mut ty_inf)?;

        // Recursive-return defaulting inspects the final constraints. A contract already says
        // what its function returns.
        ty_inf.normalize_remaining_constraints();
        if !mode.is_validation() {
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
        // Take final substituted constraints.
        let all_constraints = ty_inf.take_constraints();

        // For each function: filter constraints, check unbounds, finalize type scheme.
        let mut used_constraints: FxHashSet<PubTypeConstraintPtr> = FxHashSet::default();
        for (((input, id), explicit_root_tys), declared) in ast_functions()
            .zip(local_fns.iter())
            .zip(function_explicit_root_tys.iter())
            .zip(&declared_signatures)
        {
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
            let generated = solver.finish().commit(
                &mut output.functions,
                &mut output.def_table,
                &mut pending_functions,
            );
            elaborate_generated_functions(output, others, &mut pending_functions, generated)?;

            let mut constraints = constraints;
            if let Some(declared) = declared {
                let checked_constraints = constraints.iter().filter(|constraint| {
                    !is_compiler_provided_value_constraint(
                        constraint,
                        ModuleEnv::new(output, others),
                    )
                });
                let checked = check_declared_signature(declared, checked_constraints, &mut ty_inf);
                if let (Err((reason, _)), None) = (&checked, input.trait_default) {
                    return Err(internal_compilation_error!(RecursiveGroupBodyDoesNotFit {
                        function: function.name.0,
                        reason: *reason,
                        span: function.name.1,
                    }));
                }
                if let Err((reason, missing)) = checked {
                    let (trait_id, index) = input.trait_default.unwrap();
                    let trait_def = output.trait_def(trait_id);
                    let missing_constraint = missing.and_then(|constraint| {
                        let env = ModuleEnv::new(output, others);
                        let scheme = trait_def
                            .default_method_scheme(trait_id, index, env, function.span)
                            .ok()?;
                        missing_requirement(
                            &constraint,
                            trait_def,
                            &scheme,
                            declared,
                            &mut ty_inf,
                            &env,
                        )
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
                if input.trait_default.is_none() {
                    // Calls in the group recorded the contract's requirements, in their order,
                    // so a body needing any other one cannot be published.
                    let contract_constraints = declared
                        .constraints
                        .iter()
                        .map(|constraint| ty_inf.substitute_in_constraint(constraint))
                        .collect::<Vec<_>>();
                    if constraints
                        .iter()
                        .any(|constraint| !contract_constraints.contains(constraint))
                    {
                        return Err(internal_compilation_error!(RecursiveGroupBodyDoesNotFit {
                            function: function.name.0,
                            reason: InvalidDefaultMethodKind::UndeclaredConstraint,
                            span: function.name.1,
                        }));
                    }
                    constraints.clear();
                }
                constraints.extend(
                    declared
                        .constraints
                        .iter()
                        .map(|constraint| ty_inf.substitute_in_constraint(constraint)),
                );
                constraints = constraints.into_iter().unique().collect();
                let declared_ty = ty_inf.substitute_in_fn_type(&declared.ty);
                output.functions[id.as_index()].definition.ty_scheme.ty = declared_ty;
                // Calls in the group recorded the contract's quantifiers, in their order.
                if mode.is_validation() {
                    quantifiers = declared
                        .ty_quantifiers
                        .iter()
                        .map(|var| {
                            *ty_inf
                                .substitute_in_type(Type::variable(*var))
                                .data()
                                .as_variable()
                                .expect("a contract quantifier stays a variable")
                        })
                        .collect();
                }
            }

            // Write the final type scheme.
            let explicit_ty_vars = explicit_ty_vars
                .iter()
                .copied()
                .unique()
                .collect::<Vec<_>>();
            if !mode.is_validation() {
                quantifiers = explicit_ty_vars
                    .iter()
                    .copied()
                    .chain(
                        quantifiers
                            .into_iter()
                            .filter(|ty_var| !explicit_ty_vars.contains(ty_var)),
                    )
                    .collect();
            }
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
                descr.definition.generic_params = function.generic_params.type_params().to_vec();
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
        for (input, id) in ast_functions().zip(local_fns.iter()) {
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
                output,
                *id,
                dicts,
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
        let span = output.functions[id.as_index()]
            .spans
            .as_ref()
            .map(|spans| spans.span);
        for function_id in function_and_associated_lambdas(id, associated_lambdas) {
            let descr = &output.functions[function_id.as_index()];
            let span = descr
                .spans
                .as_ref()
                .map(|spans| spans.span)
                .or(span)
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
