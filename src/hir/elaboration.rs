// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use ustr::{Ustr, ustr};

use crate::{
    FxHashMap, FxHashSet, Location, Modules,
    ast::Path,
    compiler::{diagnostics::CompilationWarning, error::InternalCompilationError},
    hir::{
        borrow_checker::BorrowContext,
        dictionary::{
            DictElaborationCtx, DictionaryReq, EvidenceBindingSource, LateFunctionInstData,
            StaticEvidence, find_projection_subscript_dict_index,
            find_projection_subscript_dict_index_for_receiver_ty, find_trait_impl_dict_index,
            find_variant_payload_indirection_index, instantiate_dictionary_requirements,
        },
        hir_syn::{call_dictionary_function, get_dictionary},
        value_dispatch::{resolve_local_clone, resolve_local_drop},
    },
    internal_compilation_error,
    module::{
        ELocalDecl, EvidenceBindingId, FunctionId, GeneratedStructuralProjectionSpec, LocalDecl,
        LocalDeclId, LocalFunctionId, Module, ModuleEnv, ModuleId,
        PendingGeneratedStructuralProjectionSubscripts, PendingLocalClone, PendingLocalDrop,
        PendingModuleFunction, PendingTakeLocalValueMode, ProjectionIndex, ProjectionKey,
        ResolvedLocalClone, ResolvedLocalDrop, ResolvedTakeLocalValueMode, SubscriptId,
        SubscriptMemberKind, TraitDictionaryId, TraitId,
        generated_structural_projection_definition, id::Id,
    },
    std::core_traits_names::VALUE_TRAIT_NAME,
    types::{
        effects::EffectVar,
        r#trait::{Trait, TraitDictionaryEntryIndex, TraitMethodIndex},
        trait_solver::{
            EvidencePlanSource, REDUCTION_WORK_LIMIT, TraitSolver, trait_solver_from_module,
        },
    },
};

struct ElaborationEffectDefaultMapper<'a> {
    retained: &'a FxHashSet<EffectVar>,
}

impl TypeMapper for ElaborationEffectDefaultMapper<'_> {
    fn map_type(&mut self, ty: Type) -> Type {
        ty
    }

    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
        mut_ty
    }

    fn map_effect_type(&mut self, effects: &EffType) -> EffType {
        effects
            .iter()
            .filter(|effect| match effect {
                Effect::Variable(variable) => self.retained.contains(variable),
                Effect::Primitive(_) => true,
            })
            .collect()
    }
}

fn default_unquantified_trait_application_effects(
    input_tys: &[Type],
    output_tys: &[Type],
    output_effs: &[EffType],
    retained: &FxHashSet<EffectVar>,
) -> (Vec<Type>, Vec<Type>, Vec<EffType>) {
    let mut mapper = ElaborationEffectDefaultMapper { retained };
    (
        input_tys.iter().map(|ty| ty.map(&mut mapper)).collect(),
        output_tys.iter().map(|ty| ty.map(&mut mapper)).collect(),
        output_effs
            .iter()
            .map(|effects| mapper.map_effect_type(effects))
            .collect(),
    )
}

use itertools::{Itertools, process_results};

use crate::{
    containers::{SVec2, b},
    hir::{
        self, ArgConvention, CallArgument, ENodeArena, ENodeId, Elaborated, LoopId, Node,
        NodeArena, NodeKind, Project as HirProject, StaticApplication, UNodeArena, UNodeId,
        Unelaborated, VariantPayloadStorageSource, elaborated_node_is_place_reference,
        emit_value_impl::function_value_method, value::LiteralValue,
    },
    std::value::{
        dynamic_product_member_layouts, generated_value_evidence_types,
        is_function_surface_only_value_trait_application, is_value_trait,
        is_value_trait_for_function_type, type_has_static_layout,
        value_layout_associated_const_values, variant_payload_storage_for_type,
    },
    types::{
        effects::{EffType, Effect, EffectsInstSubst, no_effects},
        mutability::MutType,
        trait_solver::alpha_canonicalize_types_with_instantiation,
        r#type::{
            CallImplType, CallResultConvention, FnArgType, FnType, SubscriptMemberType,
            SubscriptType, Type, TypeKind, TypeVar,
        },
        type_inference::substitution::InstSubst,
        type_like::TypeLike,
        type_mapper::{BitmapInstantiationMapper, TypeMapper},
        type_scheme::extra_parameters_from_constraints_with,
    },
};

/// Build the use-site HIR expression for a generated `Value` dictionary.
fn value_dictionary_node_kind_from_methods(
    trait_id: TraitId,
    input_tys: &[Type],
    span: Location,
    methods: Vec<LocalFunctionId>,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<(NodeKind, Type), InternalCompilationError> {
    let (dictionary, ty) = ctx
        .trait_solver
        .materialize_generated_value_impl_from_methods(trait_id, input_tys, span, methods)?;
    Ok((get_dictionary(dictionary), ty))
}

/// Build the compiler-provided `Value` dictionary for a concrete function type.
fn function_value_dictionary_node_kind(
    trait_id: TraitId,
    input_tys: &[Type],
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<(NodeKind, Type), InternalCompilationError> {
    let method_count = ctx.trait_solver.trait_def(trait_id).methods.len();
    let methods = (0..method_count)
        .map(TraitMethodIndex::from_index)
        .map(|method_index| function_value_method(ctx.trait_solver, method_index, span))
        .collect::<Result<Vec<_>, _>>()?;
    value_dictionary_node_kind_from_methods(trait_id, input_tys, span, methods, ctx)
}

/// Build the HIR expression that provides the runtime dictionary for a trait requirement.
#[allow(clippy::too_many_arguments)]
fn trait_dictionary_node_kind(
    arena: &mut NodeArena,
    trait_id: TraitId,
    input_tys: &[Type],
    output_tys: &[Type],
    output_effs: &[EffType],
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<(NodeKind, Type), InternalCompilationError> {
    let trait_def = ctx.trait_solver.trait_def(trait_id);
    if let Some(index) = find_trait_impl_dict_index(ctx.dicts, trait_id, input_tys) {
        let ty = ctx.dicts.requirements[index].to_dict_type(ctx.trait_solver);
        return Ok((
            NodeKind::LoadDictionary(hir::LoadDictionary {
                extra_parameter: EvidenceBindingId::from_index(index),
            }),
            ty,
        ));
    }

    let (input_tys, output_tys, output_effs) = default_unquantified_trait_application_effects(
        input_tys,
        output_tys,
        output_effs,
        &ctx.retained_effect_vars,
    );
    if is_value_trait_for_function_type(trait_id, trait_def, &input_tys, &output_tys) {
        return function_value_dictionary_node_kind(trait_id, &input_tys, span, ctx);
    }

    if is_value_trait(trait_id, trait_def)
        && input_tys.len() == 1
        && output_tys.is_empty()
        && generated_value_evidence_types(input_tys[0], ctx.trait_solver).is_some()
    {
        let binding = trait_dictionary_evidence_binding(
            arena,
            trait_id,
            &input_tys,
            &output_tys,
            &[],
            span,
            ctx,
        )?;
        let ty = ctx
            .trait_solver
            .trait_def(trait_id)
            .get_dictionary_type_for_tys(&input_tys, &output_tys, &[]);
        return Ok((
            NodeKind::LoadDictionary(hir::LoadDictionary {
                extra_parameter: binding,
            }),
            ty,
        ));
    }

    if !input_tys.iter().all(|ty| ty.is_trait_input_resolved())
        || recorded_evidence_root(trait_id, &input_tys, &output_tys, &output_effs, ctx).is_some()
    {
        let binding = trait_dictionary_evidence_binding(
            arena,
            trait_id,
            &input_tys,
            &output_tys,
            &output_effs,
            span,
            ctx,
        )?;
        let ty = ctx.evidence_bindings[binding.as_index()]
            .requirement
            .to_dict_type(ctx.trait_solver);
        return Ok((
            NodeKind::LoadDictionary(hir::LoadDictionary {
                extra_parameter: binding,
            }),
            ty,
        ));
    }
    let dictionary = ctx.trait_solver.solve_impl_for_application(
        trait_id,
        &input_tys,
        &output_tys,
        &output_effs,
        &ctx.retained_effect_vars,
        span,
        arena,
    )?;
    let impl_data = ctx.trait_solver.get_impl_data_by_id(dictionary);
    let ty = impl_data.dictionary_ty;
    let capture_schema = impl_data.dictionary_value.capture_schema().to_vec();
    let capture_infos = extra_arg_kind_from_inst_data(
        &hir::FnInstData::new(capture_schema, Vec::new(), Vec::new()),
        span,
        ctx,
        arena,
    );
    let capture_infos = capture_infos?;
    let captures = capture_infos
        .into_iter()
        .map(|(kind, ty, _)| arena.alloc(Node::new(kind, ty, no_effects(), span)))
        .collect();
    Ok((
        NodeKind::GetDictionary(hir::GetDictionary {
            dictionary,
            captures,
        }),
        ty,
    ))
}

/// Resolve and intern complete evidence for a selected trait application.
pub(crate) fn trait_dictionary_evidence_binding(
    arena: &mut NodeArena,
    trait_id: TraitId,
    input_tys: &[Type],
    output_tys: &[Type],
    output_effs: &[EffType],
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<EvidenceBindingId, InternalCompilationError> {
    let requirement = DictionaryReq::new_trait_impl(
        trait_id,
        input_tys.to_vec(),
        output_tys.to_vec(),
        output_effs.to_vec(),
    );
    if ctx.active_dictionary_constructions.len() >= REDUCTION_WORK_LIMIT
        || ctx.active_dictionary_constructions.contains(&requirement)
    {
        return Err(internal_compilation_error!(TraitImplNotFound {
            trait_ref: trait_id,
            input_tys: input_tys.to_vec(),
            fn_span: span,
        }));
    }
    ctx.active_dictionary_constructions.push(requirement);
    let result = trait_dictionary_evidence_binding_inner(
        arena,
        trait_id,
        input_tys,
        output_tys,
        output_effs,
        span,
        ctx,
    );
    ctx.active_dictionary_constructions.pop();
    result
}

/// Realize a definition-site choice. In particular, a selected node never asks the solver
/// which impl applies again. Public leaves are bound only after parameter order is final.
fn replay_evidence_plan(
    arena: &mut NodeArena,
    root: usize,
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<EvidenceBindingId, InternalCompilationError> {
    enum Work {
        Visit(usize),
        Construct {
            node: usize,
            requirement: DictionaryReq,
            definition: TraitDictionaryId,
            captures: Vec<usize>,
        },
    }
    let mut pending = vec![Work::Visit(root)];
    while let Some(work) = pending.pop() {
        match work {
            Work::Construct {
                node,
                requirement,
                definition,
                captures,
            } => {
                let captures = captures
                    .into_iter()
                    .map(|id| ctx.planned_bindings[id].expect("capture was elaborated first"))
                    .collect();
                ctx.planned_bindings[node] = Some(ctx.intern_evidence_binding(
                    requirement,
                    EvidenceBindingSource::ConstructedDictionary {
                        definition,
                        captures,
                    },
                ));
            }
            Work::Visit(index) => {
                if ctx.planned_bindings[index].is_some() {
                    continue;
                }
                let node = &ctx.evidence_plan.nodes[index];
                let value_trait = ctx.trait_solver.std_trait_id(VALUE_TRAIT_NAME);
                let requirement = node
                    .constraint
                    .dictionary_requirement_key(value_trait)
                    .expect("evidence plan nodes have a dictionary requirement");
                let (selected, captures) = match &node.source {
                    EvidencePlanSource::Public => {
                        ctx.planned_bindings[index] = Some(evidence_binding_for_requirement(
                            arena,
                            &requirement,
                            span,
                            ctx,
                        )?);
                        continue;
                    }
                    EvidencePlanSource::SelfReference { .. } => {
                        return Err(internal_compilation_error!(Internal {
                            error: "Recursive Value evidence escaped its dictionary entry".into(),
                            span,
                        }));
                    }
                    EvidencePlanSource::Pending => {
                        return Err(internal_compilation_error!(Internal {
                            error: "An unresolved evidence plan reached elaboration".into(),
                            span,
                        }));
                    }
                    EvidencePlanSource::Structural { members } => {
                        // The members are what the answer requires, to check and to publish.
                        // Its evidence takes those that it captures only: a marker trait, for
                        // one, has no evidence to give.
                        let members = members.clone();
                        ctx.planned_bindings[index] = Some(structural_evidence_binding(
                            arena,
                            &requirement,
                            &members,
                            span,
                            ctx,
                        )?);
                        continue;
                    }
                    EvidencePlanSource::Selected {
                        application,
                        captures,
                    } => {
                        let selected = ctx.trait_solver.materialize_uniform_dictionary(
                            application,
                            &requirement,
                            span,
                        )?;
                        (selected, captures.clone())
                    }
                    EvidencePlanSource::GeneratedValue { members } => {
                        if let Some((entry_plan, original_ids)) =
                            ctx.evidence_plan.recursive_entry_plan(index)
                        {
                            let selected =
                                ctx.trait_solver.materialize_recursive_value_dictionary(
                                    &requirement,
                                    &entry_plan,
                                    span,
                                    arena,
                                )?;
                            let schema = ctx
                                .trait_solver
                                .get_impl_data_by_id(selected)
                                .dictionary_value
                                .capture_schema();
                            let captures = schema
                                .iter()
                                .map(|capture| {
                                    let original = entry_plan.nodes.iter().zip(&original_ids)
                                        .find_map(|(node, original)| {
                                            let requirement = node.constraint.dictionary_requirement_key(value_trait)?;
                                            (matches!(node.source, EvidencePlanSource::Public)
                                                && requirement.same_contract(capture)).then_some(*original)
                                        });
                                    original.ok_or_else(|| internal_compilation_error!(Internal {
                                        error: "Recursive Value capture is absent from its entry plan".into(),
                                        span,
                                    }))
                                })
                                .collect::<Result<Vec<_>, _>>()?;
                            (selected, captures)
                        } else {
                            let DictionaryReq::TraitImpl {
                                trait_id,
                                input_tys,
                                ..
                            } = &requirement
                            else {
                                unreachable!()
                            };
                            let (canonical, instantiation) =
                                alpha_canonicalize_types_with_instantiation(input_tys);
                            let (selected, _) = ctx
                                .trait_solver
                                .materialize_compiler_provided_value_dictionary(
                                    arena, *trait_id, &canonical, span,
                                )?;
                            let mut mapper = BitmapInstantiationMapper::new(&instantiation);
                            let captures = ctx
                                .trait_solver
                                .get_impl_data_by_id(selected)
                                .dictionary_value
                                .capture_schema()
                                .iter()
                                .map(|req| req.instantiate(&mut mapper))
                                .map(|capture| {
                                    let member = members.iter().copied()
                                        .filter(|member| *member != index)
                                        .find(|member| {
                                            let requirement = ctx.evidence_plan.nodes[*member]
                                                .constraint.dictionary_requirement_key(value_trait);
                                            requirement.as_ref() == Some(&capture)
                                        });
                                    member.ok_or_else(|| internal_compilation_error!(Internal {
                                        error: "Generated Value evidence differs from its recorded members".into(),
                                        span,
                                    }))
                                })
                                .collect::<Result<Vec<_>, _>>()?;
                            (selected, captures)
                        }
                    }
                    EvidencePlanSource::Ground(selected) => {
                        let selected = *selected;
                        let schema = ctx
                            .trait_solver
                            .get_impl_data_by_id(selected)
                            .dictionary_value
                            .capture_schema()
                            .to_vec();
                        let captures = schema
                            .iter()
                            .map(|req| evidence_binding_for_requirement(arena, req, span, ctx))
                            .collect::<Result<Vec<_>, _>>()?;
                        ctx.planned_bindings[index] = Some(ctx.intern_evidence_binding(
                            requirement,
                            EvidenceBindingSource::ConstructedDictionary {
                                definition: TraitDictionaryId::new(
                                    selected.module,
                                    selected.impl_id,
                                ),
                                captures,
                            },
                        ));
                        continue;
                    }
                };
                let construction = pending.len();
                let capture_count = captures.len();
                pending.push(Work::Construct {
                    node: index,
                    requirement,
                    definition: TraitDictionaryId::new(selected.module, selected.impl_id),
                    captures,
                });
                // Read from the queued construction to avoid a second vector of child visits.
                // Reverse pushes preserve the capture order on this LIFO worklist.
                for child in (0..capture_count).rev() {
                    let Work::Construct { captures, .. } = &pending[construction] else {
                        unreachable!("the construction stays queued below its children");
                    };
                    let child = captures[child];
                    pending.push(Work::Visit(child));
                }
            }
        }
    }
    Ok(ctx.planned_bindings[root].expect("the plan root was elaborated"))
}

// Body requests use complete contracts at the boundary of the plan. Only original roots
// participate: prerequisite captures follow their own recorded edges, never sibling searches.
fn recorded_evidence_root(
    trait_id: TraitId,
    input_tys: &[Type],
    output_tys: &[Type],
    output_effs: &[EffType],
    ctx: &DictElaborationCtx<'_, '_, '_>,
) -> Option<usize> {
    let requested = DictionaryReq::new_trait_impl(
        trait_id,
        input_tys.to_vec(),
        output_tys.to_vec(),
        output_effs.to_vec(),
    );
    ctx.evidence_plan.roots.iter().copied().find(|index| {
        let node = &ctx.evidence_plan.nodes[*index];
        !matches!(node.source, EvidencePlanSource::Public)
            && node
                .constraint
                .dictionary_requirement_key(ctx.trait_solver.std_trait_id(VALUE_TRAIT_NAME))
                .is_some_and(|planned| planned.same_contract(&requested))
    })
}

fn trait_dictionary_evidence_binding_inner(
    arena: &mut NodeArena,
    trait_id: TraitId,
    input_tys: &[Type],
    output_tys: &[Type],
    output_effs: &[EffType],
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<EvidenceBindingId, InternalCompilationError> {
    if let Some(index) = find_trait_impl_dict_index(ctx.dicts, trait_id, input_tys) {
        return Ok(EvidenceBindingId::from_index(index));
    }
    let (input_tys, output_tys, output_effs) = default_unquantified_trait_application_effects(
        input_tys,
        output_tys,
        output_effs,
        &ctx.retained_effect_vars,
    );
    if let Some(index) =
        recorded_evidence_root(trait_id, &input_tys, &output_tys, &output_effs, ctx)
    {
        return replay_evidence_plan(arena, index, span, ctx);
    }
    let is_open_generated_value = {
        let trait_def = ctx.trait_solver.trait_def(trait_id);
        is_value_trait(trait_id, trait_def)
            && input_tys.len() == 1
            && output_tys.is_empty()
            && generated_value_evidence_types(input_tys[0], ctx.trait_solver).is_some()
    };
    if is_open_generated_value {
        let (canonical_input_tys, instantiation) =
            alpha_canonicalize_types_with_instantiation(&input_tys);
        let (selected, _) = ctx
            .trait_solver
            .materialize_compiler_provided_value_dictionary(
                arena,
                trait_id,
                &canonical_input_tys,
                span,
            )?;
        let definition = TraitDictionaryId::new(selected.module, selected.impl_id);
        let mut mapper = BitmapInstantiationMapper::new(&instantiation);
        let capture_schema = ctx
            .trait_solver
            .get_impl_data_by_id(selected)
            .dictionary_value
            .capture_schema()
            .iter()
            .map(|requirement| requirement.instantiate(&mut mapper))
            .collect::<Vec<_>>();
        let mut captures = Vec::with_capacity(capture_schema.len());
        for requirement in &capture_schema {
            captures.push(evidence_binding_for_requirement(
                arena,
                requirement,
                span,
                ctx,
            )?);
        }
        let requirement =
            DictionaryReq::new_trait_impl(trait_id, input_tys, output_tys, output_effs);
        let source = EvidenceBindingSource::ConstructedDictionary {
            definition,
            captures,
        };
        return Ok(ctx.intern_evidence_binding(requirement, source));
    }
    if !input_tys.iter().all(|ty| ty.is_trait_input_resolved()) {
        return Err(internal_compilation_error!(TraitImplNotFound {
            trait_ref: trait_id,
            input_tys,
            fn_span: span,
        }));
    }

    let selected = ctx.trait_solver.solve_impl_for_application(
        trait_id,
        &input_tys,
        &output_tys,
        &output_effs,
        &ctx.retained_effect_vars,
        span,
        arena,
    )?;
    let definition = TraitDictionaryId::new(selected.module, selected.impl_id);
    let impl_data = ctx.trait_solver.get_impl_data_by_id(selected);
    let capture_schema = impl_data.dictionary_value.capture_schema().to_vec();
    let captures = capture_schema
        .iter()
        .map(|requirement| evidence_binding_for_requirement(arena, requirement, span, ctx))
        .collect::<Result<Vec<_>, _>>();
    let captures = captures?;
    let requirement = DictionaryReq::new_trait_impl(trait_id, input_tys, output_tys, output_effs);
    let static_captures = captures
        .iter()
        .map(|capture| ctx.static_evidence(*capture))
        .collect::<Option<Vec<_>>>();
    let source = if let Some(captures) = static_captures {
        let evidence = if captures.is_empty() {
            StaticEvidence::bare_dictionary(definition)
        } else {
            StaticEvidence::Dictionary {
                definition,
                captures: captures.into_boxed_slice(),
            }
        };
        EvidenceBindingSource::Static(evidence)
    } else {
        EvidenceBindingSource::ConstructedDictionary {
            definition,
            captures,
        }
    };
    Ok(ctx.intern_evidence_binding(requirement, source))
}

fn evidence_binding_for_requirement(
    arena: &mut NodeArena,
    requirement: &DictionaryReq,
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<EvidenceBindingId, InternalCompilationError> {
    if let Some(index) = ctx
        .dicts
        .requirements
        .iter()
        .position(|available| available == requirement)
    {
        return Ok(EvidenceBindingId::from_index(index));
    }

    match requirement {
        DictionaryReq::TraitImpl {
            trait_id,
            input_tys,
            output_tys,
            output_effs,
        } => trait_dictionary_evidence_binding(
            arena,
            *trait_id,
            input_tys,
            output_tys,
            output_effs,
            span,
            ctx,
        ),
        DictionaryReq::ProjectionSubscript { .. }
        | DictionaryReq::VariantPayloadIndirection { .. } => {
            structural_evidence_binding(arena, requirement, &[], span, ctx)
        }
    }
}

/// The evidence of a requirement on the structure of a type, built here when the type is known.
/// What it captures is taken from `members`, nodes of the plan, where one has the same
/// contract, and found as any other evidence otherwise.
fn structural_evidence_binding(
    arena: &mut NodeArena,
    requirement: &DictionaryReq,
    members: &[usize],
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<EvidenceBindingId, InternalCompilationError> {
    let inst_data = hir::FnInstData::new(vec![requirement.clone()], Vec::new(), Vec::new());
    let [(kind, _, _)] = extra_arg_kind_from_inst_data(&inst_data, span, ctx, arena)?
        .try_into()
        .expect("one evidence requirement must produce one argument");
    let source = match kind {
        NodeKind::GetSubscript(subscript) => {
            let value_trait = ctx.trait_solver.std_trait_id(VALUE_TRAIT_NAME);
            let mut captures = Vec::with_capacity(subscript.inst_data.dicts_req.len());
            for capture in &subscript.inst_data.dicts_req {
                let planned = members.iter().copied().find(|member| {
                    ctx.evidence_plan.nodes[*member]
                        .constraint
                        .dictionary_requirement_key(value_trait)
                        .is_some_and(|planned| planned.same_contract(capture))
                });
                captures.push(match planned {
                    Some(member) => replay_evidence_plan(arena, member, span, ctx)?,
                    None => evidence_binding_for_requirement(arena, capture, span, ctx)?,
                });
            }
            let static_captures = captures
                .iter()
                .map(|capture| ctx.static_evidence(*capture))
                .collect::<Option<Vec<_>>>();
            if let Some(captures) = static_captures {
                EvidenceBindingSource::Static(StaticEvidence::Subscript {
                    definition: subscript.subscript,
                    captures: captures.into_boxed_slice(),
                })
            } else {
                EvidenceBindingSource::ConstructedSubscript {
                    definition: subscript.subscript,
                    captures,
                }
            }
        }
        NodeKind::Immediate(value) => {
            EvidenceBindingSource::Static(StaticEvidence::VariantPayloadStorage(
                *value
                    .as_primitive_ty::<bool>()
                    .expect("variant layout evidence must be bool"),
            ))
        }
        NodeKind::LoadSubscriptEvidence(load) => {
            return Ok(load.extra_parameter);
        }
        NodeKind::LoadVariantPayloadStorageEvidence(load) => {
            return Ok(load.extra_parameter);
        }
        other => {
            return Err(internal_compilation_error!(Internal {
                error: format!("unexpected static evidence node {other:?}"),
                span,
            }));
        }
    };
    Ok(ctx.intern_evidence_binding(requirement.clone(), source))
}

/// Return the method slot and callable type from an already-instantiated dictionary type.
fn dictionary_method_projection_data(
    trait_def: &Trait,
    dictionary_ty: Type,
    method_index: TraitMethodIndex,
) -> (TraitDictionaryEntryIndex, Type) {
    let entry_index = trait_def.dictionary_method_index(method_index);
    let function_ty = dictionary_ty
        .data()
        .as_tuple()
        .expect("Trait impl dict should be a tuple type")[usize::from(entry_index)];
    (entry_index, function_ty)
}

fn get_projection_subscript_node_kind(
    subscript: SubscriptId,
    name: Ustr,
    span: Location,
    inst_data: hir::FnInstData,
) -> NodeKind {
    NodeKind::GetSubscript(b(hir::GetSubscript {
        subscript,
        subscript_path: Path::new(vec![(name, span)]),
        inst_data,
    }))
}

/// A use of the subscript that a type declares for a field: the subscript, its members, and
/// what it requires at the use.
struct ElaboratedFieldUse {
    subscript: SubscriptId,
    ty: SubscriptType,
    inst_data: hir::FnInstData,
}

/// The use of the subscript that the type `receiver_ty` declares for `field`, where the field
/// is read from a receiver of that type with a result of type `ret`; `None` if the type
/// declares no subscript for it.
///
/// Inference made the use as an instance of the scheme of the subscript, see
/// `ProjectionSubscriptIs`, and the function being elaborated kept that instance, see
/// `DeclaredFieldUse`: it is taken from there, as the instance of a use by name is taken from
/// its node. A use of a subscript of the group being emitted gets what its members require as
/// a reference to a function of the group does. Only a use that no function made, which an
/// implementation selected here for known types requires, is found from its types.
fn declared_field_use(
    receiver_ty: Type,
    ret: Type,
    field: Ustr,
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    arena: &mut NodeArena,
) -> Result<Option<ElaboratedFieldUse>, InternalCompilationError> {
    let Some((subscript, scheme)) = ctx
        .trait_solver
        .projection_subscript_scheme(receiver_ty, field)
    else {
        return Ok(None);
    };
    let recorded = ctx
        .evidence_plan
        .field_uses
        .iter()
        .find(|field_use| {
            field_use.subscript == subscript && field_use.answers(field, receiver_ty, ret)
        })
        .cloned();
    let (ty_args, eff_args) = match recorded {
        Some(field_use) if field_use.of_group => {
            let members = ctx.module_inst_data.and_then(|inst_data| {
                let member = inst_data.subscripts.get(&subscript.subscript)?;
                inst_data.functions.get(member)
            });
            let inst_data = match members {
                Some(members) if !members.requirements.is_empty() => late_module_call_inst_data(
                    members,
                    &hir::FnInstData::none(),
                    ctx.caller_inst_data,
                    span,
                    span,
                )?,
                _ => hir::FnInstData::none(),
            };
            return Ok(Some(ElaboratedFieldUse {
                subscript,
                ty: scheme.ty,
                inst_data,
            }));
        }
        Some(field_use) => (field_use.ty_args, field_use.eff_args),
        None => {
            let Some((_, _, subst)) = ctx.trait_solver.projection_subscript_instance(
                receiver_ty,
                ret,
                field,
                span,
                arena,
            )?
            else {
                return Ok(None);
            };
            (
                scheme
                    .ty_quantifiers
                    .iter()
                    .map(|quantifier| subst.0[quantifier])
                    .collect(),
                scheme
                    .eff_quantifiers
                    .iter()
                    .sorted()
                    .map(|quantifier| subst.1[quantifier].clone())
                    .collect(),
            )
        }
    };
    let subst: InstSubst = (
        scheme
            .ty_quantifiers
            .iter()
            .copied()
            .zip(ty_args.iter().copied())
            .collect(),
        scheme
            .eff_quantifiers
            .iter()
            .sorted()
            .copied()
            .zip(eff_args.iter().cloned())
            .collect(),
    );
    let mut mapper = BitmapInstantiationMapper::new(&subst);
    let solver = &*ctx.trait_solver;
    let requirements = extra_parameters_from_constraints_with(
        &scheme.constraints,
        solver.std_trait_id(VALUE_TRAIT_NAME),
        &|id| solver.trait_def(id),
    );
    let dicts_req = instantiate_dictionary_requirements(&requirements.requirements, &mut mapper);
    Ok(Some(ElaboratedFieldUse {
        subscript,
        ty: scheme.ty,
        inst_data: hir::FnInstData::new(dicts_req, ty_args, eff_args),
    }))
}

fn generated_projection_subscript_node_kind(
    subscript: SubscriptId,
    spec: GeneratedStructuralProjectionSpec,
    name: Ustr,
    span: Location,
    solver: &TraitSolver<'_>,
) -> NodeKind {
    let value_trait_id = solver.std_trait_id(VALUE_TRAIT_NAME);
    let (definition, requirements) =
        generated_structural_projection_definition(spec, value_trait_id, solver);
    let ty_args = definition
        .ty_scheme
        .ty_quantifiers
        .iter()
        .map(|quantifier| Type::variable(*quantifier))
        .collect();
    // Effect quantifiers are stored as a set, so their positional instantiation is stabilized.
    let eff_args = definition
        .ty_scheme
        .eff_quantifiers
        .iter()
        .sorted()
        .map(|quantifier| EffType::single_variable(*quantifier))
        .collect();
    get_projection_subscript_node_kind(
        subscript,
        name,
        span,
        hir::FnInstData::new(requirements, ty_args, eff_args),
    )
}

fn structural_projection_field_index(
    ty: Type,
    field: Ustr,
    solver: &TraitSolver<'_>,
) -> Option<ProjectionIndex> {
    let ty_data = ty.data();
    let ty_kind = ty_data.clone();
    drop(ty_data);
    let structural = match ty_kind {
        TypeKind::Named(named) => solver
            .type_def(named.def)
            .instantiated_shape_with_effects(&named.params, &named.effect_params),
        _ => ty,
    };
    let structural_data = structural.data();
    let index = match &*structural_data {
        TypeKind::Record(fields) => fields.iter().position(|candidate| candidate.0 == field),
        TypeKind::Tuple(fields) => field
            .as_str()
            .parse::<usize>()
            .ok()
            .filter(|&i| i < fields.len()),
        _ => None,
    };
    drop(structural_data);
    index.map(ProjectionIndex::from_index)
}

fn extra_arg_kind_from_inst_data(
    inst_data: &hir::FnInstData,
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    arena: &mut NodeArena,
) -> Result<Vec<(NodeKind, Type, FnArgType)>, InternalCompilationError> {
    use NodeKind as K;
    use TypeKind::*;
    process_results(inst_data
        .dicts_req
        .iter()
        .map(|dict| {
            use DictionaryReq::*;
            let (node_kind, node_ty) = match dict {
                ProjectionSubscript {
                    requirement,
                    field: name,
                    subscript_ty,
                } => {
                    let ty = subscript_ty.receiver_ty();
                    let expected_node_ty = Type::subscript_type(subscript_ty.clone());
                    let expected_arg_ty = FnArgType::new_by_val(expected_node_ty);
                    // Evidence that the function is given for this very type is taken as it
                    // is: an entry of a dictionary made for a known type is given the fields
                    // of that type, and not what building them again would take.
                    if !matches!(&*ty.data(), Variable(_))
                        && let Some(index) =
                            find_projection_subscript_dict_index_for_receiver_ty(ctx.dicts, ty, name)
                    {
                        return Ok((
                            K::LoadSubscriptEvidence(hir::LoadSubscriptEvidence {
                                extra_parameter: EvidenceBindingId::from_index(index),
                            }),
                            expected_node_ty,
                            expected_arg_ty,
                        ));
                    }
                    // As inference: the subscript that the type declares, where the
                    // requirement accepts one, and the stored field otherwise.
                    if requirement.accepts_user_defined_projection()
                        && let Some(field_use) =
                            declared_field_use(ty, subscript_ty.ret, *name, span, ctx, arena)?
                    {
                        return Ok((
                            get_projection_subscript_node_kind(
                                field_use.subscript,
                                *name,
                                span,
                                field_use.inst_data,
                            ),
                            expected_node_ty,
                            expected_arg_ty,
                        ));
                    }
                    let generated = ctx
                        .generated_projection_subscripts
                        .as_mut()
                        .expect("projection evidence generation requires module elaboration");
                    let structural_key = ProjectionKey::structural(ty, *name);
                    let existing_structural = generated.get_existing(structural_key);
                    let ty_data = ty.data();
                    let ty_kind = ty_data.clone();
                    drop(ty_data);
                    let node_kind = match ty_kind {
                        Tuple(_) | Record(_) | Named(_) => {
                            let index = structural_projection_field_index(
                                ty,
                                *name,
                                ctx.trait_solver,
                            )
                            .expect("field not found in structural projection receiver");
                            let spec = GeneratedStructuralProjectionSpec {
                                key: structural_key,
                                index,
                                field_ty: subscript_ty.ret,
                            };
                            if let Some(subscript) = existing_structural {
                                return Ok((
                                    generated_projection_subscript_node_kind(
                                        subscript,
                                        spec,
                                        *name,
                                        span,
                                        ctx.trait_solver,
                                    ),
                                    expected_node_ty,
                                    expected_arg_ty,
                                ));
                            }
                            let subscript = generated.get_or_create(spec);
                            generated_projection_subscript_node_kind(
                                subscript,
                                spec,
                                *name,
                                span,
                                ctx.trait_solver,
                            )
                        }
                        Variable(var) => {
                            let index = find_projection_subscript_dict_index(ctx.dicts, var, name).unwrap_or_else(
                                || panic!("Projection subscript dictionary for field \"{name}\" in type variable \"{var}\" not found, type inference should have failed"),
                            );
                            K::LoadSubscriptEvidence(hir::LoadSubscriptEvidence {
                                extra_parameter: EvidenceBindingId::from_index(index),
                            })
                        }
                        _ => {
                            panic!("ProjectionSubscript dictionary should have a variable or product type");
                        }
                    };
                    (node_kind, expected_node_ty)
                }
                VariantPayloadIndirection {
                    variant_ty,
                    tag,
                    ..
                } => {
                    let node_ty = Type::primitive::<bool>();
                    if matches!(&*variant_ty.data(), TypeKind::Variable(_)) {
                        let index = find_variant_payload_indirection_index(
                            ctx.dicts,
                            *variant_ty,
                            *tag,
                        )
                        .ok_or_else(|| {
                            internal_compilation_error!(Internal {
                                error: format!(
                                    "variant payload-indirection evidence {dict:?} not found in generic caller requirements {:?}",
                                    ctx.dicts.requirements
                                ),
                                span,
                            })
                        })?;
                        (
                            K::LoadVariantPayloadStorageEvidence(
                                hir::LoadVariantPayloadStorageEvidence {
                                    extra_parameter: EvidenceBindingId::from_index(index),
                                },
                            ),
                            node_ty,
                        )
                    } else {
                        let storage = variant_payload_storage_for_type(
                            *variant_ty,
                            *tag,
                            span,
                            ctx.trait_solver,
                        )?;
                        (K::Immediate(LiteralValue::new_native(storage.is_indirect())), node_ty)
                    }
                }
                TraitImpl { trait_id, input_tys, output_tys, output_effs } => {
                    let (node_kind, ty) = trait_dictionary_node_kind(
                        arena,
                        *trait_id,
                        input_tys,
                        output_tys,
                        output_effs,
                        span,
                        ctx,
                    )?;
                    (node_kind, ty)
                }
            };
            Ok((
                node_kind,
                node_ty,
                FnArgType::new(node_ty, MutType::constant()),
            ))
        }), |iter| iter.collect()
    )
}

/// The requirements of a function of the module at a reference whose inference left them
/// out, because the function was not final: it is of the recursive group of the function that
/// makes the reference, or is one of its lambdas.
///
/// The functions of a recursive group are inferred with one instance of each type, so the caller
/// and the callee name a type by the same inference variable: the type argument of a callee
/// quantifier is the caller's quantifier with the same origin. An origin that the caller does not
/// quantify is a type its body cannot observe, as its unbound variables are: `never`.
///
/// Effects are the same when the callee has no effects per reference, an effect that the
/// caller does not retain being none. Otherwise they are those that the settling of the group
/// recorded for the `site` of the reference.
fn late_module_call_inst_data(
    callee: &LateFunctionInstData,
    call_inst_data: &hir::FnInstData,
    caller: Option<&LateFunctionInstData>,
    site: Location,
    span: Location,
) -> Result<hir::FnInstData, InternalCompilationError> {
    let caller_ty_origins = caller.map_or(&[][..], |caller| &caller.ty_origins);
    let caller_effect_origins = caller.map_or(&[][..], |caller| &caller.effect_origins);
    let ty_subst = callee
        .ty_origins
        .iter()
        .enumerate()
        .map(|(index, origin)| {
            let ty = match caller_ty_origins.iter().position(|other| other == origin) {
                Some(position) => Type::variable(TypeVar::new(position as u32)),
                None => Type::never(),
            };
            (TypeVar::new(index as u32), ty)
        })
        .collect::<FxHashMap<_, _>>();
    let quantifiers = (0..callee.effect_origins.len() as u32).map(EffectVar::new);
    let eff_subst = if callee.effects_per_reference {
        let recorded = caller
            .and_then(|caller| caller.reference_effects.get(&site))
            .filter(|effects| effects.len() == callee.effect_origins.len())
            .ok_or_else(|| {
                internal_compilation_error!(Internal {
                    error: "a reference inside a settled group has no recorded effects".into(),
                    span,
                })
            })?;
        quantifiers
            .zip(recorded.iter().cloned())
            .collect::<EffectsInstSubst>()
    } else {
        quantifiers
            .zip(&callee.effect_origins)
            .map(|(quantifier, origin)| {
                let position = caller_effect_origins
                    .iter()
                    .position(|other| other == origin);
                let effects = match position {
                    Some(position) => EffType::single_variable(EffectVar::new(position as u32)),
                    None => EffType::empty(),
                };
                (quantifier, effects)
            })
            .collect::<EffectsInstSubst>()
    };
    let subst = (ty_subst, eff_subst);
    let mut mapper = BitmapInstantiationMapper::new(&subst);
    let dicts_req =
        instantiate_dictionary_requirements(&callee.requirements.requirements, &mut mapper);
    Ok(hir::FnInstData::new(
        dicts_req,
        call_inst_data.ty_args.clone(),
        call_inst_data.eff_args.clone(),
    ))
}

/// Bind the variables in a final callee type to the corresponding call-site types.
///
/// Recursive module calls were inferred from a preliminary scheme, whose positional quantifier
/// order need not match the final generalized scheme. The function surface is nevertheless the
/// authoritative relationship between both schemes. Repeated pairs are accepted coinductively so
/// recursive interned type graphs terminate without assigning identity by case tag.
pub(crate) fn bind_call_type_instantiation(
    pattern: Type,
    actual: Type,
    subst: &mut FxHashMap<TypeVar, Type>,
    correspondence: &mut FxHashMap<Type, Type>,
    active: &mut FxHashSet<(Type, Type)>,
) -> bool {
    let pattern_kind = pattern.data().clone();
    if let TypeKind::Variable(var) = &pattern_kind {
        return match subst.get(var) {
            Some(bound) => *bound == actual,
            None => {
                subst.insert(*var, actual);
                true
            }
        };
    }
    if let Some(bound) = correspondence.get(&pattern) {
        return *bound == actual;
    }
    correspondence.insert(pattern, actual);
    // Callee and caller variables have separate scopes even when their interned IDs coincide.
    // Walk open structures to bind/check their leaves instead of assuming an identity mapping.
    if pattern == actual && pattern.is_constant() {
        return true;
    }
    if !active.insert((pattern, actual)) {
        return true;
    }

    let actual_kind = actual.data().clone();
    let matches = match (pattern_kind, actual_kind) {
        (TypeKind::Tuple(left), TypeKind::Tuple(right)) => {
            left.len() == right.len()
                && left.into_iter().zip(right).all(|(left, right)| {
                    bind_call_type_instantiation(left, right, subst, correspondence, active)
                })
        }
        (TypeKind::Record(left), TypeKind::Record(right))
        | (TypeKind::Variant(left), TypeKind::Variant(right)) => {
            left.len() == right.len()
                && left
                    .into_iter()
                    .zip(right)
                    .all(|((left_name, left), (right_name, right))| {
                        left_name == right_name
                            && bind_call_type_instantiation(
                                left,
                                right,
                                subst,
                                correspondence,
                                active,
                            )
                    })
        }
        (TypeKind::Native(left), TypeKind::Native(right)) => {
            left.bare_ty == right.bare_ty
                && left.arguments.len() == right.arguments.len()
                && left
                    .arguments
                    .into_iter()
                    .zip(right.arguments)
                    .all(|(left, right)| {
                        bind_call_type_instantiation(left, right, subst, correspondence, active)
                    })
        }
        (TypeKind::Named(left), TypeKind::Named(right)) => {
            left.def == right.def
                && left.params.len() == right.params.len()
                && left
                    .params
                    .into_iter()
                    .zip(right.params)
                    .all(|(left, right)| {
                        bind_call_type_instantiation(left, right, subst, correspondence, active)
                    })
        }
        (TypeKind::Function(left), TypeKind::Function(right)) => {
            left.args.len() == right.args.len()
                && left.args.iter().zip(&right.args).all(|(left, right)| {
                    bind_call_type_instantiation(left.ty, right.ty, subst, correspondence, active)
                })
                && bind_call_type_instantiation(left.ret, right.ret, subst, correspondence, active)
        }
        (TypeKind::Subscript(left), TypeKind::Subscript(right)) => {
            left.args.len() == right.args.len()
                && left.args.iter().zip(&right.args).all(|(left, right)| {
                    bind_call_type_instantiation(left.ty, right.ty, subst, correspondence, active)
                })
                && bind_call_type_instantiation(left.ret, right.ret, subst, correspondence, active)
        }
        (TypeKind::Never, TypeKind::Never) => true,
        _ => false,
    };
    active.remove(&(pattern, actual));
    matches
}

/// Result of elaborating one unelaborated HIR root into the final HIR arena.
pub struct ElaboratedHir {
    pub root: ENodeId,
    pub remap: FxHashMap<UNodeId, ENodeId>,
    pub locals: Vec<ELocalDecl>,
}

/// Where a constructor keeps its members while building them.
#[derive(Clone, Copy)]
enum ConstructionStorage {
    /// In the constructed value itself, which owns nothing else.
    Inline,
    /// In storage the constructor allocates before building its first member.
    AllocatedFirst,
}

/// Whether evaluation can leave a construction needing guest cleanup (poisoning does not).
fn can_interrupt(arena: &UNodeArena, node: UNodeId) -> bool {
    !arena[node].effects.cannot_fail()
        || matches!(
            arena[node].kind,
            NodeKind::Return(_) | NodeKind::Break(_) | NodeKind::Continue(_)
        )
        || arena[node]
            .kind
            .child_node_ids()
            .iter()
            .any(|child| can_interrupt(arena, *child))
}

fn node_contains_yield(arena: &UNodeArena, root: UNodeId) -> bool {
    matches!(arena[root].kind, NodeKind::Yield(_))
        || arena[root]
            .kind
            .child_node_ids()
            .into_iter()
            .any(|child| node_contains_yield(arena, child))
}

/// Elaborate a pre-dictionary-passing HIR tree into the final HIR arena.
#[cfg(test)]
fn elaborate_hir<'d, 'sr, 'sm>(
    src: &mut UNodeArena,
    root: UNodeId,
    dst: &mut ENodeArena,
    ctx: &mut DictElaborationCtx<'d, 'sr, 'sm>,
    locals: Vec<LocalDecl>,
) -> Result<ElaboratedHir, InternalCompilationError> {
    let mut warnings = Vec::new();
    elaborate_hir_with_warnings(src, root, dst, ctx, locals, &mut warnings)
}

/// Elaborate HIR while reporting unreachable suffixes that became visible only after final type
/// substitution. Most suffixes are already diagnosed and pruned during inference.
pub(crate) fn elaborate_hir_with_warnings<'d, 'sr, 'sm>(
    src: &mut UNodeArena,
    root: UNodeId,
    dst: &mut ENodeArena,
    ctx: &mut DictElaborationCtx<'d, 'sr, 'sm>,
    mut locals: Vec<LocalDecl>,
    warnings: &mut Vec<CompilationWarning>,
) -> Result<ElaboratedHir, InternalCompilationError> {
    hir::assignment::lower_pending_assignments(src, root, &mut locals);
    hir::value_dispatch::elaborate_local_ownership_and_value_dispatches(src, &mut locals, ctx)?;
    let mut elaboration = HirElaboration::new(dst, ctx, locals, warnings);
    let root = elaboration.elaborate_node(src, root)?;
    LocalDecl::assign_sequential_slots(&mut elaboration.locals);
    Ok(ElaboratedHir {
        root,
        remap: elaboration.remap,
        locals: elaboration
            .locals
            .into_iter()
            .map(LocalDecl::into_elaborated)
            .collect(),
    })
}

/// Finalize generated functions returned by trait-solver commits into the final HIR arena.
pub fn elaborate_generated_functions(
    module: &mut Module,
    others: &Modules,
    pending_functions: &mut FxHashMap<LocalFunctionId, PendingModuleFunction>,
    ids: impl IntoIterator<Item = LocalFunctionId>,
) -> Result<(), InternalCompilationError> {
    elaborate_generated_functions_with_private_impls(module, others, pending_functions, ids, None)
}

/// As [`elaborate_generated_functions`], for functions generated while compiling an expression
/// that may use the private impls of `private_impl_module`: they resolve evidence on its behalf.
pub(crate) fn elaborate_generated_functions_with_private_impls(
    module: &mut Module,
    others: &Modules,
    pending_functions: &mut FxHashMap<LocalFunctionId, PendingModuleFunction>,
    ids: impl IntoIterator<Item = LocalFunctionId>,
    private_impl_module: Option<ModuleId>,
) -> Result<(), InternalCompilationError> {
    let mut pending = ids.into_iter().collect::<Vec<_>>();
    let mut index = 0;
    while index < pending.len() {
        let id = pending[index];
        index += 1;
        let Some(mut function) = pending_functions.remove(&id) else {
            continue;
        };
        if function.definition.ty_scheme != module.functions[id.as_index()].definition.ty_scheme {
            return Err(internal_compilation_error!(Internal {
                error: "A pending generated body and its placeholder have different schemes".into(),
                span: function.code.arena[function.code.entry_node_id].span,
            }));
        }
        function.definition = module.functions[id.as_index()].definition.clone();
        function.spans = module.functions[id.as_index()].spans.clone();

        let dicts = module.functions[id.as_index()]
            .definition
            .ty_scheme
            .extra_parameters(ModuleEnv::new(module, others));
        let generated_projection_subscripts =
            PendingGeneratedStructuralProjectionSubscripts::new(module);
        let mut solver = trait_solver_from_module!(module, others);
        if let Some(module_id) = private_impl_module {
            solver.allow_private_impls_from(module_id);
        }
        let mut ctx = DictElaborationCtx::new_with_generated_projection_subscripts(
            &dicts,
            None,
            &mut solver,
            generated_projection_subscripts,
        );
        let elaborated =
            function.check_borrows_and_elaborate_hir(&mut module.hir_arena, &mut ctx)?;
        module.functions[id.as_index()] = elaborated;
        let generated_projection_subscripts = ctx.take_generated_projection_subscripts();
        let generated = solver.finish().commit(
            &mut module.functions,
            &mut module.def_table,
            pending_functions,
        );
        if let Some(generated_projection_subscripts) = generated_projection_subscripts {
            generated_projection_subscripts.commit(module, others);
        }
        pending.extend(generated);
    }
    Ok(())
}

/// Stateful worker that appends elaborated HIR nodes while tracking UNodeId-to-ENodeId remaps.
struct HirElaboration<'a, 'w, 'd, 'sr, 'sm> {
    generated: UNodeArena,
    dst: &'a mut ENodeArena,
    ctx: &'a mut DictElaborationCtx<'d, 'sr, 'sm>,
    locals: Vec<LocalDecl>,
    remap: FxHashMap<UNodeId, ENodeId>,
    place_aliases: FxHashMap<LocalDeclId, UNodeId>,
    in_progress: FxHashSet<UNodeId>,
    warnings: &'w mut Vec<CompilationWarning>,
    /// The open projections whose slide may fail, innermost last.
    failing_projections: Vec<FailingProjection>,
    /// The elaborated loop of each source loop label.
    loops: FxHashMap<LoopId, ElaboratedLoop>,
    /// The next label of an elaborated loop, source loops and generated ones alike.
    next_loop_id: LoopId,
}

/// An elaborated source loop.
#[derive(Clone, Copy)]
struct ElaboratedLoop {
    label: LoopId,
    /// The number of failing projections open when it was entered.
    failing_projections: usize,
}

/// The values transferred out of the body of an open projection whose slide may fail.
///
/// A `return` or `break` leaving the body stores its value in a local owned by the block around
/// the projection, then leaves the projection by breaking out of its own loop around it. After
/// that loop, where the slide has run, the transfer is re-issued from the local; if the slide
/// fails, the block drops the local instead.
#[derive(Default)]
struct FailingProjection {
    transfers: Vec<HeldTransfer>,
}

/// A transfer out of a failing projection, held until its slide has run.
struct HeldTransfer {
    local: LocalDeclId,
    target: TransferTarget,
    exit: LoopId,
}

#[derive(Debug, Clone, Copy)]
enum TransferTarget {
    Return,
    Break(LoopId),
}

impl TransferTarget {
    fn transfer(self, value: ENodeId) -> NodeKind<Elaborated> {
        match self {
            Self::Return => NodeKind::Return(value),
            Self::Break(label) => NodeKind::Break(hir::Break { label, value }),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum ArgumentLifetimePlan {
    Direct,
    Snapshot {
        clone: ResolvedLocalClone,
        drop: Option<ResolvedLocalDrop>,
    },
    MaterializeOwned {
        drop: ResolvedLocalDrop,
    },
}

struct ElaboratedCallArguments {
    arguments: Vec<CallArgument<Elaborated>>,
    cleanup: Vec<LocalDeclId>,
}

impl<'a, 'w, 'd, 'sr, 'sm> HirElaboration<'a, 'w, 'd, 'sr, 'sm> {
    fn new(
        dst: &'a mut ENodeArena,
        ctx: &'a mut DictElaborationCtx<'d, 'sr, 'sm>,
        locals: Vec<LocalDecl>,
        warnings: &'w mut Vec<CompilationWarning>,
    ) -> Self {
        Self {
            generated: UNodeArena::default(),
            dst,
            ctx,
            locals,
            remap: FxHashMap::default(),
            place_aliases: FxHashMap::default(),
            in_progress: FxHashSet::default(),
            warnings,
            failing_projections: Vec::new(),
            loops: FxHashMap::default(),
            next_loop_id: LoopId::from_index(0),
        }
    }

    /// Make the closed `Value<ty>` evidence needed by physical layout available to MIR lowering.
    ///
    /// Type inference exposes only the external evidence leaves of a compiler-derived aggregate.
    /// Elaboration constructs the aggregate dictionaries themselves and records them in the
    /// function evidence graph, where MIR lowering can retrieve them by their logical type.
    fn ensure_value_layout_evidence(
        &mut self,
        ty: Type,
        span: Location,
    ) -> Result<(), InternalCompilationError> {
        if type_has_static_layout(ty, span, self.ctx.trait_solver) {
            return Ok(());
        }
        let value_trait = self.ctx.trait_solver.std_trait_id(VALUE_TRAIT_NAME);
        trait_dictionary_evidence_binding(
            &mut self.generated,
            value_trait,
            &[ty],
            &[],
            &[],
            span,
            self.ctx,
        )?;
        Ok(())
    }

    /// Record every dictionary consumed when a product is allocated or one of its fields is
    /// addressed. Nested open members have their own closed dictionaries even though all of them
    /// ultimately capture the same source-level leaf evidence.
    fn ensure_product_layout_evidence(
        &mut self,
        aggregate_ty: Type,
        span: Location,
    ) -> Result<(), InternalCompilationError> {
        let members = dynamic_product_member_layouts(aggregate_ty, span, self.ctx.trait_solver);
        for member in members {
            self.ensure_value_layout_evidence(member, span)?;
        }
        Ok(())
    }

    fn push_owned_temp(
        &mut self,
        ty: Type,
        drop: ResolvedLocalDrop,
        span: Location,
        name: Ustr,
    ) -> LocalDeclId {
        let mut local = LocalDecl::new(
            (name, Location::new_synthesized()),
            MutType::constant(),
            ty,
            None,
            span,
        );
        local.set_owned_storage(PendingLocalDrop::Resolved(drop));
        LocalDecl::push_with_next_slot(&mut self.locals, local)
    }

    fn fresh_loop_id(&mut self) -> LoopId {
        let label = self.next_loop_id;
        self.next_loop_id = LoopId::from_index(label.as_index() + 1);
        label
    }

    /// Build a transfer of `value` to `target`, crossing the failing projections from `crossed`
    /// inwards. If it crosses any and its value needs a drop, hold the value until their slides
    /// have run (see `FailingProjection`).
    fn transfer_value(
        &mut self,
        value: ENodeId,
        target: TransferTarget,
        crossed: usize,
        span: Location,
    ) -> Result<NodeKind<Elaborated>, InternalCompilationError> {
        let value_ty = self.dst[value].ty;
        if crossed >= self.failing_projections.len() || value_ty == Type::never() {
            return Ok(target.transfer(value));
        }
        let drop =
            resolve_local_drop(&mut self.generated, self.ctx, value_ty, span)?.into_elaborated();
        if drop == ResolvedLocalDrop::Skip {
            return Ok(target.transfer(value));
        }
        let local = self.push_owned_temp(value_ty, drop, span, ustr("$transferred"));
        let exit = self.fresh_loop_id();
        // Leave through the outermost crossed projection: its exits are outside all the others.
        self.failing_projections[crossed]
            .transfers
            .push(HeldTransfer {
                local,
                target,
                exit,
            });
        let value_effects = self.dst[value].effects.clone();
        let store = self.alloc_elaborated_node(
            NodeKind::StoreLocal(hir::StoreLocal { value, id: local }),
            Type::unit(),
            value_effects,
            span,
        );
        let unit = self.alloc_elaborated_node(
            NodeKind::Immediate(LiteralValue::new_native(())),
            Type::unit(),
            no_effects(),
            span,
        );
        let exit = self.alloc_elaborated_node(
            NodeKind::Break(hir::Break {
                label: exit,
                value: unit,
            }),
            Type::never(),
            no_effects(),
            span,
        );
        Ok(NodeKind::Block(b(hir::Block {
            body: b(SVec2::from_vec(vec![store, exit])),
            cleanup: Vec::new(),
        })))
    }

    /// Lower `projection`, whose slide may fail, so that no value leaving it is in its destination
    /// before the slide has run: its body's value is held in a local, as are the values its
    /// transfers carry, and the transfers are re-issued after it:
    /// `loop 'done { loop 'exit_1 { … projection; break 'done result … }; transfer_1 }`.
    fn elaborate_failing_projection(
        &mut self,
        mut projection: hir::WithYielded<Elaborated>,
        exits: FailingProjection,
        ty: Type,
        effects: &EffType,
        span: Location,
    ) -> Result<NodeKind<Elaborated>, InternalCompilationError> {
        let result = if ty == Type::never() {
            None
        } else {
            let drop =
                resolve_local_drop(&mut self.generated, self.ctx, ty, span)?.into_elaborated();
            (drop != ResolvedLocalDrop::Skip)
                .then(|| self.push_owned_temp(ty, drop, span, ustr("$yielded")))
        };
        if result.is_none() && exits.transfers.is_empty() {
            return Ok(NodeKind::WithYielded(projection));
        }
        let mut cleanup = Vec::new();
        // The projection, then its value.
        let nodes = if let Some(result) = result {
            let body_effects = self.dst[projection.body].effects.clone();
            projection.body = self.alloc_elaborated_node(
                NodeKind::StoreLocal(hir::StoreLocal {
                    value: projection.body,
                    id: result,
                }),
                Type::unit(),
                body_effects,
                span,
            );
            cleanup.push(result);
            let projection = self.alloc_elaborated_node(
                NodeKind::WithYielded(projection),
                Type::unit(),
                effects.clone(),
                span,
            );
            let value = self.alloc_elaborated_node(
                NodeKind::TakeLocalValue(hir::TakeLocalValue {
                    id: result,
                    mode: ResolvedTakeLocalValueMode::MoveOwned,
                }),
                ty,
                no_effects(),
                span,
            );
            vec![projection, value]
        } else {
            vec![self.alloc_elaborated_node(
                NodeKind::WithYielded(projection),
                ty,
                effects.clone(),
                span,
            )]
        };
        if exits.transfers.is_empty() {
            return Ok(NodeKind::Block(b(hir::Block {
                body: b(SVec2::from_vec(nodes)),
                cleanup,
            })));
        }
        let mut node = match nodes[..] {
            [node] => node,
            _ => self.alloc_elaborated_node(
                NodeKind::Block(b(hir::Block {
                    body: b(SVec2::from_vec(nodes)),
                    cleanup: Vec::new(),
                })),
                ty,
                effects.clone(),
                span,
            ),
        };
        let done = (ty != Type::never()).then(|| self.fresh_loop_id());
        if let Some(done) = done {
            node = self.alloc_elaborated_node(
                NodeKind::Break(hir::Break {
                    label: done,
                    value: node,
                }),
                Type::never(),
                effects.clone(),
                span,
            );
        }
        for held in exits.transfers.into_iter().rev() {
            let exit = self.alloc_elaborated_node(
                NodeKind::Loop(hir::Loop {
                    label: held.exit,
                    body: node,
                }),
                Type::unit(),
                effects.clone(),
                span,
            );
            let held_ty = self.locals[held.local.as_index()].ty;
            let value = self.alloc_elaborated_node(
                NodeKind::TakeLocalValue(hir::TakeLocalValue {
                    id: held.local,
                    mode: ResolvedTakeLocalValueMode::MoveOwned,
                }),
                held_ty,
                no_effects(),
                span,
            );
            let transfer = self.alloc_elaborated_node(
                held.target.transfer(value),
                Type::never(),
                no_effects(),
                span,
            );
            node = self.alloc_elaborated_node(
                NodeKind::Block(b(hir::Block {
                    body: b(SVec2::from_vec(vec![exit, transfer])),
                    cleanup: Vec::new(),
                })),
                Type::never(),
                effects.clone(),
                span,
            );
            cleanup.push(held.local);
        }
        if let Some(done) = done {
            node = self.alloc_elaborated_node(
                NodeKind::Loop(hir::Loop {
                    label: done,
                    body: node,
                }),
                ty,
                effects.clone(),
                span,
            );
        }
        Ok(NodeKind::Block(b(hir::Block {
            body: b(SVec2::from_vec(vec![node])),
            cleanup,
        })))
    }

    #[allow(clippy::too_many_arguments)]
    fn materialize_call_value(
        &mut self,
        value: ENodeId,
        ty: Type,
        effects: &EffType,
        value_span: Location,
        scope_span: Location,
        name: Ustr,
        drop: ResolvedLocalDrop,
    ) -> (ENodeId, LocalDeclId) {
        let local = self.push_owned_temp(ty, drop, scope_span, name);
        let store = self.alloc_elaborated_node(
            NodeKind::StoreLocal(hir::StoreLocal { value, id: local }),
            Type::unit(),
            effects.clone(),
            value_span,
        );
        let load = self.alloc_elaborated_node(
            NodeKind::LoadLocal(hir::LoadLocal { id: local }),
            ty,
            no_effects(),
            value_span,
        );
        let value = self.alloc_elaborated_node(
            NodeKind::Block(b(hir::Block {
                body: b(SVec2::from_vec(vec![store, load])),
                cleanup: Vec::new(),
            })),
            ty,
            effects.clone(),
            value_span,
        );
        (value, local)
    }

    fn elaborate_node(
        &mut self,
        src: &UNodeArena,
        old: UNodeId,
    ) -> Result<ENodeId, InternalCompilationError> {
        if let Some(&new) = self.remap.get(&old) {
            return Ok(new);
        }
        if !self.in_progress.insert(old) {
            return Err(internal_compilation_error!(Internal {
                error: "cycle found while elaborating HIR".to_string(),
                span: src[old].span,
            }));
        }

        let old_node = &src[old];
        let old_ty = old_node.ty;
        let old_effects = old_node.effects.clone();
        let old_span = old_node.span;
        let kind = self.elaborate_source_kind(src, old, old_ty, &old_effects, old_span)?;
        let new = self
            .dst
            .alloc(Node::<Elaborated>::new(kind, old_ty, old_effects, old_span));
        self.in_progress.remove(&old);
        self.remap.insert(old, new);
        Ok(new)
    }

    /// Keep completed fields owned until every field has evaluated, then transfer them together.
    fn elaborate_construction(
        &mut self,
        src: &UNodeArena,
        old: UNodeId,
        nodes: &[UNodeId],
        constructor: fn(hir::NodeIds<Elaborated>) -> NodeKind<Elaborated>,
        storage: ConstructionStorage,
    ) -> Result<NodeKind<Elaborated>, InternalCompilationError> {
        let ty = src[old].ty;
        let effects = &src[old].effects;
        let span = src[old].span;
        // Poisoning needs no guest cleanup. Only source failure or a control transfer can
        // require dropping a completed prefix; straight-line constructors stay unchanged.
        let last_interruption = nodes.iter().rposition(|node| can_interrupt(src, *node));
        let prefix_len = last_interruption.unwrap_or(0);
        // An array allocates before building its first element, so it owns storage even when that
        // element is the one interrupted, except a trivially copied one, built after its elements.
        let allocates_first = matches!(storage, ConstructionStorage::AllocatedFirst)
            && nodes.first().is_some_and(|element| {
                !self
                    .ctx
                    .trait_solver
                    .concrete_type_is_trivial_copy(src[*element].ty)
            });
        if last_interruption.is_none() || (prefix_len == 0 && !allocates_first) {
            let fields = b(SVec2::from_vec(
                self.elaborate_node_iter(src, nodes.iter().copied())?,
            ));
            return Ok(constructor(fields));
        }
        let mut drops = Vec::with_capacity(nodes.len());
        for node in nodes.iter().take(prefix_len) {
            drops.push(if src[*node].ty == Type::never() {
                ResolvedLocalDrop::Skip
            } else {
                resolve_local_drop(&mut self.generated, self.ctx, src[*node].ty, span)?
                    .into_elaborated()
            });
        }
        let needs_cleanup =
            allocates_first || drops.iter().any(|drop| *drop != ResolvedLocalDrop::Skip);
        let mut fields = Vec::with_capacity(nodes.len());
        let mut body = Vec::new();
        let mut cleanup = Vec::new();
        for (index, node) in nodes.iter().copied().enumerate() {
            let value = self.elaborate_node(src, node)?;
            if !needs_cleanup {
                fields.push(value);
                continue;
            }
            if src[node].ty == Type::never() {
                body.push(value);
                return Ok(NodeKind::Block(b(hir::Block {
                    body: b(SVec2::from_vec(body)),
                    cleanup,
                })));
            }
            // The interrupting field can itself hold a partial in-place construction. Later
            // fields cannot be interrupted and need no temporary cleanup obligation.
            let drop = match drops.get(index).copied() {
                Some(drop) => drop,
                None if index == prefix_len => {
                    resolve_local_drop(&mut self.generated, self.ctx, src[node].ty, span)?
                        .into_elaborated()
                }
                None => ResolvedLocalDrop::Skip,
            };
            let local = self.push_owned_temp(src[node].ty, drop, span, ustr("$field"));
            body.push(self.alloc_elaborated_node(
                NodeKind::StoreLocal(hir::StoreLocal { value, id: local }),
                Type::unit(),
                src[node].effects.clone(),
                src[node].span,
            ));
            cleanup.push(local);
            fields.push(self.alloc_elaborated_node(
                NodeKind::TakeLocalValue(hir::TakeLocalValue {
                    id: local,
                    mode: ResolvedTakeLocalValueMode::MoveOwned,
                }),
                src[node].ty,
                no_effects(),
                src[node].span,
            ));
        }
        let fields = b(SVec2::from_vec(fields));
        let product = constructor(fields);
        if body.is_empty() {
            return Ok(product);
        }
        body.push(self.alloc_elaborated_node(product, ty, effects.clone(), span));
        Ok(NodeKind::Block(b(hir::Block {
            body: b(SVec2::from_vec(body)),
            cleanup,
        })))
    }

    fn elaborate_synthetic_node(
        &mut self,
        kind: NodeKind<Unelaborated>,
        ty: Type,
        effects: EffType,
        span: Location,
    ) -> Result<ENodeId, InternalCompilationError> {
        let kind = self.elaborate_synthetic_kind(kind, ty, &effects, span)?;
        Ok(self.alloc_elaborated_node(kind, ty, effects, span))
    }

    fn elaborate_get_subscript(
        &mut self,
        mut get_subscript: hir::GetSubscript,
        node_ty: Type,
        node_effects: &EffType,
        node_span: Location,
    ) -> Result<NodeKind<Elaborated>, InternalCompilationError> {
        let captures = if !get_subscript.inst_data.dicts_req.is_empty() {
            let (captures, _) =
                self.elaborate_extra_args_from_inst_data(&get_subscript.inst_data, node_span)?;
            get_subscript.inst_data.dicts_req.clear();
            captures
        } else if get_subscript.subscript.module
            == self.ctx.trait_solver.current_type_items.module.id
            && let Some(requirements) = self.ctx.module_inst_data.and_then(|inst_data| {
                let member = inst_data
                    .subscripts
                    .get(&get_subscript.subscript.subscript)?;
                inst_data.functions.get(member)
            })
            && !requirements.requirements.is_empty()
        {
            // The subscript is of the group being emitted: its value holds what its members
            // require, as a reference to a function of the group does.
            let late_inst_data = late_module_call_inst_data(
                requirements,
                &get_subscript.inst_data,
                self.ctx.caller_inst_data,
                node_span,
                node_span,
            )?;
            self.elaborate_extra_args_from_inst_data(&late_inst_data, node_span)?
                .0
        } else {
            Vec::new()
        };
        if captures.is_empty() {
            Ok(NodeKind::GetSubscript(b(get_subscript)))
        } else {
            let subscript = self.alloc_elaborated_node(
                NodeKind::GetSubscript(b(get_subscript)),
                node_ty,
                node_effects.clone(),
                node_span,
            );
            Ok(NodeKind::BuildSubscriptValue(b(hir::BuildSubscriptValue {
                subscript,
                evidence_captures: captures,
            })))
        }
    }

    fn elaborate_synthetic_kind(
        &mut self,
        kind: NodeKind<Unelaborated>,
        ty: Type,
        effects: &EffType,
        span: Location,
    ) -> Result<NodeKind<Elaborated>, InternalCompilationError> {
        use NodeKind::*;
        Ok(match kind {
            Immediate(value) => Immediate(value),
            GetSubscript(get_subscript) => {
                return self.elaborate_get_subscript(*get_subscript, ty, effects, span);
            }
            GetDictionary(get_dict) => {
                let captures = get_dict
                    .captures
                    .into_iter()
                    .map(|capture| self.elaborate_generated_evidence_node(capture))
                    .collect::<Result<_, _>>()?;
                GetDictionary(hir::GetDictionary {
                    dictionary: get_dict.dictionary,
                    captures,
                })
            }
            LoadDictionary(load) => LoadDictionary(load),
            LoadSubscriptEvidence(load) => LoadSubscriptEvidence(load),
            LoadVariantPayloadStorageEvidence(load) => LoadVariantPayloadStorageEvidence(load),
            _ => {
                return Err(internal_compilation_error!(Internal {
                    error: "unexpected synthetic HIR node requiring recursive elaboration"
                        .to_string(),
                    span,
                }));
            }
        })
    }

    fn elaborate_generated_evidence_node(
        &mut self,
        node: UNodeId,
    ) -> Result<ENodeId, InternalCompilationError> {
        let node = self.generated[node].clone();
        let kind = self.elaborate_synthetic_kind(node.kind, node.ty, &node.effects, node.span)?;
        Ok(self.alloc_elaborated_node(kind, node.ty, node.effects, node.span))
    }

    fn alloc_elaborated_node(
        &mut self,
        kind: NodeKind<Elaborated>,
        ty: Type,
        effects: EffType,
        span: Location,
    ) -> ENodeId {
        self.dst
            .alloc(Node::<Elaborated>::new(kind, ty, effects, span))
    }

    fn projection_evidence_field_access(
        &mut self,
        child: ENodeId,
        field_name: Ustr,
        access_mode: SubscriptMemberKind,
        index: usize,
        node_ty: Type,
        node_span: Location,
    ) -> NodeKind<Elaborated> {
        use NodeKind::*;
        let extra_parameter = EvidenceBindingId::from_index(index);
        let DictionaryReq::ProjectionSubscript { subscript_ty, .. } =
            &self.ctx.dicts.requirements[index]
        else {
            panic!("Projection subscript dictionary index should reference projection evidence");
        };
        let subscript_ty = subscript_ty.clone();
        let subscript = self.alloc_elaborated_node(
            LoadSubscriptEvidence(hir::LoadSubscriptEvidence { extra_parameter }),
            Type::subscript_type(subscript_ty.clone()),
            no_effects(),
            node_span,
        );
        self.subscript_field_access(
            subscript,
            &subscript_ty,
            child,
            field_name,
            access_mode,
            node_ty,
        )
    }

    /// The access to the field `field_name` of `child` through the value `subscript` of the
    /// subscript that gives it, of type `subscript_ty`.
    fn subscript_field_access(
        &mut self,
        subscript: ENodeId,
        subscript_ty: &SubscriptType,
        child: ENodeId,
        field_name: Ustr,
        access_mode: SubscriptMemberKind,
        node_ty: Type,
    ) -> NodeKind<Elaborated> {
        use NodeKind::*;
        let member_ty = match access_mode {
            SubscriptMemberKind::Ref => subscript_ty.ref_member.as_ref(),
            SubscriptMemberKind::Mut => subscript_ty.mut_member.as_ref(),
        }
        .unwrap_or_else(|| {
            panic!(
                "Projection evidence for field \"{field_name}\" should contain the selected member"
            )
        });
        let mut inst_fn_args = subscript_ty.args.clone();
        if access_mode.mut_member() {
            inst_fn_args[0].mut_ty = MutType::mutable();
        }
        let passing = if access_mode.mut_member() {
            ArgConvention::MutableRef
        } else {
            ArgConvention::Let
        };
        SubscriptApply(b(hir::SubscriptApplication {
            subscript,
            mut_member: access_mode.mut_member(),
            arguments: vec![CallArgument {
                value: child,
                passing,
            }],
            ty: CallImplType::new(
                FnType::new(inst_fn_args, node_ty, member_ty.effects.clone()),
                CallResultConvention::Subscript(member_ty.result_convention),
            ),
        }))
    }

    /// The access to the field `field_name` of `child` when the type of `child`, known only
    /// once its uses were inferred, declares a subscript for that field: a use of that
    /// subscript, with the effects that inference gave to the access, `node_effects`. `None`
    /// if the type declares none.
    #[allow(clippy::too_many_arguments)]
    fn declared_subscript_field_access(
        &mut self,
        child: ENodeId,
        child_ty: Type,
        field_name: Ustr,
        field_span: Location,
        access_mode: SubscriptMemberKind,
        node_ty: Type,
        node_effects: &EffType,
        node_span: Location,
    ) -> Result<Option<NodeKind<Elaborated>>, InternalCompilationError> {
        let Some(field_use) = declared_field_use(
            child_ty,
            node_ty,
            field_name,
            field_span,
            self.ctx,
            &mut self.generated,
        )?
        else {
            return Ok(None);
        };
        let member = |member: &Option<SubscriptMemberType>| {
            member.as_ref().map(|member| {
                SubscriptMemberType::new(node_effects.clone(), member.result_convention)
            })
        };
        let subscript_ty = SubscriptType::new(
            vec![FnArgType::new_by_val(child_ty)],
            node_ty,
            member(&field_use.ty.ref_member),
            member(&field_use.ty.mut_member),
        );
        let subscript_node_ty = Type::subscript_type(subscript_ty.clone());
        let get_subscript = hir::GetSubscript {
            subscript: field_use.subscript,
            subscript_path: Path::new(vec![(field_name, node_span)]),
            inst_data: field_use.inst_data,
        };
        let value = self.elaborate_get_subscript(
            get_subscript,
            subscript_node_ty,
            &no_effects(),
            node_span,
        )?;
        let value = self.alloc_elaborated_node(value, subscript_node_ty, no_effects(), node_span);
        Ok(Some(self.subscript_field_access(
            value,
            &subscript_ty,
            child,
            field_name,
            access_mode,
            node_ty,
        )))
    }

    fn materialize_elaborated_place_value(
        &mut self,
        source: ENodeId,
        ty: Type,
        span: Location,
    ) -> Result<ENodeId, InternalCompilationError> {
        let effects = self.dst[source].effects.clone();
        let clone = resolve_local_clone(&mut self.generated, self.ctx, ty, span)?;
        Ok(self.alloc_elaborated_node(
            NodeKind::CloneValue(hir::CloneValue { source, clone }),
            ty,
            effects,
            span,
        ))
    }

    fn inline_yielded_binding_body(
        &mut self,
        binding: LocalDeclId,
        place: ENodeId,
        body: ENodeId,
    ) -> Result<Option<NodeKind<Elaborated>>, InternalCompilationError> {
        if matches!(&self.dst[place].kind, NodeKind::Block(_)) {
            return Ok(None);
        }
        match &self.dst[body].kind {
            NodeKind::LoadLocal(load) if load.id == binding => {
                Ok(Some(self.dst[place].kind.clone()))
            }
            NodeKind::CloneValue(clone) => match &self.dst[clone.source].kind {
                NodeKind::LoadLocal(load) if load.id == binding => {
                    Ok(Some(NodeKind::CloneValue(hir::CloneValue {
                        source: place,
                        clone: clone.clone,
                    })))
                }
                _ => Ok(None),
            },
            _ => Ok(None),
        }
    }

    fn elaborate_node_iter(
        &mut self,
        src: &UNodeArena,
        nodes: impl IntoIterator<Item = UNodeId>,
    ) -> Result<Vec<ENodeId>, InternalCompilationError> {
        let nodes = nodes.into_iter();
        let (lower, _) = nodes.size_hint();
        let mut result = Vec::with_capacity(lower);
        for node in nodes {
            result.push(self.elaborate_node(src, node)?);
        }
        Ok(result)
    }

    fn elaborate_extra_arg_kinds(
        &mut self,
        args: impl IntoIterator<Item = (NodeKind<Unelaborated>, Type, FnArgType)>,
        span: Location,
    ) -> Result<(Vec<ENodeId>, Vec<FnArgType>), InternalCompilationError> {
        let args = args.into_iter();
        let (lower, _) = args.size_hint();
        let mut nodes = Vec::with_capacity(lower);
        let mut arg_tys = Vec::with_capacity(lower);
        for (kind, ty, arg_ty) in args {
            nodes.push(self.elaborate_synthetic_node(kind, ty, no_effects(), span)?);
            arg_tys.push(arg_ty);
        }
        Ok((nodes, arg_tys))
    }

    fn elaborate_extra_args_from_inst_data(
        &mut self,
        inst_data: &hir::FnInstData,
        span: Location,
    ) -> Result<(Vec<ENodeId>, Vec<FnArgType>), InternalCompilationError> {
        let args = extra_arg_kind_from_inst_data(inst_data, span, self.ctx, &mut self.generated)?;
        self.elaborate_extra_arg_kinds(args, span)
    }

    fn elaborate_call_arguments(
        &mut self,
        src: &UNodeArena,
        arguments: &[CallArgument],
        returns_caller_rooted_place: bool,
        node_span: Location,
    ) -> Result<ElaboratedCallArguments, InternalCompilationError> {
        let mut snapshot = vec![false; arguments.len()];
        let caller_rooted_base = returns_caller_rooted_place.then(|| {
            hir::addressor_place_base_argument_index(src, arguments)
                .expect("addressor-place application should have a base argument")
        });

        let borrow_context = BorrowContext::new(self.ctx.trait_solver.others, &self.place_aliases);
        for (let_index, mutable_index) in
            hir::borrow_checker::let_arguments_overlapping_mutable(src, arguments, &borrow_context)
        {
            if caller_rooted_base == Some(let_index) {
                return Err(internal_compilation_error!(MutablePathsOverlap {
                    a_span: src[arguments[let_index].value].span,
                    b_span: src[arguments[mutable_index].value].span,
                    fn_span: node_span,
                }));
            }
            snapshot[let_index] = true;
        }

        for (let_index, _) in hir::borrow_checker::let_arguments_overlapping_later_argument_writes(
            src,
            arguments,
            &borrow_context,
        ) {
            if caller_rooted_base != Some(let_index) {
                snapshot[let_index] = true;
            }
        }

        // Resolve the complete plan before rewriting an argument. This keeps conflict
        // classification independent of elaboration traversal and allocation order.
        let mut plans = Vec::with_capacity(arguments.len());
        for (index, argument) in arguments.iter().enumerate() {
            let source = argument.value;
            let ty = src[source].ty;
            let plan = if ty == Type::never() {
                // Evaluating a `never` argument transfers control before the call. It therefore
                // needs neither a snapshot nor an owned call lifetime, even if conservative path
                // analysis happened to classify its place as overlapping.
                ArgumentLifetimePlan::Direct
            } else if snapshot[index] {
                let clone = resolve_local_clone(&mut self.generated, self.ctx, ty, node_span)?;
                let drop = if matches!(clone, ResolvedLocalClone::TrivialCopy) {
                    None
                } else {
                    Some(
                        resolve_local_drop(&mut self.generated, self.ctx, ty, node_span)?
                            .into_elaborated(),
                    )
                };
                ArgumentLifetimePlan::Snapshot { clone, drop }
            } else if argument.passing == ArgConvention::Let
                && (!hir::node_is_place_reference(src, source)
                    // A generic trait method is place-like only while type inference represents
                    // dictionary dispatch. Elaboration produces a fresh function value, so its
                    // owned environment needs the same explicit call lifetime as any rvalue.
                    || matches!(src[source].kind, NodeKind::GetTraitMethod(_)))
            {
                let drop = resolve_local_drop(&mut self.generated, self.ctx, ty, node_span)?
                    .into_elaborated();
                if drop == ResolvedLocalDrop::Skip {
                    ArgumentLifetimePlan::Direct
                } else {
                    ArgumentLifetimePlan::MaterializeOwned { drop }
                }
            } else {
                ArgumentLifetimePlan::Direct
            };
            plans.push(plan);
        }

        let mut result = Vec::with_capacity(arguments.len());
        let mut cleanup = Vec::new();
        for (argument, plan) in arguments.iter().zip(plans) {
            let source = argument.value;
            let source_node = &src[source];
            let mut value = self.elaborate_node(src, source)?;
            let drop = match plan {
                ArgumentLifetimePlan::Direct => None,
                ArgumentLifetimePlan::Snapshot { clone, drop } => {
                    value = self.alloc_elaborated_node(
                        NodeKind::CloneValue(hir::CloneValue {
                            source: value,
                            clone,
                        }),
                        source_node.ty,
                        source_node.effects.clone(),
                        source_node.span,
                    );
                    drop
                }
                ArgumentLifetimePlan::MaterializeOwned { drop } => Some(drop),
            };

            if let Some(drop) = drop {
                let (materialized, local) = self.materialize_call_value(
                    value,
                    source_node.ty,
                    &source_node.effects,
                    source_node.span,
                    node_span,
                    if matches!(plan, ArgumentLifetimePlan::Snapshot { .. }) {
                        ustr("$snapshot")
                    } else {
                        ustr("$arg")
                    },
                    drop,
                );
                value = materialized;
                cleanup.push(local);
            }

            result.push(CallArgument {
                value,
                passing: argument.passing,
            });
        }
        Ok(ElaboratedCallArguments {
            arguments: result,
            cleanup,
        })
    }

    fn wrap_call_cleanup(
        &mut self,
        call: NodeKind<Elaborated>,
        cleanup: Vec<LocalDeclId>,
        ty: Type,
        effects: &EffType,
        span: Location,
    ) -> NodeKind<Elaborated> {
        if cleanup.is_empty() {
            return call;
        }
        let call = self.alloc_elaborated_node(call, ty, effects.clone(), span);
        NodeKind::Block(b(hir::Block {
            body: b(SVec2::from_vec(vec![call])),
            cleanup,
        }))
    }

    /// Argument cleanup is introduced during elaboration. Keep it outside the consumer of an
    /// addressor's pointer; otherwise a temporary receiver is destroyed before its member is read.
    fn with_place_scope(
        &mut self,
        mut node: hir::WithPlace<Elaborated>,
        ty: Type,
        effects: &EffType,
        span: Location,
    ) -> NodeKind<Elaborated> {
        if let NodeKind::Block(mut block) = self.dst[node.place].kind.clone() {
            node.place = block.body.pop().expect("addressor block has a tail place");
            let inner = self.with_place_scope(node, ty, effects, span);
            let inner = self.alloc_elaborated_node(inner, ty, effects.clone(), span);
            block.body.push(inner);
            NodeKind::Block(block)
        } else {
            NodeKind::WithPlace(node)
        }
    }

    fn elaborate_source_kind(
        &mut self,
        src: &UNodeArena,
        old: UNodeId,
        node_ty: Type,
        node_effects: &EffType,
        node_span: Location,
    ) -> Result<NodeKind<Elaborated>, InternalCompilationError> {
        use NodeKind::*;

        Ok(match &src[old].kind {
            Immediate(value) => Immediate(value.clone()),
            Uninit => Uninit,
            BuildClosure(build_closure) => {
                let captures_value_dictionary = build_closure.captures_value_dictionary;
                let function = build_closure.function;
                let mut dictionary_captures = self
                    .elaborate_node_iter(src, build_closure.dictionary_captures.iter().copied())?;
                let mut captures =
                    self.elaborate_node_iter(src, build_closure.captures.iter().copied())?;
                let mut captures_value_dictionary = captures_value_dictionary
                    .map(|node| self.elaborate_node(src, node))
                    .transpose()?;
                let function = self.elaborate_node(src, function)?;

                let function = if let BuildClosure(inner) = &self.dst[function].kind {
                    dictionary_captures.splice(0..0, inner.dictionary_captures.iter().copied());
                    if !inner.captures.is_empty() && !captures.is_empty() {
                        panic!("Cannot flatten closures with two owned capture environments yet");
                    }
                    if captures.is_empty() {
                        captures = inner.captures.clone();
                        captures_value_dictionary = inner.captures_value_dictionary;
                    }
                    inner.function
                } else {
                    function
                };

                BuildClosure(b(hir::BuildClosure {
                    function,
                    dictionary_captures,
                    captures,
                    captures_value_dictionary,
                }))
            }
            BuildSubscriptValue(build) => {
                let mut evidence_captures =
                    self.elaborate_node_iter(src, build.evidence_captures.iter().copied())?;
                let subscript = self.elaborate_node(src, build.subscript)?;

                let subscript = if let BuildSubscriptValue(inner) = &self.dst[subscript].kind {
                    evidence_captures.splice(0..0, inner.evidence_captures.iter().copied());
                    inner.subscript
                } else {
                    subscript
                };

                BuildSubscriptValue(b(hir::BuildSubscriptValue {
                    subscript,
                    evidence_captures,
                }))
            }
            FunctionApply(app) => {
                let function_source = app.function;
                let ty = app.ty.clone();
                let snapshot_function = hir::borrow_checker::callee_overlaps_argument_writes(
                    src,
                    function_source,
                    &app.arguments,
                    &BorrowContext::new(self.ctx.trait_solver.others, &self.place_aliases),
                );

                // The function expression is evaluated before every argument. Preserve that
                // observation when a later argument may modify the same storage by cloning the
                // function value into an owned call temporary at its source position. Allocate
                // this temporary before argument temporaries so reverse cleanup order remains
                // argument(s), then function.
                let function_node = &src[function_source];
                let mut function = self.elaborate_node(src, function_source)?;
                let mut cleanup = Vec::new();
                if snapshot_function {
                    let clone = resolve_local_clone(
                        &mut self.generated,
                        self.ctx,
                        function_node.ty,
                        node_span,
                    )?;
                    let drop = resolve_local_drop(
                        &mut self.generated,
                        self.ctx,
                        function_node.ty,
                        node_span,
                    )?
                    .into_elaborated();
                    function = self.alloc_elaborated_node(
                        NodeKind::CloneValue(hir::CloneValue {
                            source: function,
                            clone,
                        }),
                        function_node.ty,
                        function_node.effects.clone(),
                        function_node.span,
                    );
                    let (materialized, local) = self.materialize_call_value(
                        function,
                        function_node.ty,
                        &function_node.effects,
                        function_node.span,
                        node_span,
                        ustr("$function_snapshot"),
                        drop,
                    );
                    function = materialized;
                    cleanup.push(local);
                }
                let arguments = self.elaborate_call_arguments(
                    src,
                    &app.arguments,
                    ty.returns_place(),
                    node_span,
                )?;
                cleanup.extend(arguments.cleanup);
                let call = FunctionApply(b(hir::FunctionApplication {
                    function,
                    arguments: arguments.arguments,
                    ty,
                }));
                self.wrap_call_cleanup(call, cleanup, node_ty, node_effects, node_span)
            }
            CloneClosureEnv(node) => {
                let source = node.source;
                CloneClosureEnv(hir::CloneClosureEnv {
                    source: self.elaborate_node(src, source)?,
                })
            }
            DropClosureEnv(node) => {
                let target = node.target;
                DropClosureEnv(hir::DropClosureEnv {
                    target: self.elaborate_node(src, target)?,
                })
            }
            CloneSubscriptValue(node) => {
                let source = node.source;
                CloneSubscriptValue(hir::CloneSubscriptValue {
                    source: self.elaborate_node(src, source)?,
                })
            }
            DropSubscriptValue(node) => {
                let target = node.target;
                DropSubscriptValue(hir::DropSubscriptValue {
                    target: self.elaborate_node(src, target)?,
                })
            }
            CloneValue(node) => {
                let source = node.source;
                let mut clone = node.clone;
                if matches!(clone, PendingLocalClone::Unknown) {
                    clone = PendingLocalClone::Resolved(resolve_local_clone(
                        &mut self.generated,
                        self.ctx,
                        node_ty,
                        node_span,
                    )?);
                }
                CloneValue(hir::CloneValue {
                    source: self.elaborate_node(src, source)?,
                    clone: clone.into_elaborated(),
                })
            }
            DropValue(node) => {
                let target = node.target;
                let mut drop = node.drop;
                if matches!(drop, PendingLocalDrop::Unknown) {
                    drop = resolve_local_drop(
                        &mut self.generated,
                        self.ctx,
                        src[target].ty,
                        node_span,
                    )?;
                }
                DropValue(hir::DropValue {
                    target: self.elaborate_node(src, target)?,
                    drop: drop.into_elaborated(),
                })
            }
            StaticApply(app) => {
                let function = app.function;
                let function_path = app.function_path.clone();
                let function_span = app.function_span;
                let argument_names = app.argument_names.clone();
                let argument_name_hint_policy = app.argument_name_hint_policy;
                let ty = app.ty.clone();
                let inst_data = app.inst_data.clone();
                let source_extra_arguments = app.extra_arguments.iter().copied();
                let mut extra_arguments = if !inst_data.dicts_req.is_empty() {
                    self.elaborate_extra_args_from_inst_data(&inst_data, function_span)?
                        .0
                } else if function.module == self.ctx.trait_solver.current_type_items.module.id
                    && let Some(requirements) = self
                        .ctx
                        .module_inst_data
                        .and_then(|inst_data| inst_data.functions.get(&function.function))
                {
                    let late_inst_data = late_module_call_inst_data(
                        requirements,
                        &inst_data,
                        self.ctx.caller_inst_data,
                        function_span,
                        node_span,
                    )?;
                    self.elaborate_extra_args_from_inst_data(&late_inst_data, node_span)?
                        .0
                } else {
                    Vec::new()
                };
                let source_extra_arguments =
                    self.elaborate_node_iter(src, source_extra_arguments)?;
                extra_arguments.extend(source_extra_arguments);
                let arguments = self.elaborate_call_arguments(
                    src,
                    &app.arguments,
                    ty.returns_place(),
                    node_span,
                )?;
                let call = StaticApply(b(StaticApplication {
                    function,
                    function_path,
                    function_span,
                    extra_arguments,
                    arguments: arguments.arguments,
                    argument_names,
                    argument_name_hint_policy,
                    ty,
                    inst_data,
                }));
                self.wrap_call_cleanup(call, arguments.cleanup, node_ty, node_effects, node_span)
            }
            SubscriptApply(app) => {
                let subscript = app.subscript;
                let mut_member = app.mut_member;
                let ty = app.ty.clone();
                let arguments = self.elaborate_call_arguments(
                    src,
                    &app.arguments,
                    ty.returns_place(),
                    node_span,
                )?;
                let call = SubscriptApply(b(hir::SubscriptApplication {
                    subscript: self.elaborate_node(src, subscript)?,
                    mut_member,
                    arguments: arguments.arguments,
                    ty,
                }));
                self.wrap_call_cleanup(call, arguments.cleanup, node_ty, node_effects, node_span)
            }
            TraitMethodApply(app) => {
                let trait_id = app.trait_id;
                let method_index = app.method_index;
                let method_path = app.method_path.clone();
                let method_span = app.method_span;
                let arguments_unnamed = app.arguments_unnamed;
                let ty = app.ty.clone();
                let input_tys = app.input_tys.clone();
                let output_tys = app.output_tys.clone();
                let output_effs = app.output_effs.clone();
                let inst_data = app.inst_data.clone();
                assert!(
                    inst_data.dicts_req.is_empty(),
                    "Instantiation data for trait method is not supported yet."
                );
                // Even a concrete selected implementation can be a dictionary constructor.
                // Uniform dictionary projection preserves its hidden evidence; capture-free
                // dictionaries remain symbolic constants and optimize back to direct calls.
                let (is_value_function, argument_names) = {
                    let trait_def = self.ctx.trait_solver.trait_def(trait_id);
                    let definition = &trait_def.method(method_index).1;
                    (
                        is_value_trait_for_function_type(trait_id, trait_def, &input_tys, &[]),
                        definition.arg_names.clone(),
                    )
                };
                let arguments = self.elaborate_call_arguments(
                    src,
                    &app.arguments,
                    ty.returns_place(),
                    node_span,
                )?;
                let call = if is_value_function {
                    let function = FunctionId::new(
                        self.ctx.trait_solver.current_type_items.module.id,
                        function_value_method(self.ctx.trait_solver, method_index, method_span)?,
                    );
                    StaticApply(b(hir::StaticApplication {
                        function,
                        function_path: Some(method_path),
                        function_span: method_span,
                        extra_arguments: Vec::new(),
                        arguments: arguments.arguments,
                        argument_names,
                        argument_name_hint_policy: arguments_unnamed,
                        ty,
                        inst_data: hir::FnInstData::none(),
                    }))
                } else {
                    let (dict_kind, dict_ty) = trait_dictionary_node_kind(
                        &mut self.generated,
                        trait_id,
                        &input_tys,
                        &output_tys,
                        &output_effs,
                        method_span,
                        self.ctx,
                    )?;
                    let dictionary = self.elaborate_synthetic_node(
                        dict_kind,
                        dict_ty,
                        no_effects(),
                        method_span,
                    )?;
                    let (entry_index, _) = dictionary_method_projection_data(
                        self.ctx.trait_solver.trait_def(trait_id),
                        dict_ty,
                        method_index,
                    );
                    call_dictionary_function(
                        dictionary,
                        entry_index,
                        arguments.arguments,
                        argument_names,
                        ty,
                        Some(output_effs),
                    )
                };
                self.wrap_call_cleanup(call, arguments.cleanup, node_ty, node_effects, node_span)
            }
            GetFunction(get_fn) => {
                let mut get_fn = (**get_fn).clone();
                let captures = if !get_fn.inst_data.dicts_req.is_empty() {
                    let (captures, _) =
                        self.elaborate_extra_args_from_inst_data(&get_fn.inst_data, node_span)?;
                    get_fn.inst_data.dicts_req.clear();
                    captures
                } else if get_fn.function.module
                    == self.ctx.trait_solver.current_type_items.module.id
                {
                    if let Some(requirements) = self
                        .ctx
                        .module_inst_data
                        .and_then(|inst_data| inst_data.functions.get(&get_fn.function.function))
                        .filter(|inst_data| !inst_data.requirements.is_empty())
                    {
                        let late_inst_data = late_module_call_inst_data(
                            requirements,
                            &get_fn.inst_data,
                            self.ctx.caller_inst_data,
                            get_fn.function_span,
                            node_span,
                        )?;
                        self.elaborate_extra_args_from_inst_data(&late_inst_data, node_span)?
                            .0
                    } else {
                        Vec::new()
                    }
                } else {
                    Vec::new()
                };
                if captures.is_empty() {
                    GetFunction(b(get_fn))
                } else {
                    let function = self.alloc_elaborated_node(
                        GetFunction(b(get_fn)),
                        node_ty,
                        node_effects.clone(),
                        node_span,
                    );
                    BuildClosure(b(hir::BuildClosure {
                        function,
                        dictionary_captures: captures,
                        captures: Vec::new(),
                        captures_value_dictionary: None,
                    }))
                }
            }
            GetSubscript(get_subscript) => self.elaborate_get_subscript(
                (**get_subscript).clone(),
                node_ty,
                node_effects,
                node_span,
            )?,
            GetTraitMethod(get_method) => {
                let trait_id = get_method.trait_id;
                let method_index = get_method.method_index;
                let method_path = get_method.method_path.clone();
                let method_span = get_method.method_span;
                assert!(
                    get_method.inst_data.dicts_req.is_empty(),
                    "Instantiation data for trait method is not supported yet."
                );
                let input_tys = get_method.input_tys.clone();
                let output_tys = get_method.output_tys.clone();
                let output_effs = get_method.output_effs.clone();
                let is_value_function = {
                    let trait_def = self.ctx.trait_solver.trait_def(trait_id);
                    is_value_trait_for_function_type(trait_id, trait_def, &input_tys, &output_tys)
                };
                if is_value_function {
                    let function = FunctionId::new(
                        self.ctx.trait_solver.current_type_items.module.id,
                        function_value_method(self.ctx.trait_solver, method_index, method_span)?,
                    );
                    GetFunction(b(hir::GetFunction {
                        function,
                        function_path: method_path,
                        function_span: method_span,
                        inst_data: hir::FnInstData::none(),
                    }))
                } else {
                    let (dict_ty, entry_index) = {
                        let trait_def = self.ctx.trait_solver.trait_def(trait_id);
                        let dict_ty = trait_def.get_dictionary_type_for_tys(
                            &input_tys,
                            &output_tys,
                            &output_effs,
                        );
                        let (entry_index, _) =
                            dictionary_method_projection_data(trait_def, dict_ty, method_index);
                        (dict_ty, entry_index)
                    };
                    let (dict_kind, _) = trait_dictionary_node_kind(
                        &mut self.generated,
                        trait_id,
                        &input_tys,
                        &output_tys,
                        &output_effs,
                        method_span,
                        self.ctx,
                    )?;
                    let dictionary = self.elaborate_synthetic_node(
                        dict_kind,
                        dict_ty,
                        no_effects(),
                        method_span,
                    )?;
                    GetDictionaryFunction(hir::GetDictionaryFunction {
                        dictionary,
                        entry_index,
                    })
                }
            }
            GetTraitAssociatedConst(get_const) => {
                let trait_id = get_const.trait_id;
                let associated_const_index = get_const.associated_const_index;
                let associated_const_span = get_const.associated_const_span;
                let input_tys = get_const.input_tys.clone();
                let output_tys = get_const.output_tys.clone();
                let is_compiler_value_application = {
                    let trait_def = self.ctx.trait_solver.trait_def(trait_id);
                    is_value_trait_for_function_type(trait_id, trait_def, &input_tys, &output_tys)
                        || is_function_surface_only_value_trait_application(
                            trait_id,
                            trait_def,
                            &input_tys,
                            &output_tys,
                        )
                };
                if is_compiler_value_application {
                    let values = value_layout_associated_const_values(
                        input_tys[0],
                        node_span,
                        self.ctx.trait_solver,
                    )?;
                    Immediate(LiteralValue::new_native(
                        values[usize::from(associated_const_index)],
                    ))
                } else {
                    let (dict_kind, dict_ty) = trait_dictionary_node_kind(
                        &mut self.generated,
                        trait_id,
                        &input_tys,
                        &output_tys,
                        &[],
                        associated_const_span,
                        self.ctx,
                    )?;
                    let dictionary = self.elaborate_synthetic_node(
                        dict_kind,
                        dict_ty,
                        no_effects(),
                        associated_const_span,
                    )?;
                    call_dictionary_function(
                        dictionary,
                        self.ctx
                            .trait_solver
                            .trait_def(trait_id)
                            .dictionary_associated_const_index(associated_const_index),
                        Vec::new(),
                        Vec::new(),
                        CallImplType::value(FnType::new_by_val([], node_ty, no_effects())),
                        None,
                    )
                }
            }
            GetTraitDictionary(get_dict) => {
                let input_tys = get_dict.input_tys.clone();
                let output_tys = get_dict.output_tys.clone();
                let output_effs = get_dict.output_effs.clone();
                let (node_kind, _) = trait_dictionary_node_kind(
                    &mut self.generated,
                    get_dict.trait_id,
                    &input_tys,
                    &output_tys,
                    &output_effs,
                    node_span,
                    self.ctx,
                )?;
                self.elaborate_synthetic_kind(node_kind, node_ty, node_effects, node_span)?
            }
            GetDictionary(get_dict) => GetDictionary(hir::GetDictionary {
                dictionary: get_dict.dictionary,
                captures: get_dict
                    .captures
                    .iter()
                    .map(|capture| self.elaborate_node(src, *capture))
                    .collect::<Result<_, _>>()?,
            }),
            LoadDictionary(load) => LoadDictionary(*load),
            LoadSubscriptEvidence(load) => LoadSubscriptEvidence(*load),
            LoadVariantPayloadStorageEvidence(load) => LoadVariantPayloadStorageEvidence(*load),
            StoreLocal(store) => {
                let value = store.value;
                let id = store.id;
                StoreLocal(hir::StoreLocal {
                    value: self.elaborate_node(src, value)?,
                    id,
                })
            }
            TakeLocalValue(node) => {
                let id = node.id;
                let mut mode = node.mode;
                if matches!(mode, PendingTakeLocalValueMode::Unknown) {
                    mode = if self.locals[id.as_index()].owns_storage() {
                        PendingTakeLocalValueMode::MoveOwned
                    } else {
                        PendingTakeLocalValueMode::CloneBorrowed(resolve_local_clone(
                            &mut self.generated,
                            self.ctx,
                            node_ty,
                            node_span,
                        )?)
                    };
                }
                TakeLocalValue(hir::TakeLocalValue {
                    id,
                    mode: mode.into_elaborated(),
                })
            }
            LoadLocal(load) => LoadLocal(*load),
            GetDictionaryFunction(node) => {
                let dictionary = node.dictionary;
                let entry_index = node.entry_index;
                GetDictionaryFunction(hir::GetDictionaryFunction {
                    dictionary: self.elaborate_node(src, dictionary)?,
                    entry_index,
                })
            }
            CallDictionaryFunction(call) => {
                let dictionary = call.dictionary;
                let entry_index = call.entry_index;
                let ty = call.ty.clone();
                let output_effs = call.output_effs.clone();
                let arguments = self.elaborate_call_arguments(
                    src,
                    &call.arguments,
                    ty.returns_place(),
                    node_span,
                )?;
                let call = CallDictionaryFunction(b(hir::CallDictionaryFunction {
                    dictionary: self.elaborate_node(src, dictionary)?,
                    entry_index,
                    arguments: arguments.arguments,
                    argument_names: call.argument_names.clone(),
                    ty,
                    output_effs,
                }));
                self.wrap_call_cleanup(call, arguments.cleanup, node_ty, node_effects, node_span)
            }
            Return(node) => {
                let value = self.elaborate_node(src, *node)?;
                self.transfer_value(value, TransferTarget::Return, 0, node_span)?
            }
            Block(block) => {
                let cleanup = block.cleanup.clone();
                let mut body = Vec::with_capacity(block.body.len());
                for (index, node) in block.body.iter().copied().enumerate() {
                    body.push(self.elaborate_node(src, node)?);
                    if src[node].ty == Type::never()
                        && !node_contains_yield(src, node)
                        && let Some(location) = Location::fuse(
                            block
                                .body
                                .iter()
                                .skip(index + 1)
                                .map(|node| src[*node].span)
                                .filter(|location| !location.is_synthesized()),
                        )
                    {
                        self.warnings
                            .push(CompilationWarning::unreachable_code(location));
                        break;
                    }
                }
                Block(b(hir::Block {
                    body: b(SVec2::from_vec(body)),
                    cleanup,
                }))
            }
            Assign(assignment) => {
                let place = assignment.place;
                let value = assignment.value;
                let mut drop = assignment.drop;
                let place_ty = src[place].ty;
                if let Some(drop) = &mut drop
                    && matches!(drop, PendingLocalDrop::Unknown)
                {
                    *drop = resolve_local_drop(&mut self.generated, self.ctx, place_ty, node_span)?;
                }
                Assign(hir::Assignment {
                    place: self.elaborate_node(src, place)?,
                    value: self.elaborate_node(src, value)?,
                    drop: drop.map(|drop| drop.into_elaborated()),
                })
            }
            PendingAssignment(_) => unreachable!("assignment preparation precedes HIR elaboration"),
            Tuple(nodes) => {
                self.ensure_product_layout_evidence(node_ty, node_span)?;
                self.elaborate_construction(src, old, nodes, Tuple, ConstructionStorage::Inline)?
            }
            Project(project) => {
                let value = project.value;
                let index = project.index;
                if project.variant_payload {
                    self.ensure_value_layout_evidence(node_ty, node_span)?;
                } else {
                    self.ensure_product_layout_evidence(src[value].ty, node_span)?;
                }
                Project(hir::Project {
                    value: self.elaborate_node(src, value)?,
                    index,
                    variant_payload: project.variant_payload,
                })
            }
            Record(nodes) => {
                self.ensure_product_layout_evidence(node_ty, node_span)?;
                self.elaborate_construction(src, old, nodes, Record, ConstructionStorage::Inline)?
            }
            FieldAccess(field_access) => {
                use TypeKind::*;
                let child_id = field_access.value;
                let field_name = field_access.field;
                let child = self.elaborate_node(src, child_id)?;
                let child_ty = src[child_id].ty;
                self.ensure_product_layout_evidence(child_ty, node_span)?;
                let ty_data = child_ty.data();
                let ty_data = if let Some(named) = ty_data.as_named() {
                    let named = named.clone();
                    drop(ty_data);
                    self.ctx
                        .trait_solver
                        .type_def(named.def)
                        .instantiated_shape_with_effects(&named.params, &named.effect_params)
                        .data()
                } else {
                    ty_data
                };
                // What the field is, by the rule that inference followed when it answered
                // the requirement of the access, see `ProjectionSubscriptIs`: the evidence of
                // a type that is still open, or that the function was given for this type;
                // else, where the access accepts one, the subscript that the type declares;
                // else a place of the product.
                let open = ty_data.as_variable().copied();
                let stored = match &*ty_data {
                    Tuple(fields) => {
                        let index = field_name.as_str().parse::<usize>().ok();
                        assert!(
                            index.is_none_or(|index| index < fields.len()),
                            "tuple field must have been checked by inference"
                        );
                        index
                    }
                    Record(record) => record.iter().position(|field| field.0 == field_name),
                    _ => None,
                };
                drop(ty_data);
                let access_mode = field_access.access_mode;
                let given = match open {
                    Some(var) => Some(
                        find_projection_subscript_dict_index(self.ctx.dicts, var, &field_name)
                            .unwrap_or_else(
                                || panic!("Projection subscript dictionary for field \"{field_name}\" in type variable \"{var}\" not found, type inference should have failed"),
                            ),
                    ),
                    None => find_projection_subscript_dict_index_for_receiver_ty(
                        self.ctx.dicts,
                        child_ty,
                        &field_name,
                    ),
                };
                if let Some(index) = given {
                    self.projection_evidence_field_access(
                        child,
                        field_name,
                        access_mode,
                        index,
                        node_ty,
                        node_span,
                    )
                } else if field_access.requirement.accepts_user_defined_projection()
                    && let Some(access) = self.declared_subscript_field_access(
                        child,
                        child_ty,
                        field_name,
                        field_access.field_span,
                        access_mode,
                        node_ty,
                        node_effects,
                        node_span,
                    )?
                {
                    access
                } else if let Some(index) = stored {
                    Project(HirProject::new(child, ProjectionIndex::from_index(index)))
                } else {
                    panic!("Field not found in type, type inference should have failed");
                }
            }
            Variant(variant) => {
                let payload_ty = src[variant.payload].ty;
                self.ensure_value_layout_evidence(payload_ty, node_span)?;
                let payload_storage = if matches!(&*node_ty.data(), TypeKind::Variable(_)) {
                    let index = find_variant_payload_indirection_index(
                        self.ctx.dicts,
                        node_ty,
                        variant.tag,
                    )
                    .ok_or_else(|| {
                        internal_compilation_error!(Internal {
                            error: format!(
                                "variant payload-indirection evidence for type {node_ty:?} and case .{} not found for generic construction",
                                variant.tag
                            ),
                            span: node_span,
                        })
                    })?;
                    VariantPayloadStorageSource::Evidence(EvidenceBindingId::from_index(index))
                } else {
                    VariantPayloadStorageSource::Static(variant_payload_storage_for_type(
                        node_ty,
                        variant.tag,
                        node_span,
                        self.ctx.trait_solver,
                    )?)
                };
                let mut payload = self.elaborate_node(src, variant.payload)?;
                // A custom destructor only accepts complete receivers. Stage interruptible
                // payloads before publishing the shell; the local owns any partial construction.
                let custom_drop = matches!(&*node_ty.data(), TypeKind::Named(named)
                    if self.ctx.trait_solver.type_def(named.def).has_custom_value_impl);
                let staged = if custom_drop
                    && payload_ty != Type::unit()
                    && can_interrupt(src, variant.payload)
                {
                    let drop =
                        resolve_local_drop(&mut self.generated, self.ctx, payload_ty, node_span)?
                            .into_elaborated();
                    let local = self.push_owned_temp(payload_ty, drop, node_span, ustr("$payload"));
                    let store = self.alloc_elaborated_node(
                        StoreLocal(hir::StoreLocal {
                            value: payload,
                            id: local,
                        }),
                        Type::unit(),
                        src[variant.payload].effects.clone(),
                        node_span,
                    );
                    payload = self.alloc_elaborated_node(
                        TakeLocalValue(hir::TakeLocalValue {
                            id: local,
                            mode: ResolvedTakeLocalValueMode::MoveOwned,
                        }),
                        payload_ty,
                        no_effects(),
                        node_span,
                    );
                    Some((local, store))
                } else {
                    None
                };
                let construction = Variant(hir::Variant {
                    tag: variant.tag,
                    payload,
                    payload_storage: Some(payload_storage),
                });
                if let Some((local, store)) = staged {
                    let value =
                        self.alloc_elaborated_node(construction, node_ty, no_effects(), node_span);
                    Block(b(hir::Block {
                        body: b(SVec2::from_vec(vec![store, value])),
                        cleanup: vec![local],
                    }))
                } else {
                    construction
                }
            }
            Array(nodes) => {
                // Buffer allocation needs the whole element layout, not just its generic leaves.
                if let Some(element) = nodes.first() {
                    self.ensure_value_layout_evidence(src[*element].ty, node_span)?;
                }
                self.elaborate_construction(
                    src,
                    old,
                    nodes,
                    Array,
                    ConstructionStorage::AllocatedFirst,
                )?
            }
            Case(case) => {
                let value = case.value;
                let default = case.default;
                let mut alternatives = Vec::with_capacity(case.alternatives.len());
                for (literal, node) in &case.alternatives {
                    alternatives.push((literal.clone(), self.elaborate_node(src, *node)?));
                }
                Case(b(hir::Case {
                    value: self.elaborate_node(src, value)?,
                    alternatives,
                    default: self.elaborate_node(src, default)?,
                }))
            }
            Loop(node) => {
                let label = self.fresh_loop_id();
                let failing_projections = self.failing_projections.len();
                self.loops.insert(
                    node.label,
                    ElaboratedLoop {
                        label,
                        failing_projections,
                    },
                );
                Loop(hir::Loop {
                    label,
                    body: self.elaborate_node(src, node.body)?,
                })
            }
            Break(node) => {
                let value = self.elaborate_node(src, node.value)?;
                let target = self.loops[&node.label];
                self.transfer_value(
                    value,
                    TransferTarget::Break(target.label),
                    target.failing_projections,
                    node_span,
                )?
            }
            Continue(node) => Continue(hir::Continue {
                label: self.loops[&node.label].label,
            }),
            Yield(node) => Yield(self.elaborate_node(src, *node)?),
            WithYielded(node) => {
                let accessor = self.elaborate_node(src, node.accessor)?;
                // The accessor's slide runs after the body. If it can fail, values leaving the
                // body, as its result or through a transfer, stay owned until it has run.
                let slide_may_fail = !elaborated_node_is_place_reference(self.dst, accessor)
                    && !self.dst[accessor].effects.cannot_fail();
                if slide_may_fail {
                    self.failing_projections.push(FailingProjection::default());
                }
                let previous = self.place_aliases.insert(node.binding, node.accessor);
                let body = self.elaborate_node(src, node.body);
                let exits = slide_may_fail.then(|| self.failing_projections.pop().unwrap());
                if let Some(previous) = previous {
                    self.place_aliases.insert(node.binding, previous);
                } else {
                    self.place_aliases.remove(&node.binding);
                }
                let body = body?;
                // A generic yielded projection may resolve to a concrete direct
                // projection or addressor-place call. In either case the
                // elaborated accessor already produces a place and needs no
                // suspended yielded-accessor protocol.
                if elaborated_node_is_place_reference(self.dst, accessor) {
                    if let Some(inlined) =
                        self.inline_yielded_binding_body(node.binding, accessor, body)?
                    {
                        inlined
                    } else {
                        self.with_place_scope(
                            hir::WithPlace {
                                place: accessor,
                                binding: node.binding,
                                body,
                                access: node.access,
                            },
                            node_ty,
                            node_effects,
                            node_span,
                        )
                    }
                } else {
                    let mut body = body;
                    if elaborated_node_is_place_reference(self.dst, body) {
                        body = self.materialize_elaborated_place_value(body, node_ty, node_span)?;
                    }
                    let projection = hir::WithYielded {
                        accessor,
                        binding: node.binding,
                        body,
                        access: node.access,
                    };
                    match exits {
                        Some(exits) => self.elaborate_failing_projection(
                            projection,
                            exits,
                            node_ty,
                            node_effects,
                            node_span,
                        )?,
                        None => WithYielded(projection),
                    }
                }
            }
            WithPlace(node) => {
                let place = self.elaborate_node(src, node.place)?;
                let previous = self.place_aliases.insert(node.binding, node.place);
                let body = self.elaborate_node(src, node.body);
                if let Some(previous) = previous {
                    self.place_aliases.insert(node.binding, previous);
                } else {
                    self.place_aliases.remove(&node.binding);
                }
                let body = body?;
                self.with_place_scope(
                    hir::WithPlace {
                        place,
                        binding: node.binding,
                        body,
                        access: node.access,
                    },
                    node_ty,
                    node_effects,
                    node_span,
                )
            }
            CheckCallDepth => CheckCallDepth,
            CheckFuel => CheckFuel,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        FxHashMap, Location, Modules, SourceId,
        containers::b,
        hir::{
            GetTraitAssociatedConst,
            dictionary::ExtraParameters,
            function::{CallableDefinition, Function},
            value::LiteralValue,
        },
        module::{
            CurrentTypeItems, FunctionCollector, LocalDecl, LocalTraitId, Module, ModuleId, Path,
            PendingFunctionCollector, PendingGeneratedStructuralProjectionSubscripts,
            QualifiedNameEnv, TraitId, TraitImpls, id::Id,
        },
        std::math::int_type,
        types::{
            effects::{EffectVar, PrimitiveEffect},
            r#trait::{Trait, TraitAssociatedConst, TraitAssociatedConstIndex},
            trait_solver::{CurrentProjectionSubscriptTypes, TraitSolver},
            r#type::Type,
        },
    };

    fn extra_parameters(requirements: Vec<DictionaryReq>) -> ExtraParameters {
        ExtraParameters {
            requirements,
            repr_map: FxHashMap::default(),
        }
    }

    fn late_data(
        requirements: Vec<DictionaryReq>,
        ty_origins: Vec<TypeVar>,
        effect_origins: Vec<EffectVar>,
    ) -> LateFunctionInstData {
        LateFunctionInstData {
            requirements: extra_parameters(requirements),
            ty_origins,
            effect_origins,
            effects_per_reference: false,
            reference_effects: FxHashMap::default(),
        }
    }

    #[test]
    fn late_call_maps_callee_types_to_the_caller_by_their_origins() {
        // The callee numbers the two types in the opposite order, and has one of its own.
        let (first, second, own) = (TypeVar::new(40), TypeVar::new(41), TypeVar::new(42));
        let requirement = |variant: u32, payload: u32| {
            DictionaryReq::new_variant_payload_indirection(
                Type::variable(TypeVar::new(variant)),
                ustr("Some"),
                Type::variable(TypeVar::new(payload)),
            )
        };
        let callee = late_data(
            vec![requirement(0, 1), requirement(2, 2)],
            vec![second, first, own],
            Vec::new(),
        );
        let caller = late_data(Vec::new(), vec![first, second], Vec::new());
        let span = Location::new_synthesized();
        let inst_data = late_module_call_inst_data(
            &callee,
            &hir::FnInstData::none(),
            Some(&caller),
            span,
            span,
        )
        .unwrap();
        assert!(inst_data.dicts_req[0].same_contract(&requirement(1, 0)));
        assert!(inst_data.dicts_req[1].same_contract(
            &DictionaryReq::new_variant_payload_indirection(
                Type::never(),
                ustr("Some"),
                Type::never(),
            )
        ));
    }

    #[test]
    fn late_call_gives_callee_effects_by_their_origins_or_as_recorded() {
        let callback = |effect: EffType| {
            Type::function_type(FnType::new_by_val(Vec::<Type>::new(), Type::unit(), effect))
        };
        let variable = |index: u32| EffType::single_variable(EffectVar::new(index));
        let requirement = |first: EffType, second: EffType| {
            DictionaryReq::new_variant_payload_indirection(
                callback(first),
                ustr("Some"),
                callback(second),
            )
        };
        // The callee numbers the two effects in the opposite order, and has one of its own.
        let (first, second, own) = (EffectVar::new(40), EffectVar::new(41), EffectVar::new(42));
        let mut callee = late_data(
            vec![
                requirement(variable(0), variable(1)),
                requirement(variable(2), variable(2)),
            ],
            Vec::new(),
            vec![second, first, own],
        );
        let mut caller = late_data(Vec::new(), Vec::new(), vec![first, second]);
        let span = Location::new_synthesized();
        let none = hir::FnInstData::none();

        let shared = late_module_call_inst_data(&callee, &none, Some(&caller), span, span).unwrap();
        assert!(shared.dicts_req[0].same_contract(&requirement(variable(1), variable(0))));
        assert!(
            shared.dicts_req[1].same_contract(&requirement(EffType::empty(), EffType::empty()))
        );

        // A function with effects per reference takes those recorded for the site, and no other.
        callee.effects_per_reference = true;
        assert!(late_module_call_inst_data(&callee, &none, Some(&caller), span, span).is_err());
        let write = EffType::single_primitive(PrimitiveEffect::Write);
        caller
            .reference_effects
            .insert(span, vec![variable(0), write.clone(), EffType::empty()]);
        let recorded =
            late_module_call_inst_data(&callee, &none, Some(&caller), span, span).unwrap();
        assert!(recorded.dicts_req[0].same_contract(&requirement(variable(0), write)));
    }

    fn layout_trait() -> Trait {
        Trait::new_with_self_input_type(
            "Layout",
            "Compiler-only layout metadata.",
            Vec::<&str>::new(),
            Vec::<(&str, CallableDefinition)>::new(),
        )
        .with_associated_consts([
            TraitAssociatedConst::new("SIZE", Type::primitive::<isize>(), "Size in bytes."),
            TraitAssociatedConst::new("ALIGN", Type::primitive::<isize>(), "Alignment in bytes."),
        ])
    }

    #[test]
    fn final_elaboration_prunes_suffix_after_late_never_substitution() {
        let source_id = SourceId::from_index(1);
        let live_span = Location::new(0, 6, source_id);
        let dead_span = Location::new(8, 11, source_id);
        let other_dead_span = Location::new(13, 17, source_id);
        let block_span = Location::new(0, 17, source_id);
        let mut arena = NodeArena::default();
        // This models a node whose type became Never only when final substitutions were applied.
        let diverging = arena.alloc(Node::new(
            NodeKind::Immediate(LiteralValue::new_native(())),
            Type::never(),
            no_effects(),
            live_span,
        ));
        let dead = arena.alloc(Node::new(
            NodeKind::Immediate(LiteralValue::new_native(999isize)),
            int_type(),
            no_effects(),
            dead_span,
        ));
        let other_dead = arena.alloc(Node::new(
            NodeKind::Immediate(LiteralValue::new_native(1000isize)),
            int_type(),
            no_effects(),
            other_dead_span,
        ));
        let root = arena.alloc(Node::new(
            NodeKind::Block(b(hir::Block {
                body: b(SVec2::from_vec(vec![diverging, dead, other_dead])),
                cleanup: Vec::new(),
            })),
            Type::never(),
            no_effects(),
            block_span,
        ));

        let modules = Modules::new();
        let current_module = Module::new(ModuleId::new(0), Path::single_str("$elaboration_test"));
        let mut impls = TraitImpls::new(ModuleId::new(0));
        let mut deps = FxHashSet::default();
        let mut solver = TraitSolver::new(
            CurrentTypeItems::new_from_module(&current_module),
            &mut impls,
            &current_module.def_table,
            &mut deps,
            CurrentProjectionSubscriptTypes::empty(),
            PendingFunctionCollector::new(0),
            &modules,
        );
        let dicts = ExtraParameters {
            requirements: vec![],
            repr_map: FxHashMap::default(),
        };
        let generated_projection_subscripts =
            PendingGeneratedStructuralProjectionSubscripts::new(&current_module);
        let mut ctx = DictElaborationCtx::new_with_generated_projection_subscripts(
            &dicts,
            None,
            &mut solver,
            generated_projection_subscripts,
        );
        let mut elaborated_arena = ENodeArena::default();
        let mut warnings = Vec::new();

        let elaborated = elaborate_hir_with_warnings(
            &mut arena,
            root,
            &mut elaborated_arena,
            &mut ctx,
            Vec::new(),
            &mut warnings,
        )
        .unwrap();

        let NodeKind::Block(block) = &elaborated_arena[elaborated.root].kind else {
            panic!("expected elaborated block");
        };
        assert_eq!(block.body.len(), 1);
        assert_eq!(
            warnings,
            vec![CompilationWarning::unreachable_code(Location::new(
                dead_span.start(),
                other_dead_span.end(),
                source_id,
            ))]
        );
    }

    fn get_associated_const_node(
        trait_id: TraitId,
        trait_def: &Trait,
        associated_const_index: TraitAssociatedConstIndex,
        input_tys: Vec<Type>,
    ) -> NodeKind {
        NodeKind::GetTraitAssociatedConst(b(GetTraitAssociatedConst {
            associated_const_name: trait_def.associated_const(associated_const_index).name,
            associated_const_span: Location::new_synthesized(),
            trait_id,
            associated_const_index,
            input_tys,
            output_tys: vec![],
            output_effs: vec![],
        }))
    }

    #[test]
    fn concrete_associated_const_elaborates_to_closed_dictionary_getter_call() {
        let traits = vec![layout_trait()];
        let trait_def = &traits[0];
        let trait_id = TraitId::new(ModuleId::new(0), LocalTraitId::new(0));
        let mut arena = NodeArena::default();
        let span = Location::new_synthesized();
        let node = arena.alloc(Node::new(
            get_associated_const_node(
                trait_id,
                trait_def,
                TraitAssociatedConstIndex::from_index(0),
                vec![Type::unit()],
            ),
            int_type(),
            no_effects(),
            span,
        ));

        let modules = Modules::new();
        let mut current_module =
            Module::new(ModuleId::new(0), Path::single_str("$elaboration_test"));
        current_module.traits = traits.clone();
        let qualified_name_env = QualifiedNameEnv::new_from_module(&current_module, &modules);
        let mut impls = TraitImpls::new(ModuleId::new(0));
        let mut fn_collector = FunctionCollector::new(0);
        let mut getter_arena = ENodeArena::default();
        impls.add_concrete_raw(
            trait_id,
            trait_def,
            [Type::unit()],
            [],
            [],
            [
                LiteralValue::new_native(8isize),
                LiteralValue::new_native(4isize),
            ],
            Vec::<(Function, Vec<LocalDecl>)>::new(),
            &mut getter_arena,
            &mut fn_collector,
            &qualified_name_env,
        );
        let mut deps = FxHashSet::default();
        let mut solver = TraitSolver::new(
            CurrentTypeItems::new_from_module(&current_module),
            &mut impls,
            &current_module.def_table,
            &mut deps,
            CurrentProjectionSubscriptTypes::empty(),
            PendingFunctionCollector::new(0),
            &modules,
        );
        let dicts = ExtraParameters {
            requirements: vec![],
            repr_map: FxHashMap::default(),
        };
        let generated_projection_subscripts =
            PendingGeneratedStructuralProjectionSubscripts::new(&current_module);
        let mut ctx = DictElaborationCtx::new_with_generated_projection_subscripts(
            &dicts,
            None,
            &mut solver,
            generated_projection_subscripts,
        );

        let mut elaborated_arena = ENodeArena::default();
        let elaborated = elaborate_hir(
            &mut arena,
            node,
            &mut elaborated_arena,
            &mut ctx,
            Vec::new(),
        )
        .unwrap();

        let NodeKind::CallDictionaryFunction(call) = &elaborated_arena[elaborated.root].kind else {
            panic!("expected associated const to elaborate to a dictionary getter call");
        };
        assert!(call.arguments.is_empty());
        assert_eq!(usize::from(call.entry_index), 0);
        let NodeKind::GetDictionary(dictionary) = &elaborated_arena[call.dictionary].kind else {
            panic!("expected dictionary getter source to construct a closed dictionary");
        };
        assert!(dictionary.captures.is_empty());
    }

    #[test]
    fn generic_associated_const_elaborates_to_dictionary_getter_call() {
        let traits = vec![layout_trait()];
        let trait_def = &traits[0];
        let trait_id = TraitId::new(ModuleId::new(0), LocalTraitId::new(0));
        let input_ty = Type::variable_id(0);
        let mut arena = NodeArena::default();
        let span = Location::new_synthesized();
        let node = arena.alloc(Node::new(
            get_associated_const_node(
                trait_id,
                trait_def,
                TraitAssociatedConstIndex::from_index(1),
                vec![input_ty],
            ),
            int_type(),
            no_effects(),
            span,
        ));

        let mut impls = TraitImpls::new(ModuleId::new(0));
        let modules = Modules::new();
        let mut current_module =
            Module::new(ModuleId::new(0), Path::single_str("$elaboration_test"));
        current_module.traits = traits.clone();
        let mut deps = FxHashSet::default();
        let mut solver = TraitSolver::new(
            CurrentTypeItems::new_from_module(&current_module),
            &mut impls,
            &current_module.def_table,
            &mut deps,
            CurrentProjectionSubscriptTypes::empty(),
            PendingFunctionCollector::new(0),
            &modules,
        );
        let dicts = ExtraParameters {
            requirements: vec![DictionaryReq::new_trait_impl(
                trait_id,
                vec![input_ty],
                vec![],
                vec![],
            )],
            repr_map: FxHashMap::default(),
        };
        let generated_projection_subscripts =
            PendingGeneratedStructuralProjectionSubscripts::new(&current_module);
        let mut ctx = DictElaborationCtx::new_with_generated_projection_subscripts(
            &dicts,
            None,
            &mut solver,
            generated_projection_subscripts,
        );

        let mut elaborated_arena = ENodeArena::default();
        let elaborated = elaborate_hir(
            &mut arena,
            node,
            &mut elaborated_arena,
            &mut ctx,
            Vec::new(),
        )
        .unwrap();

        let NodeKind::CallDictionaryFunction(call) = &elaborated_arena[elaborated.root].kind else {
            panic!("expected associated const to elaborate to a dictionary getter call");
        };
        assert!(call.arguments.is_empty());
        assert_eq!(usize::from(call.entry_index), 1);
        let NodeKind::LoadDictionary(load) = &elaborated_arena[call.dictionary].kind else {
            panic!("expected dictionary getter source to load a dictionary");
        };
        assert_eq!(load.extra_parameter.as_index(), 0);
    }
}
