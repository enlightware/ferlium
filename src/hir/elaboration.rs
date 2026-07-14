// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{FxHashMap, FxHashSet, Modules};
use ustr::{Ustr, ustr};

use crate::{
    Location,
    compiler::error::InternalCompilationError,
    hir::hir_syn::get_dictionary,
    hir::{
        dictionary::{
            DictElaborationCtx, DictionariesReq, DictionaryReq, ExtraParameters,
            find_projection_subscript_dict_index,
            find_projection_subscript_dict_index_for_receiver_ty, find_trait_impl_dict_index,
        },
        value_dispatch::{resolve_local_clone, resolve_local_drop},
    },
    internal_compilation_error,
    module::{
        ELocalDecl, ExtraParameterId, FunctionId, GeneratedStructuralProjectionSpec, LocalDecl,
        LocalDeclId, LocalFunctionId, Module, ModuleEnv, PendingLocalClone, PendingLocalDrop,
        PendingModuleFunction, PendingTakeLocalValueMode, ProjectionIndex, ProjectionKey,
        ResolvedLocalClone, ResolvedLocalDrop, SubscriptId, SubscriptMemberKind, TraitId, id::Id,
    },
    types::r#trait::{TraitDictionaryEntryIndex, TraitMethodIndex},
    types::trait_solver::{TraitSolver, trait_solver_from_module},
};
use itertools::process_results;

use crate::{
    containers::{SVec2, b},
    hir::emit_value_impl::{function_value_method, generic_value_methods_for_type},
    hir::value::LiteralValue,
    hir::{
        self, ArgConvention, CallArgument, ENodeArena, ENodeId, Elaborated, Node, NodeArena,
        NodeKind, Project as HirProject, StaticApplication, UNodeArena, UNodeId, Unelaborated,
    },
    std::value::{
        is_function_surface_only_value_trait_application, is_value_trait_for_function_type,
        value_layout_associated_const_values,
    },
    types::effects::{EffType, no_effects},
    types::mutability::MutType,
    types::r#type::{CallImplType, CallResultConvention, FnArgType, FnType, Type, TypeKind},
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

/// Build a generated `Value` dictionary for a structural type whose unresolved
/// type variables appear only inside function types.
fn generic_derived_value_dictionary_node_kind(
    arena: &mut NodeArena,
    trait_id: TraitId,
    input_tys: &[Type],
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<(NodeKind, Type), InternalCompilationError> {
    let methods =
        generic_value_methods_for_type(ctx.trait_solver, trait_id, input_tys, span, arena)?;
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
    if is_value_trait_for_function_type(trait_id, trait_def, input_tys, output_tys) {
        return function_value_dictionary_node_kind(trait_id, input_tys, span, ctx);
    }

    let trait_def = ctx.trait_solver.trait_def(trait_id);
    if is_function_surface_only_value_trait_application(trait_id, trait_def, input_tys, output_tys)
    {
        return generic_derived_value_dictionary_node_kind(arena, trait_id, input_tys, span, ctx);
    }

    let ty = ctx
        .trait_solver
        .trait_def(trait_id)
        .get_dictionary_type_for_tys(input_tys, output_tys, output_effs);

    let node_kind = if input_tys.iter().all(|ty| ty.is_trait_input_resolved()) {
        let dictionary = ctx
            .trait_solver
            .solve_impl(trait_id, input_tys, span, arena)?;
        NodeKind::GetDictionary(hir::GetDictionary { dictionary })
    } else {
        let index = find_trait_impl_dict_index(ctx.dicts, trait_id, input_tys)
            .expect("Dictionary for trait impl not found, type inference should have failed");
        NodeKind::LoadDictionary(hir::LoadDictionary {
            extra_parameter: ExtraParameterId::from_index(index),
        })
    };
    Ok((node_kind, ty))
}

/// Return the method slot and callable type from an already-instantiated dictionary type.
fn dictionary_method_projection_data(
    trait_def: &crate::types::r#trait::Trait,
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
) -> NodeKind {
    NodeKind::GetSubscript(b(hir::GetSubscript {
        subscript,
        subscript_path: crate::ast::Path::new(vec![(name, span)]),
        inst_data: hir::FnInstData::new(Vec::new()),
    }))
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
                    let generated = ctx
                        .generated_projection_subscripts
                        .as_mut()
                        .expect("projection evidence generation requires module elaboration");
                    let structural_key = ProjectionKey::structural(ty, *name);
                    if let Some(subscript) = generated.get_existing(structural_key) {
                        let node_kind = get_projection_subscript_node_kind(subscript, *name, span);
                        return Ok((node_kind, expected_node_ty, expected_arg_ty));
                    }
                    if requirement.accepts_user_defined_projection()
                        && let Some(key) = ProjectionKey::nominal_for_receiver_ty(ty, *name)
                        && let Some(subscript) = ctx.trait_solver.projection_subscript_id(key)
                    {
                        let node_kind = get_projection_subscript_node_kind(subscript, *name, span);
                        return Ok((node_kind, expected_node_ty, expected_arg_ty));
                    }
                    let ty_kind = ty.data().clone();
                    let node_kind = match ty_kind {
                        Record(record) => {
                            let index = record.iter().position(|field| field.0 == *name).expect(
                                "Field not found in type, type inference should have failed"
                            );
                            let subscript =
                                generated.get_or_create(GeneratedStructuralProjectionSpec {
                                    key: structural_key,
                                    index,
                                    field_ty: subscript_ty.ret,
                                });
                            get_projection_subscript_node_kind(subscript, *name, span)
                        }
                        Named(named) => {
                            let shape = ctx
                                .trait_solver
                                .type_def(named.def)
                                .instantiated_shape_with_effects(
                                    &named.params,
                                    &named.effect_params,
                                );
                            let shape_data = shape.data();
                            let record = shape_data
                                .as_record()
                                .expect("ProjectionSubscript named receiver should have a record representation or explicit projection");
                            let index = record.iter().position(|field| field.0 == *name).expect(
                                "Field not found in type, type inference should have failed"
                            );
                            let subscript =
                                generated.get_or_create(GeneratedStructuralProjectionSpec {
                                    key: structural_key,
                                    index,
                                    field_ty: subscript_ty.ret,
                                });
                            get_projection_subscript_node_kind(subscript, *name, span)
                        }
                        Variable(var) => {
                            let index = find_projection_subscript_dict_index(ctx.dicts, var, name).unwrap_or_else(
                                || panic!("Projection subscript dictionary for field \"{name}\" in type variable \"{var}\" not found, type inference should have failed"),
                            );
                            K::LoadSubscriptEvidence(hir::LoadSubscriptEvidence {
                                extra_parameter: ExtraParameterId::from_index(index),
                            })
                        }
                        _ => {
                            panic!("ProjectionSubscript dictionary should have a variable or record type");
                        }
                    };
                    (node_kind, expected_node_ty)
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

fn extra_arg_kind_for_module_function(
    inst_data: &DictionariesReq,
    dicts: &ExtraParameters,
    trait_solver: &TraitSolver<'_>,
) -> Vec<(NodeKind, Type, FnArgType)> {
    inst_data
        .iter()
        .map(|dict| {
            // We find the index of the called function's requirement dict
            // in our requirement dicts. As dictionary passing is done
            // before type scheme simplification, they can be matched 1 to 1.
            let index = dicts
                .requirements
                .iter()
                .position(|d| d == dict)
                .expect("Target dictionary not found in ours");
            let ty = dict.to_dict_type(trait_solver);
            let extra_parameter = ExtraParameterId::from_index(index);
            let kind = match dict {
                DictionaryReq::TraitImpl { .. } => {
                    NodeKind::LoadDictionary(hir::LoadDictionary { extra_parameter })
                }
                DictionaryReq::ProjectionSubscript { .. } => {
                    NodeKind::LoadSubscriptEvidence(hir::LoadSubscriptEvidence { extra_parameter })
                }
            };
            (kind, ty, FnArgType::new(ty, MutType::constant()))
        })
        .collect()
}

/// Result of elaborating one unelaborated HIR root into the final HIR arena.
pub struct ElaboratedHir {
    pub root: ENodeId,
    pub remap: FxHashMap<UNodeId, ENodeId>,
    pub locals: Vec<ELocalDecl>,
}

/// Elaborate a pre-dictionary-passing HIR tree into the final HIR arena.
pub fn elaborate_hir<'d, 'sr, 'sm>(
    src: &UNodeArena,
    root: UNodeId,
    dst: &mut ENodeArena,
    ctx: &mut DictElaborationCtx<'d, 'sr, 'sm>,
    locals: Vec<LocalDecl>,
) -> Result<ElaboratedHir, InternalCompilationError> {
    let mut elaboration = HirElaboration::new(dst, ctx, locals);
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
    let mut pending = ids.into_iter().collect::<Vec<_>>();
    let mut index = 0;
    while index < pending.len() {
        let id = pending[index];
        index += 1;
        let Some(mut function) = pending_functions.remove(&id) else {
            continue;
        };
        function.definition = module.functions[id.as_index()].definition.clone();
        function.spans = module.functions[id.as_index()].spans.clone();

        let dicts = module.functions[id.as_index()]
            .definition
            .ty_scheme
            .extra_parameters(ModuleEnv::new(module, others));
        let generated_projection_subscripts =
            crate::module::PendingGeneratedStructuralProjectionSubscripts::new(module);
        let mut solver = trait_solver_from_module!(module, others);
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
        let generated = solver.commit(
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
struct HirElaboration<'a, 'd, 'sr, 'sm> {
    generated: UNodeArena,
    dst: &'a mut ENodeArena,
    ctx: &'a mut DictElaborationCtx<'d, 'sr, 'sm>,
    locals: Vec<LocalDecl>,
    remap: FxHashMap<UNodeId, ENodeId>,
    in_progress: FxHashSet<UNodeId>,
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

impl<'a, 'd, 'sr, 'sm> HirElaboration<'a, 'd, 'sr, 'sm> {
    fn new(
        dst: &'a mut ENodeArena,
        ctx: &'a mut DictElaborationCtx<'d, 'sr, 'sm>,
        locals: Vec<LocalDecl>,
    ) -> Self {
        Self {
            generated: UNodeArena::default(),
            dst,
            ctx,
            locals,
            remap: FxHashMap::default(),
            in_progress: FxHashSet::default(),
        }
    }

    fn push_owned_call_temp(
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
        let local = self.push_owned_call_temp(ty, drop, scope_span, name);
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

    fn elaborate_synthetic_node(
        &mut self,
        kind: NodeKind<Unelaborated>,
        ty: Type,
        effects: EffType,
        span: Location,
    ) -> Result<ENodeId, InternalCompilationError> {
        let kind = self.elaborate_synthetic_kind(kind, span)?;
        Ok(self.alloc_elaborated_node(kind, ty, effects, span))
    }

    fn elaborate_synthetic_kind(
        &mut self,
        kind: NodeKind<Unelaborated>,
        span: Location,
    ) -> Result<NodeKind<Elaborated>, InternalCompilationError> {
        use NodeKind::*;
        Ok(match kind {
            Immediate(value) => Immediate(value),
            GetSubscript(get_subscript) => GetSubscript(get_subscript),
            GetDictionary(get_dict) => GetDictionary(get_dict),
            LoadDictionary(load) => LoadDictionary(load),
            LoadSubscriptEvidence(load) => LoadSubscriptEvidence(load),
            _ => {
                return Err(internal_compilation_error!(Internal {
                    error: "unexpected synthetic HIR node requiring recursive elaboration"
                        .to_string(),
                    span,
                }));
            }
        })
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
        let extra_parameter = ExtraParameterId::from_index(index);
        let DictionaryReq::ProjectionSubscript { subscript_ty, .. } =
            &self.ctx.dicts.requirements[index]
        else {
            panic!("Projection subscript dictionary index should reference projection evidence");
        };
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
            inst_fn_args[0].mut_ty = crate::types::mutability::MutType::mutable();
        }
        let subscript = self.alloc_elaborated_node(
            LoadSubscriptEvidence(hir::LoadSubscriptEvidence { extra_parameter }),
            Type::subscript_type(subscript_ty.clone()),
            no_effects(),
            node_span,
        );
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

    fn elaborated_node_is_place_reference(&self, node_id: ENodeId) -> bool {
        // Elaborated HIR has no `FieldAccess`, `TraitMethodApply`, or
        // `GetTraitMethod` nodes; keep this phase-specific rather than
        // teaching the unelaborated place helper about elaboration payloads.
        match &self.dst[node_id].kind {
            NodeKind::LoadLocal(_) | NodeKind::Project(_) => true,
            NodeKind::FunctionApply(app) => app.ty.returns_place(),
            NodeKind::SubscriptApply(app) => app.ty.returns_place(),
            NodeKind::StaticApply(app) => app.ty.returns_place(),
            NodeKind::CallDictionaryMethod(call) => call.ty.returns_place(),
            NodeKind::WithPlace(node) => self.elaborated_node_is_place_reference(node.body),
            NodeKind::Block(block) => block
                .tail_node()
                .is_some_and(|node| self.elaborated_node_is_place_reference(node)),
            _ => false,
        }
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

        for (let_index, mutable_index) in
            hir::borrow_checker::let_arguments_overlapping_mutable(src, arguments)
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

        for (let_index, _) in
            hir::borrow_checker::let_arguments_overlapping_later_argument_writes(src, arguments)
        {
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
                let function = app.function;
                let ty = app.ty.clone();
                let arguments = self.elaborate_call_arguments(
                    src,
                    &app.arguments,
                    ty.returns_place(),
                    node_span,
                )?;
                let call = FunctionApply(b(hir::FunctionApplication {
                    function: self.elaborate_node(src, function)?,
                    arguments: arguments.arguments,
                    ty,
                }));
                self.wrap_call_cleanup(call, arguments.cleanup, node_ty, node_effects, node_span)
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
                    && let Some(extra_arg_kinds) = self
                        .ctx
                        .module_inst_data
                        .and_then(|inst_data| inst_data.get(&function.function))
                        .map(|inst_data| {
                            extra_arg_kind_for_module_function(
                                &inst_data.requirements,
                                self.ctx.dicts,
                                self.ctx.trait_solver,
                            )
                        })
                {
                    self.elaborate_extra_arg_kinds(extra_arg_kinds, node_span)?
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
                let inst_data = app.inst_data.clone();
                assert!(
                    inst_data.dicts_req.is_empty(),
                    "Instantiation data for trait method is not supported yet."
                );
                let resolved = input_tys.iter().all(|ty| ty.is_trait_input_resolved());
                let (is_value_function, is_function_surface_only, argument_names) = {
                    let trait_def = self.ctx.trait_solver.trait_def(trait_id);
                    let definition = &trait_def.method(method_index).1;
                    (
                        is_value_trait_for_function_type(trait_id, trait_def, &input_tys, &[]),
                        is_function_surface_only_value_trait_application(
                            trait_id,
                            trait_def,
                            &input_tys,
                            &[],
                        ),
                        definition.arg_names.clone(),
                    )
                };
                let arguments = self.elaborate_call_arguments(
                    src,
                    &app.arguments,
                    ty.returns_place(),
                    node_span,
                )?;
                let call = if is_value_function || resolved {
                    let function = if is_value_function {
                        FunctionId::new(
                            self.ctx.trait_solver.current_type_items.module.id,
                            function_value_method(
                                self.ctx.trait_solver,
                                method_index,
                                method_span,
                            )?,
                        )
                    } else {
                        self.ctx.trait_solver.solve_impl_method(
                            trait_id,
                            &input_tys,
                            method_index,
                            method_span,
                            &mut self.generated,
                        )?
                    };
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
                } else if is_function_surface_only {
                    let (dict_ty, entry_index) = {
                        let trait_def = self.ctx.trait_solver.trait_def(trait_id);
                        let dict_ty = trait_def.get_dictionary_type_for_tys(&input_tys, &[], &[]);
                        let (entry_index, _) =
                            dictionary_method_projection_data(trait_def, dict_ty, method_index);
                        (dict_ty, entry_index)
                    };
                    let (dict_kind, _) = trait_dictionary_node_kind(
                        &mut self.generated,
                        trait_id,
                        &input_tys,
                        &[],
                        &[],
                        method_span,
                        self.ctx,
                    )?;
                    let dictionary = self.elaborate_synthetic_node(
                        dict_kind,
                        dict_ty,
                        no_effects(),
                        method_span,
                    )?;
                    CallDictionaryMethod(b(hir::CallDictionaryMethod {
                        dictionary,
                        entry_index,
                        arguments: arguments.arguments,
                        ty,
                    }))
                } else {
                    let dict_index = find_trait_impl_dict_index(
                        self.ctx.dicts,
                        trait_id,
                        &input_tys,
                    )
                    .expect(
                        "Dictionary for trait impl not found, type inference should have failed",
                    );
                    let dict_ty =
                        self.ctx.dicts.requirements[dict_index].to_dict_type(self.ctx.trait_solver);
                    let dictionary = self.elaborate_synthetic_node(
                        NodeKind::LoadDictionary(hir::LoadDictionary {
                            extra_parameter: ExtraParameterId::from_index(dict_index),
                        }),
                        dict_ty,
                        no_effects(),
                        method_span,
                    )?;
                    let (entry_index, _) = dictionary_method_projection_data(
                        self.ctx.trait_solver.trait_def(trait_id),
                        dict_ty,
                        method_index,
                    );
                    CallDictionaryMethod(b(hir::CallDictionaryMethod {
                        dictionary,
                        entry_index,
                        arguments: arguments.arguments,
                        ty,
                    }))
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
                    if let Some(extra_arg_kinds) = self
                        .ctx
                        .module_inst_data
                        .and_then(|inst_data| inst_data.get(&get_fn.function.function))
                        .filter(|inst_data| !inst_data.is_empty())
                        .map(|inst_data| {
                            extra_arg_kind_for_module_function(
                                &inst_data.requirements,
                                self.ctx.dicts,
                                self.ctx.trait_solver,
                            )
                        })
                    {
                        self.elaborate_extra_arg_kinds(extra_arg_kinds, node_span)?
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
            GetSubscript(get_subscript) => {
                let mut get_subscript = (**get_subscript).clone();
                let captures = if !get_subscript.inst_data.dicts_req.is_empty() {
                    let (captures, _) = self
                        .elaborate_extra_args_from_inst_data(&get_subscript.inst_data, node_span)?;
                    get_subscript.inst_data.dicts_req.clear();
                    captures
                } else {
                    Vec::new()
                };
                if captures.is_empty() {
                    GetSubscript(b(get_subscript))
                } else {
                    let subscript = self.alloc_elaborated_node(
                        GetSubscript(b(get_subscript)),
                        node_ty,
                        node_effects.clone(),
                        node_span,
                    );
                    BuildSubscriptValue(b(hir::BuildSubscriptValue {
                        subscript,
                        evidence_captures: captures,
                    }))
                }
            }
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
                let resolved = input_tys.iter().all(|ty| ty.is_trait_input_resolved());
                let is_value_function = {
                    let trait_def = self.ctx.trait_solver.trait_def(trait_id);
                    is_value_trait_for_function_type(trait_id, trait_def, &input_tys, &output_tys)
                };
                if is_value_function || resolved {
                    let function = if is_value_function {
                        FunctionId::new(
                            self.ctx.trait_solver.current_type_items.module.id,
                            function_value_method(
                                self.ctx.trait_solver,
                                method_index,
                                method_span,
                            )?,
                        )
                    } else {
                        self.ctx.trait_solver.solve_impl_method(
                            trait_id,
                            &input_tys,
                            method_index,
                            method_span,
                            &mut self.generated,
                        )?
                    };
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
                    GetDictionaryMethod(hir::GetDictionaryMethod {
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
                let resolved = input_tys.iter().all(|ty| ty.is_trait_input_resolved());
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
                } else if resolved {
                    Immediate(self.ctx.trait_solver.solve_associated_const(
                        trait_id,
                        &input_tys,
                        associated_const_index,
                        associated_const_span,
                        &mut self.generated,
                    )?)
                } else {
                    let dict_index = find_trait_impl_dict_index(
                        self.ctx.dicts,
                        trait_id,
                        &input_tys,
                    )
                    .expect(
                        "Dictionary for trait impl not found, type inference should have failed",
                    );
                    let dict_ty =
                        self.ctx.dicts.requirements[dict_index].to_dict_type(self.ctx.trait_solver);
                    let dictionary = self.elaborate_synthetic_node(
                        NodeKind::LoadDictionary(hir::LoadDictionary {
                            extra_parameter: ExtraParameterId::from_index(dict_index),
                        }),
                        dict_ty,
                        no_effects(),
                        associated_const_span,
                    )?;
                    GetDictionaryAssociatedConst(hir::GetDictionaryAssociatedConst {
                        dictionary,
                        entry_index: self
                            .ctx
                            .trait_solver
                            .trait_def(trait_id)
                            .dictionary_associated_const_index(associated_const_index),
                    })
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
                self.elaborate_synthetic_kind(node_kind, node_span)?
            }
            GetDictionary(get_dict) => GetDictionary(*get_dict),
            LoadDictionary(load) => LoadDictionary(*load),
            LoadSubscriptEvidence(load) => LoadSubscriptEvidence(*load),
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
            GetDictionaryMethod(node) => {
                let dictionary = node.dictionary;
                let entry_index = node.entry_index;
                GetDictionaryMethod(hir::GetDictionaryMethod {
                    dictionary: self.elaborate_node(src, dictionary)?,
                    entry_index,
                })
            }
            GetDictionaryAssociatedConst(node) => {
                let dictionary = node.dictionary;
                let entry_index = node.entry_index;
                GetDictionaryAssociatedConst(hir::GetDictionaryAssociatedConst {
                    dictionary: self.elaborate_node(src, dictionary)?,
                    entry_index,
                })
            }
            CallDictionaryMethod(call) => {
                let dictionary = call.dictionary;
                let entry_index = call.entry_index;
                let ty = call.ty.clone();
                let arguments = self.elaborate_call_arguments(
                    src,
                    &call.arguments,
                    ty.returns_place(),
                    node_span,
                )?;
                let call = CallDictionaryMethod(b(hir::CallDictionaryMethod {
                    dictionary: self.elaborate_node(src, dictionary)?,
                    entry_index,
                    arguments: arguments.arguments,
                    ty,
                }));
                self.wrap_call_cleanup(call, arguments.cleanup, node_ty, node_effects, node_span)
            }
            Return(node) => Return(self.elaborate_node(src, *node)?),
            Block(block) => {
                let cleanup = block.cleanup.clone();
                Block(b(hir::Block {
                    body: b(SVec2::from_vec(
                        self.elaborate_node_iter(src, block.body.iter().copied())?,
                    )),
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
            Tuple(nodes) => Tuple(b(SVec2::from_vec(
                self.elaborate_node_iter(src, nodes.iter().copied())?,
            ))),
            Project(project) => {
                let value = project.value;
                let index = project.index;
                Project(hir::Project {
                    value: self.elaborate_node(src, value)?,
                    index,
                })
            }
            Record(nodes) => Record(b(SVec2::from_vec(
                self.elaborate_node_iter(src, nodes.iter().copied())?,
            ))),
            FieldAccess(field_access) => {
                use TypeKind::*;
                let child_id = field_access.value;
                let field_name = field_access.field;
                let child = self.elaborate_node(src, child_id)?;
                let child_ty = src[child_id].ty;
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
                match &*ty_data {
                    Record(record) => {
                        if let Some(index) = record.iter().position(|field| field.0 == field_name) {
                            Project(HirProject::new(child, ProjectionIndex::from_index(index)))
                        } else if let Some(index) =
                            find_projection_subscript_dict_index_for_receiver_ty(
                                self.ctx.dicts,
                                child_ty,
                                &field_name,
                            )
                        {
                            self.projection_evidence_field_access(
                                child,
                                field_name,
                                field_access.access_mode,
                                index,
                                node_ty,
                                node_span,
                            )
                        } else {
                            panic!("Field not found in type, type inference should have failed");
                        }
                    }
                    Variable(var) => {
                        let var = *var;
                        drop(ty_data);
                        let access_mode = field_access.access_mode;
                        let index = find_projection_subscript_dict_index(
                            self.ctx.dicts,
                            var,
                            &field_name,
                        )
                            .unwrap_or_else(
                                || panic!("Projection subscript dictionary for field \"{field_name}\" in type variable \"{var}\" not found, type inference should have failed"),
                            );
                        self.projection_evidence_field_access(
                            child,
                            field_name,
                            access_mode,
                            index,
                            node_ty,
                            node_span,
                        )
                    }
                    _ => {
                        panic!("FieldAccess should have a record or variable type");
                    }
                }
            }
            Variant(variant) => Variant(hir::Variant {
                tag: variant.tag,
                payload: self.elaborate_node(src, variant.payload)?,
            }),
            ExtractTag(node) => ExtractTag(self.elaborate_node(src, *node)?),
            Array(nodes) => Array(b(SVec2::from_vec(
                self.elaborate_node_iter(src, nodes.iter().copied())?,
            ))),
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
            Loop(node) => Loop(hir::Loop {
                label: node.label,
                body: self.elaborate_node(src, node.body)?,
            }),
            Break(node) => Break(hir::Break {
                label: node.label,
                value: self.elaborate_node(src, node.value)?,
            }),
            Continue(node) => Continue(hir::Continue { label: node.label }),
            Yield(node) => Yield(self.elaborate_node(src, *node)?),
            WithYielded(node) => {
                let accessor = self.elaborate_node(src, node.accessor)?;
                let body = self.elaborate_node(src, node.body)?;
                // A generic yielded projection may resolve to a concrete direct
                // projection or addressor-place call. In either case the
                // elaborated accessor already produces a place and needs no
                // suspended yielded-accessor protocol.
                if self.elaborated_node_is_place_reference(accessor) {
                    if let Some(inlined) =
                        self.inline_yielded_binding_body(node.binding, accessor, body)?
                    {
                        inlined
                    } else {
                        WithPlace(hir::WithPlace {
                            place: accessor,
                            binding: node.binding,
                            body,
                        })
                    }
                } else {
                    let mut body = body;
                    if self.elaborated_node_is_place_reference(body) {
                        body = self.materialize_elaborated_place_value(body, node_ty, node_span)?;
                    }
                    WithYielded(hir::WithYielded {
                        accessor,
                        binding: node.binding,
                        body,
                    })
                }
            }
            WithPlace(node) => WithPlace(hir::WithPlace {
                place: self.elaborate_node(src, node.place)?,
                binding: node.binding,
                body: self.elaborate_node(src, node.body)?,
            }),
            CheckCallDepth => CheckCallDepth,
            CheckFuel => CheckFuel,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{
        FxHashMap, Location, Modules,
        containers::b,
        hir::function::Function,
        hir::{GetTraitAssociatedConst, value::LiteralValue},
        module::{
            CurrentTypeItems, FunctionCollector, LocalDecl, LocalTraitId, Module, ModuleId, Path,
            PendingFunctionCollector, PendingGeneratedStructuralProjectionSubscripts,
            QualifiedNameEnv, TraitId, TraitImpls, id::Id,
        },
        std::math::int_type,
        types::{
            r#trait::{Trait, TraitAssociatedConst, TraitAssociatedConstIndex},
            trait_solver::{CurrentProjectionSubscriptTypes, TraitSolver},
            r#type::Type,
        },
    };

    fn layout_trait() -> Trait {
        Trait::new_with_self_input_type(
            "Layout",
            "Compiler-only layout metadata.",
            Vec::<&str>::new(),
            Vec::<(&str, crate::hir::function::CallableDefinition)>::new(),
        )
        .with_associated_consts([
            TraitAssociatedConst::new("SIZE", Type::primitive::<isize>(), "Size in bytes."),
            TraitAssociatedConst::new("ALIGN", Type::primitive::<isize>(), "Alignment in bytes."),
        ])
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
    fn concrete_associated_const_elaborates_to_immediate() {
        let traits = vec![layout_trait()];
        let trait_def = &traits[0];
        let trait_id = TraitId::new(ModuleId(0), LocalTraitId(0));
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
        let mut current_module = Module::new(ModuleId(0), Path::single_str("$elaboration_test"));
        current_module.traits = traits.clone();
        let qualified_name_env = QualifiedNameEnv::new_from_module(&current_module, &modules);
        let mut impls = TraitImpls::new(ModuleId(0));
        let mut fn_collector = FunctionCollector::new(0);
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
            &mut fn_collector,
            &qualified_name_env,
        );
        let mut deps = FxHashSet::default();
        let mut solver = TraitSolver::new(
            CurrentTypeItems::new_from_module(&current_module),
            &mut impls,
            FxHashMap::default(),
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
        let elaborated =
            elaborate_hir(&arena, node, &mut elaborated_arena, &mut ctx, Vec::new()).unwrap();

        let NodeKind::Immediate(immediate) = &elaborated_arena[elaborated.root].kind else {
            panic!("expected associated const to elaborate to an immediate");
        };
        assert_eq!(immediate.as_primitive_ty::<isize>(), Some(&8));
    }

    #[test]
    fn generic_associated_const_elaborates_to_dictionary_associated_const() {
        let traits = vec![layout_trait()];
        let trait_def = &traits[0];
        let trait_id = TraitId::new(ModuleId(0), LocalTraitId(0));
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

        let mut impls = TraitImpls::new(ModuleId(0));
        let modules = Modules::new();
        let mut current_module = Module::new(ModuleId(0), Path::single_str("$elaboration_test"));
        current_module.traits = traits.clone();
        let mut deps = FxHashSet::default();
        let mut solver = TraitSolver::new(
            CurrentTypeItems::new_from_module(&current_module),
            &mut impls,
            FxHashMap::default(),
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
        let elaborated =
            elaborate_hir(&arena, node, &mut elaborated_arena, &mut ctx, Vec::new()).unwrap();

        let NodeKind::GetDictionaryAssociatedConst(get_const) =
            &elaborated_arena[elaborated.root].kind
        else {
            panic!("expected associated const to elaborate to a dictionary associated const");
        };
        assert_eq!(usize::from(get_const.entry_index), 1);
        let NodeKind::LoadDictionary(load) = &elaborated_arena[get_const.dictionary].kind else {
            panic!("expected dictionary associated const source to load a dictionary");
        };
        assert_eq!(load.extra_parameter.as_index(), 0);
    }
}
