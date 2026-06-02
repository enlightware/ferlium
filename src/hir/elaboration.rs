// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{FxHashMap, FxHashSet, Modules};

use crate::{
    Location,
    compiler::error::InternalCompilationError,
    hir::{
        dictionary::{
            DictElaborationCtx, DictionariesReq, DictionaryReq, ExtraParameters,
            find_field_dict_index, find_trait_impl_dict_index,
        },
        value_dispatch::{resolve_arg_passing, resolve_local_clone, resolve_local_drop},
    },
    internal_compilation_error,
    module::{
        ConcreteTraitImplKey, ExtraParameterId, FunctionId, LocalDecl, LocalFunctionId, Module,
        ModuleEnv, PendingLocalClone, PendingLocalDrop, PendingModuleFunction,
        PendingTakeLocalValueMode, ProjectionIndex, TraitId, TraitImpl, TraitImplId, TraitImpls,
        build_dictionary_value, id::Id,
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
        self, CallArgument, ENodeArena, ENodeId, Elaborated, Node, NodeArena, NodeKind,
        Project as HirProject, ProjectAt as HirProjectAt, StaticApplication, UNodeArena, UNodeId,
        Unelaborated, function::PendingArgPassing,
    },
    std::{
        math::int_type,
        value::{
            is_function_surface_only_value_trait_application, is_value_trait_for_function_type,
            value_layout_associated_const_values,
        },
    },
    types::effects::{EffType, no_effects},
    types::mutability::MutType,
    types::r#type::{FnArgType, Type, TypeKind},
    types::type_like::TypeLike,
};

/// Build the use-site HIR expression for a generated `Value` dictionary.
fn value_dictionary_node_kind_from_methods(
    trait_id: TraitId,
    input_tys: &[Type],
    span: Location,
    methods: Vec<LocalFunctionId>,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<(NodeKind, Type), InternalCompilationError> {
    let trait_def = ctx.trait_solver.trait_def(trait_id);
    // This builds compiler-generated `Value` dictionaries. The associated
    // consts are layout metadata, so they are computed from the concrete HIR
    // type rather than read from a source impl.
    assert_eq!(methods.len(), trait_def.methods.len());
    let definitions = trait_def.instantiate_for_tys(input_tys, &[]);
    let method_tys = definitions
        .into_iter()
        .map(|definition| Type::function_type(definition.ty_scheme.ty))
        .collect::<Vec<_>>();
    let associated_const_values =
        value_layout_associated_const_values(input_tys[0], span, ctx.trait_solver)?;
    let ty = trait_def.get_dictionary_type_for_tys(input_tys, &[]);
    let associated_const_values = associated_const_values
        .into_iter()
        .map(LiteralValue::new_native)
        .collect::<Vec<_>>();
    let associated_const_tys = trait_def.instantiate_associated_const_tys_for_tys(input_tys, &[]);
    let dictionary_ty = TraitImpls::dictionary_ty(method_tys, associated_const_tys);
    let dictionary_value = build_dictionary_value(&methods, &associated_const_values);
    let imp = TraitImpl::new(
        Vec::new(),
        methods,
        dictionary_value,
        dictionary_ty,
        false,
        None,
    )
    .with_associated_const_values(associated_const_values);
    let impl_id = if input_tys.iter().all(Type::is_constant) {
        let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
        if let Some(impl_id) = ctx.trait_solver.impls.concrete().get(&key).copied() {
            impl_id
        } else {
            ctx.trait_solver.impls.add_concrete_struct(key, imp)
        }
    } else {
        ctx.trait_solver.impls.add_anonymous_dictionary_struct(imp)
    };
    Ok((
        NodeKind::GetDictionary(hir::GetDictionary {
            dictionary: TraitImplId::Local(impl_id),
        }),
        ty,
    ))
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
fn trait_dictionary_node_kind(
    arena: &mut NodeArena,
    trait_id: TraitId,
    input_tys: &[Type],
    output_tys: &[Type],
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
        .get_dictionary_type_for_tys(input_tys, output_tys);

    let node_kind = if input_tys.iter().all(Type::is_constant) {
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
                FieldIndex { ty, field: name } => {
                    let ty_data = ty.data();
                    let node_kind = match &*ty_data {
                        Record(record) => {
                            // Known type, get the index from the type and create an immediate with it.
                            let index = record.iter().position(|field| field.0 == *name).expect(
                                "Field not found in type, type inference should have failed"
                            );
                            K::Immediate(LiteralValue::new_native(index as isize))
                        }
                        Variable(var) => {
                            // Variable, it must be in the input dictionaries, look for it.
                            let var = *var;
                            drop(ty_data);
                            let index = find_field_dict_index(ctx.dicts, var, name).unwrap_or_else(
                                || panic!("Dictionary for field \"{name}\" in type variable \"{var}\" not found, type inference should have failed"),
                            );
                            K::LoadFieldIndex(hir::LoadFieldIndex {
                                extra_parameter: ExtraParameterId::from_index(index),
                            })
                        }
                        _ => {
                            panic!("FieldIndex dictionary should have a variable or record type");
                        }
                    };
                    (node_kind, int_type())
                }
                TraitImpl { trait_id, input_tys, output_tys, .. } => {
                    let (node_kind, ty) = trait_dictionary_node_kind(
                        arena,
                        *trait_id,
                        input_tys,
                        output_tys,
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
                DictionaryReq::FieldIndex { .. } => {
                    NodeKind::LoadFieldIndex(hir::LoadFieldIndex { extra_parameter })
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
}

/// Elaborate a pre-dictionary-passing HIR tree into the final HIR arena.
pub fn elaborate_hir<'d, 'sr, 'sm>(
    src: &UNodeArena,
    root: UNodeId,
    dst: &mut ENodeArena,
    ctx: &mut DictElaborationCtx<'d, 'sr, 'sm>,
    locals: &[LocalDecl],
) -> Result<ElaboratedHir, InternalCompilationError> {
    let mut elaboration = HirElaboration::new(dst, ctx, locals);
    let root = elaboration.elaborate_node(src, root)?;
    Ok(ElaboratedHir {
        root,
        remap: elaboration.remap,
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
        let mut solver = trait_solver_from_module!(module, others);
        let mut ctx = DictElaborationCtx::new(&dicts, None, &mut solver);
        let (elaborated, _) =
            function.check_borrows_and_elaborate_hir(&mut module.hir_arena, &mut ctx)?;
        module.functions[id.as_index()] = elaborated;
        pending.extend(solver.commit(
            &mut module.functions,
            &mut module.def_table,
            pending_functions,
        ));
    }
    Ok(())
}

/// Stateful worker that appends elaborated HIR nodes while tracking UNodeId-to-ENodeId remaps.
struct HirElaboration<'a, 'd, 'sr, 'sm> {
    generated: UNodeArena,
    dst: &'a mut ENodeArena,
    ctx: &'a mut DictElaborationCtx<'d, 'sr, 'sm>,
    locals: &'a [LocalDecl],
    remap: FxHashMap<UNodeId, ENodeId>,
    in_progress: FxHashSet<UNodeId>,
}

impl<'a, 'd, 'sr, 'sm> HirElaboration<'a, 'd, 'sr, 'sm> {
    fn new(
        dst: &'a mut ENodeArena,
        ctx: &'a mut DictElaborationCtx<'d, 'sr, 'sm>,
        locals: &'a [LocalDecl],
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
            GetDictionary(get_dict) => GetDictionary(get_dict),
            LoadDictionary(load) => LoadDictionary(load),
            LoadFieldIndex(load) => LoadFieldIndex(load),
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
        arguments: impl IntoIterator<Item = (UNodeId, PendingArgPassing, Type)>,
        node_span: Location,
    ) -> Result<Vec<CallArgument<Elaborated>>, InternalCompilationError> {
        let arguments = arguments.into_iter();
        let (lower, _) = arguments.size_hint();
        let mut result = Vec::with_capacity(lower);
        for (value, mut passing, arg_ty) in arguments {
            resolve_arg_passing(
                src,
                &mut self.generated,
                self.ctx,
                &mut passing,
                value,
                arg_ty,
                node_span,
            )?;
            result.push(CallArgument {
                value: self.elaborate_node(src, value)?,
                passing: passing.into_elaborated(),
            });
        }
        Ok(result)
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
            Apply(app) => {
                let function = app.function;
                let returns_place = app.returns_place;
                let source_arguments = app
                    .arguments
                    .iter()
                    .map(|arg| (arg.value, arg.passing, src[arg.value].ty));
                Apply(b(hir::Application {
                    function: self.elaborate_node(src, function)?,
                    arguments: self.elaborate_call_arguments(src, source_arguments, node_span)?,
                    returns_place,
                }))
            }
            CloneClosureEnv(node) => {
                let source = node.source;
                let target = node.target;
                CloneClosureEnv(hir::CloneClosureEnv {
                    source: self.elaborate_node(src, source)?,
                    target: self.elaborate_node(src, target)?,
                })
            }
            DropClosureEnv(node) => {
                let target = node.target;
                DropClosureEnv(hir::DropClosureEnv {
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
                let ty = app.ty.clone();
                let inst_data = app.inst_data.clone();
                let returns_place = app.returns_place;
                let source_arguments = app
                    .arguments
                    .iter()
                    .zip(&app.ty.args)
                    .map(|(arg, arg_ty)| (arg.value, arg.passing, arg_ty.ty));
                let source_extra_arguments = app.extra_arguments.iter().copied();
                let mut extra_arguments = if !inst_data.dicts_req.is_empty() {
                    self.elaborate_extra_args_from_inst_data(&inst_data, function_span)?
                        .0
                } else if let FunctionId::Local(id) = function
                    && let Some(extra_arg_kinds) = self
                        .ctx
                        .module_inst_data
                        .and_then(|inst_data| inst_data.get(&id))
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
                StaticApply(b(StaticApplication {
                    function,
                    function_path,
                    function_span,
                    extra_arguments,
                    arguments: self.elaborate_call_arguments(src, source_arguments, node_span)?,
                    argument_names,
                    ty,
                    inst_data,
                    returns_place,
                }))
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
                let source_arguments = || {
                    app.arguments
                        .iter()
                        .zip(&app.ty.args)
                        .map(|(arg, arg_ty)| (arg.value, arg.passing, arg_ty.ty))
                };
                assert!(
                    inst_data.dicts_req.is_empty(),
                    "Instantiation data for trait method is not supported yet."
                );
                let resolved = input_tys.iter().all(Type::is_constant);
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
                        arguments_unnamed.filter_args(&definition.arg_names),
                    )
                };
                if is_value_function || resolved {
                    let function = if is_value_function {
                        FunctionId::Local(function_value_method(
                            self.ctx.trait_solver,
                            method_index,
                            method_span,
                        )?)
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
                        arguments: self.elaborate_call_arguments(
                            src,
                            source_arguments(),
                            node_span,
                        )?,
                        argument_names,
                        ty,
                        inst_data: hir::FnInstData::none(),
                        returns_place: false,
                    }))
                } else if is_function_surface_only {
                    let (dict_ty, entry_index) = {
                        let trait_def = self.ctx.trait_solver.trait_def(trait_id);
                        let dict_ty = trait_def.get_dictionary_type_for_tys(&input_tys, &[]);
                        let (entry_index, _) =
                            dictionary_method_projection_data(trait_def, dict_ty, method_index);
                        (dict_ty, entry_index)
                    };
                    let (dict_kind, _) = trait_dictionary_node_kind(
                        &mut self.generated,
                        trait_id,
                        &input_tys,
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
                        arguments: self.elaborate_call_arguments(
                            src,
                            source_arguments(),
                            node_span,
                        )?,
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
                        arguments: self.elaborate_call_arguments(
                            src,
                            source_arguments(),
                            node_span,
                        )?,
                        ty,
                    }))
                }
            }
            GetFunction(get_fn) => {
                let mut get_fn = (**get_fn).clone();
                let captures = if !get_fn.inst_data.dicts_req.is_empty() {
                    let (captures, _) =
                        self.elaborate_extra_args_from_inst_data(&get_fn.inst_data, node_span)?;
                    get_fn.inst_data.dicts_req.clear();
                    captures
                } else if let FunctionId::Local(fn_local_id) = get_fn.function {
                    if let Some(extra_arg_kinds) = self
                        .ctx
                        .module_inst_data
                        .and_then(|inst_data| inst_data.get(&fn_local_id))
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
                let resolved = input_tys.iter().all(Type::is_constant);
                let is_value_function = {
                    let trait_def = self.ctx.trait_solver.trait_def(trait_id);
                    is_value_trait_for_function_type(trait_id, trait_def, &input_tys, &output_tys)
                };
                if is_value_function || resolved {
                    let function = if is_value_function {
                        FunctionId::Local(function_value_method(
                            self.ctx.trait_solver,
                            method_index,
                            method_span,
                        )?)
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
                        let dict_ty =
                            trait_def.get_dictionary_type_for_tys(&input_tys, &output_tys);
                        let (entry_index, _) =
                            dictionary_method_projection_data(trait_def, dict_ty, method_index);
                        (dict_ty, entry_index)
                    };
                    let (dict_kind, _) = trait_dictionary_node_kind(
                        &mut self.generated,
                        trait_id,
                        &input_tys,
                        &output_tys,
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
                let resolved = input_tys.iter().all(Type::is_constant);
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
                let (node_kind, _) = trait_dictionary_node_kind(
                    &mut self.generated,
                    get_dict.trait_id,
                    &input_tys,
                    &output_tys,
                    node_span,
                    self.ctx,
                )?;
                self.elaborate_synthetic_kind(node_kind, node_span)?
            }
            GetDictionary(get_dict) => GetDictionary(*get_dict),
            LoadDictionary(load) => LoadDictionary(*load),
            LoadFieldIndex(load) => LoadFieldIndex(*load),
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
                let source_arguments = call
                    .arguments
                    .iter()
                    .zip(&call.ty.args)
                    .map(|(arg, arg_ty)| (arg.value, arg.passing, arg_ty.ty));
                CallDictionaryMethod(b(hir::CallDictionaryMethod {
                    dictionary: self.elaborate_node(src, dictionary)?,
                    entry_index,
                    arguments: self.elaborate_call_arguments(src, source_arguments, node_span)?,
                    ty,
                }))
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
                        .instantiated_shape(&named.params)
                        .data()
                } else {
                    ty_data
                };
                match &*ty_data {
                    Record(record) => {
                        let index = record
                            .iter()
                            .position(|field| field.0 == field_name)
                            .expect("Field not found in type, type inference should have failed");
                        Project(HirProject::new(child, ProjectionIndex::from_index(index)))
                    }
                    Variable(var) => {
                        let var = *var;
                        drop(ty_data);
                        let index = find_field_dict_index(self.ctx.dicts, var, &field_name)
                            .unwrap_or_else(
                                || panic!("Dictionary for field \"{field_name}\" in type variable \"{var}\" not found, type inference should have failed"),
                            );
                        ProjectAt(HirProjectAt::new(
                            child,
                            ExtraParameterId::from_index(index),
                        ))
                    }
                    _ => {
                        panic!("FieldAccess should have a record or variable type");
                    }
                }
            }
            ProjectAt(project) => {
                let value = project.value;
                let index = project.index;
                ProjectAt(hir::ProjectAt {
                    value: self.elaborate_node(src, value)?,
                    index,
                })
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
            FunctionCollector, LocalDecl, LocalTraitId, ModuleId, PendingFunctionCollector,
            TraitId, TraitImpls, id::Id,
        },
        types::{
            r#trait::{Trait, TraitAssociatedConst, TraitAssociatedConstIndex},
            trait_solver::TraitSolver,
            r#type::Type,
        },
    };

    fn layout_trait() -> Trait {
        Trait::new_with_self_input_type(
            "Layout",
            "Compiler-only layout metadata.",
            Vec::<&str>::new(),
            Vec::<(&str, crate::hir::function::FunctionDefinition)>::new(),
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

        let mut impls = TraitImpls::new(ModuleId(0));
        let mut fn_collector = FunctionCollector::new(0);
        impls.add_concrete_raw(
            trait_id,
            trait_def,
            [Type::unit()],
            [],
            [
                LiteralValue::new_native(8isize),
                LiteralValue::new_native(4isize),
            ],
            Vec::<(Function, Vec<LocalDecl>)>::new(),
            &mut fn_collector,
        );
        let modules = Modules::new();
        let type_defs = Vec::new();
        let mut import_fn_slots = Vec::new();
        let mut import_impl_slots = Vec::new();
        let mut solver = TraitSolver::new(
            crate::types::trait_solver::CurrentTypeDefs::new(ModuleId(0), &type_defs),
            &traits,
            &mut impls,
            FxHashMap::default(),
            &mut import_fn_slots,
            &mut import_impl_slots,
            PendingFunctionCollector::new(0),
            &modules,
        );
        let dicts = ExtraParameters {
            requirements: vec![],
            repr_map: FxHashMap::default(),
        };
        let mut ctx = DictElaborationCtx::new(&dicts, None, &mut solver);

        let mut elaborated_arena = ENodeArena::default();
        let elaborated = elaborate_hir(&arena, node, &mut elaborated_arena, &mut ctx, &[]).unwrap();

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
        let type_defs = Vec::new();
        let mut import_fn_slots = Vec::new();
        let mut import_impl_slots = Vec::new();
        let mut solver = TraitSolver::new(
            crate::types::trait_solver::CurrentTypeDefs::new(ModuleId(0), &type_defs),
            &traits,
            &mut impls,
            FxHashMap::default(),
            &mut import_fn_slots,
            &mut import_impl_slots,
            PendingFunctionCollector::new(0),
            &modules,
        );
        let dicts = ExtraParameters {
            requirements: vec![DictionaryReq::new_trait_impl(
                trait_id,
                vec![input_ty],
                vec![],
            )],
            repr_map: FxHashMap::default(),
        };
        let mut ctx = DictElaborationCtx::new(&dicts, None, &mut solver);

        let mut elaborated_arena = ENodeArena::default();
        let elaborated = elaborate_hir(&arena, node, &mut elaborated_arena, &mut ctx, &[]).unwrap();

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
