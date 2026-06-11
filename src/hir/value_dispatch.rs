// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    Location,
    compiler::error::InternalCompilationError,
    containers::{SVec2, b},
    hir::{
        self, NodeArena, NodeId, NodeKind,
        dictionary::{DictElaborationCtx, find_trait_impl_dict_index},
        emit_value_impl::{function_value_method, generic_value_methods_for_type},
        function::{
            PendingArgPassing, PendingValueArgPassing, ResolvedValueArgPassing,
            resolve_arg_passing_for_call,
        },
    },
    internal_compilation_error,
    module::{
        ExtraParameterId, FunctionId, LocalDecl, LocalDeclId, LocalStorage, PendingLocalClone,
        PendingLocalDrop, ResolvedLocalClone, ResolvedLocalDrop, id::Id,
    },
    std::{
        core_traits_names::VALUE_TRAIT_NAME,
        value::{
            VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX, is_function_surface_only_value_type,
            uninit_inner_type,
        },
    },
    types::{
        effects::{EffType, no_effects},
        mutability::MutType,
        r#trait::TraitMethodIndex,
        trait_solver::TraitSolver,
        r#type::{FnArgType, FnType, Type},
        type_like::TypeLike,
    },
};

/// Resolve any remaining local ownership placeholders and local clone/drop value dispatches.
pub fn elaborate_local_ownership_and_value_dispatches<'d, 'sr, 'sm>(
    arena: &mut NodeArena,
    locals: &mut [LocalDecl],
    ctx: &mut DictElaborationCtx<'d, 'sr, 'sm>,
) -> Result<(), InternalCompilationError> {
    for local in locals {
        if matches!(local.storage, LocalStorage::Deferred(_)) {
            return Err(internal_compilation_error!(Internal {
                error: "deferred local storage reached value dispatch elaboration".to_string(),
                span: local.scope,
            }));
        }

        if matches!(local.clone, Some(PendingLocalClone::Unknown)) {
            local.clone = Some(PendingLocalClone::Resolved(resolve_local_clone(
                arena,
                ctx,
                local.ty,
                local.scope,
            )?));
        }

        let local_ty = local.ty;
        let local_scope = local.scope;
        if let Some(drop) = local.local_drop_mut()
            && matches!(drop, PendingLocalDrop::Unknown)
        {
            *drop = resolve_local_drop(arena, ctx, local_ty, local_scope)?;
        }
    }
    Ok(())
}

#[derive(Debug, Clone, Copy)]
enum ResolvedValueMethodDispatch {
    Static(FunctionId),
    Dictionary(ExtraParameterId),
}

/// Resolve a required `Value` method into either a static function or a runtime dictionary slot.
fn resolve_value_method_dispatch(
    arena: &mut NodeArena,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    ty: Type,
    method_index: TraitMethodIndex,
    span: Location,
    missing_dictionary_msg: &str,
) -> Result<ResolvedValueMethodDispatch, InternalCompilationError> {
    if ty.is_function() {
        return Ok(ResolvedValueMethodDispatch::Static(FunctionId::Local(
            function_value_method(ctx.trait_solver, method_index, span)?,
        )));
    }
    if is_function_surface_only_value_type(ty) {
        let value_trait_id = ctx.trait_solver.std_trait_id(VALUE_TRAIT_NAME);
        let methods =
            generic_value_methods_for_type(ctx.trait_solver, value_trait_id, &[ty], span, arena)?;
        return Ok(ResolvedValueMethodDispatch::Static(FunctionId::Local(
            methods[usize::from(method_index)],
        )));
    }
    if ty.is_constant() {
        let value_trait_id = ctx.trait_solver.std_trait_id(VALUE_TRAIT_NAME);
        return Ok(ResolvedValueMethodDispatch::Static(
            ctx.trait_solver
                .solve_impl_method(value_trait_id, &[ty], method_index, span, arena)?,
        ));
    }
    let value_trait_id = ctx.trait_solver.std_trait_id(VALUE_TRAIT_NAME);
    let dict_index = find_trait_impl_dict_index(ctx.dicts, value_trait_id, &[ty])
        .unwrap_or_else(|| panic!("{missing_dictionary_msg}: {ty:?}"));
    Ok(ResolvedValueMethodDispatch::Dictionary(
        ExtraParameterId::from_index(dict_index),
    ))
}

pub(crate) fn resolve_local_clone(
    arena: &mut NodeArena,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    ty: Type,
    span: Location,
) -> Result<ResolvedLocalClone, InternalCompilationError> {
    if ctx
        .trait_solver
        .solve_concrete_trivial_copy_layout(arena, ty, span)?
        .is_some()
    {
        return Ok(ResolvedLocalClone::TrivialCopy);
    }
    let dispatch = resolve_value_method_dispatch(
        arena,
        ctx,
        ty,
        VALUE_CLONE_METHOD_INDEX,
        span,
        "Value dictionary for clone not found, type inference should have failed",
    )?;
    Ok(match dispatch {
        ResolvedValueMethodDispatch::Static(function) => ResolvedLocalClone::Static(function),
        ResolvedValueMethodDispatch::Dictionary(dictionary) => {
            ResolvedLocalClone::Dictionary(dictionary)
        }
    })
}

pub(crate) fn resolve_local_drop(
    arena: &mut NodeArena,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    ty: Type,
    span: Location,
) -> Result<PendingLocalDrop, InternalCompilationError> {
    if uninit_inner_type(ty).is_some() {
        return Ok(PendingLocalDrop::Resolved(ResolvedLocalDrop::Skip));
    }
    if ctx
        .trait_solver
        .solve_concrete_trivial_copy_layout(arena, ty, span)?
        .is_some()
    {
        return Ok(PendingLocalDrop::Resolved(ResolvedLocalDrop::Skip));
    }
    let dispatch = resolve_value_method_dispatch(
        arena,
        ctx,
        ty,
        VALUE_DROP_METHOD_INDEX,
        span,
        "Value dictionary for drop not found, type inference should have failed",
    )?;
    Ok(PendingLocalDrop::Resolved(match dispatch {
        ResolvedValueMethodDispatch::Static(function) => ResolvedLocalDrop::Static(function),
        ResolvedValueMethodDispatch::Dictionary(dictionary) => {
            ResolvedLocalDrop::Dictionary(dictionary)
        }
    }))
}

pub(crate) fn resolve_arg_passing(
    source_arena: &NodeArena,
    generated_arena: &mut NodeArena,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    passing: &mut PendingArgPassing,
    arg: NodeId,
    ty: Type,
    span: Location,
) -> Result<(), InternalCompilationError> {
    match passing {
        PendingArgPassing::MutableRef
        | PendingArgPassing::Value(PendingValueArgPassing::Resolved(
            ResolvedValueArgPassing::SharedRef,
        )) => {}
        PendingArgPassing::Value(PendingValueArgPassing::Resolved(
            ResolvedValueArgPassing::TrivialCopy,
        )) => {
            if ctx
                .trait_solver
                .solve_concrete_trivial_copy_layout(generated_arena, ty, span)?
                .is_none()
            {
                return Err(internal_compilation_error!(Internal {
                    error: "trivial-copy call argument has no resolved layout".to_string(),
                    span,
                }));
            }
        }
        PendingArgPassing::Value(PendingValueArgPassing::Unknown) => {
            let needs_temp = crate::hir::function::call_argument_may_need_temp(source_arena, arg);
            *passing = PendingArgPassing::Value(PendingValueArgPassing::Resolved(
                resolve_value_arg_passing(generated_arena, ctx, ty, needs_temp, span)?,
            ));
        }
    }
    Ok(())
}

fn resolve_value_arg_passing(
    arena: &mut NodeArena,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    ty: Type,
    needs_temp: bool,
    span: Location,
) -> Result<ResolvedValueArgPassing, InternalCompilationError> {
    if ctx
        .trait_solver
        .solve_concrete_trivial_copy_layout(arena, ty, span)?
        .is_some()
    {
        Ok(ResolvedValueArgPassing::TrivialCopy)
    } else if needs_temp {
        Err(internal_compilation_error!(Internal {
            error: "shared-reference call argument still needs an explicit temporary".to_string(),
            span,
        }))
    } else {
        Ok(ResolvedValueArgPassing::SharedRef)
    }
}

pub(crate) fn resolved_arg_passing_for_generated_call(
    arena: &mut NodeArena,
    trait_solver: &mut TraitSolver<'_>,
    args: &[NodeId],
    arg_tys: &[FnArgType],
    span: Location,
) -> Result<Vec<PendingArgPassing>, InternalCompilationError> {
    resolve_arg_passing_for_call(
        arena,
        trait_solver,
        args,
        arg_tys,
        span,
        resolve_generated_trivial_copy_or_shared_ref_arg_passing,
    )
}

/// Build a generated static call, materializing non-place shared-reference
/// arguments as explicit owned locals scoped to a cleanup block.
pub(crate) fn static_apply_generated_with_locals(
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    trait_solver: &mut TraitSolver<'_>,
    function: FunctionId,
    arguments: impl IntoIterator<Item = (NodeId, Type)>,
    ret_ty: Type,
    span: Location,
) -> Result<NodeId, InternalCompilationError> {
    let (mut arguments, args_tys): (Vec<_>, Vec<_>) = arguments.into_iter().unzip();
    let fn_ty = FnType::new_by_val(args_tys, ret_ty, EffType::empty());
    let prepared = prepare_generated_call_arguments_with_locals(
        arena,
        locals,
        trait_solver,
        &mut arguments,
        &fn_ty.args,
        span,
    )?;
    let call = arena.alloc(hir::Node::new(
        hir::hir_syn::static_apply_with_argument_passing(
            function,
            fn_ty,
            arguments,
            prepared.argument_passing,
            span,
        ),
        ret_ty,
        EffType::empty(),
        span,
    ));

    Ok(wrap_generated_call_with_temp_cleanup(
        arena,
        prepared.temp_stores,
        prepared.cleanup,
        call,
        ret_ty,
        span,
    ))
}

/// Prepared visible arguments plus explicit temporary stores/cleanup needed by a generated call.
pub(crate) struct GeneratedCallArgumentPreparation {
    pub argument_passing: Vec<PendingArgPassing>,
    pub temp_stores: Vec<NodeId>,
    pub cleanup: Vec<LocalDeclId>,
}

/// Materialize generated non-place shared-reference arguments as locals before resolving passing.
pub(crate) fn prepare_generated_call_arguments_with_locals(
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    trait_solver: &mut TraitSolver<'_>,
    arguments: &mut [NodeId],
    arg_tys: &[FnArgType],
    span: Location,
) -> Result<GeneratedCallArgumentPreparation, InternalCompilationError> {
    let mut temp_stores = Vec::new();
    let mut cleanup = Vec::new();

    for (arg, arg_ty) in arguments.iter_mut().zip(arg_tys) {
        if arg_ty
            .mut_ty
            .as_resolved()
            .is_some_and(|mut_ty| mut_ty.is_mutable())
            || !generated_value_argument_needs_shared_ref_temp(
                arena,
                trait_solver,
                *arg,
                arg_ty.ty,
                span,
            )?
        {
            continue;
        }

        let value = *arg;
        let value_span = arena[value].span;
        let value_effects = arena[value].effects.clone();
        let ty = arg_ty.ty;
        let mut local = LocalDecl::new(
            (crate::ustr("$arg"), Location::new_synthesized()),
            MutType::constant(),
            ty,
            None,
            span,
        );
        local.set_owned_storage(PendingLocalDrop::Resolved(resolve_generated_temp_drop(
            arena,
            trait_solver,
            ty,
            span,
        )?));
        let local_id = LocalDecl::push_with_next_slot(locals, local);

        let store = arena.alloc(hir::Node::new(
            NodeKind::StoreLocal(hir::StoreLocal {
                value,
                id: local_id,
            }),
            Type::unit(),
            value_effects,
            span,
        ));
        let load = arena.alloc(hir::Node::new(
            NodeKind::LoadLocal(hir::LoadLocal { id: local_id }),
            ty,
            no_effects(),
            value_span,
        ));
        temp_stores.push(store);
        cleanup.push(local_id);
        *arg = load;
    }

    let argument_passing =
        resolved_arg_passing_for_generated_call(arena, trait_solver, arguments, arg_tys, span)?;
    Ok(GeneratedCallArgumentPreparation {
        argument_passing,
        temp_stores,
        cleanup,
    })
}

/// Wrap a generated call in a block that stores argument temps and cleans them up after the call.
pub(crate) fn wrap_generated_call_with_temp_cleanup(
    arena: &mut NodeArena,
    mut temp_stores: Vec<NodeId>,
    cleanup: Vec<LocalDeclId>,
    call: NodeId,
    ty: Type,
    span: Location,
) -> NodeId {
    if temp_stores.is_empty() {
        return call;
    }
    temp_stores.push(call);
    arena.alloc(hir::Node::new(
        NodeKind::Block(b(hir::Block {
            body: b(SVec2::from_vec(temp_stores)),
            cleanup,
        })),
        ty,
        EffType::empty(),
        span,
    ))
}

fn generated_value_argument_needs_shared_ref_temp(
    arena: &mut NodeArena,
    trait_solver: &mut TraitSolver<'_>,
    arg: NodeId,
    ty: Type,
    span: Location,
) -> Result<bool, InternalCompilationError> {
    Ok(ty.is_constant()
        && ty != Type::never()
        && !ty.is_function()
        && !hir::node_is_place_reference(arena, arg)
        && trait_solver
            .solve_concrete_trivial_copy_layout(arena, ty, span)?
            .is_none())
}

fn resolve_generated_trivial_copy_or_shared_ref_arg_passing(
    arena: &mut NodeArena,
    trait_solver: &mut TraitSolver<'_>,
    ty: Type,
    needs_temp: bool,
    span: Location,
) -> Result<ResolvedValueArgPassing, InternalCompilationError> {
    if trait_solver
        .solve_concrete_trivial_copy_layout(arena, ty, span)?
        .is_some()
    {
        Ok(ResolvedValueArgPassing::TrivialCopy)
    } else if needs_temp {
        Err(internal_compilation_error!(Internal {
            error: "generated shared-reference call argument still needs an explicit temporary"
                .to_string(),
            span,
        }))
    } else {
        Ok(ResolvedValueArgPassing::SharedRef)
    }
}

fn resolve_generated_temp_drop(
    arena: &mut NodeArena,
    trait_solver: &mut TraitSolver<'_>,
    ty: Type,
    span: Location,
) -> Result<ResolvedLocalDrop, InternalCompilationError> {
    if trait_solver
        .solve_concrete_trivial_copy_layout(arena, ty, span)?
        .is_some()
    {
        return Ok(ResolvedLocalDrop::Skip);
    }
    if is_function_surface_only_value_type(ty) {
        return Ok(ResolvedLocalDrop::Static(FunctionId::Local(
            function_value_method(trait_solver, VALUE_DROP_METHOD_INDEX, span)?,
        )));
    }
    Ok(ResolvedLocalDrop::Static(trait_solver.solve_impl_method(
        trait_solver.std_trait_id(VALUE_TRAIT_NAME),
        &[ty],
        VALUE_DROP_METHOD_INDEX,
        span,
        arena,
    )?))
}
