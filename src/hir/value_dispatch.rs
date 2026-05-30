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
    hir::{
        self, NodeArena, NodeId, NodeKind,
        dictionary::{DictElaborationCtx, find_trait_impl_dict_index},
        emit_value_impl::{function_value_method, generic_value_methods_for_type},
        function::{
            PendingArgPassing, PendingValueArgPassing, ResolvedValueArgPassing,
            SharedRefTempCleanup, resolve_arg_passing_for_call,
        },
    },
    internal_compilation_error,
    module::{
        ExtraParameterId, FunctionId, LocalDecl, LocalStorage, PendingLocalClone, PendingLocalDrop,
        ResolvedLocalClone, ResolvedLocalDrop, id::Id,
    },
    std::{
        core_traits_names::{TRIVIAL_COPY_TRAIT_NAME, VALUE_TRAIT_NAME},
        value::{
            VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX, is_function_surface_only_value_type,
        },
    },
    types::{
        effects::EffType,
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
    if type_has_concrete_trivial_copy_impl(arena, ctx, ty, span) {
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
    if type_has_concrete_trivial_copy_impl(arena, ctx, ty, span) {
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
        | PendingArgPassing::Value(PendingValueArgPassing::Resolved(_)) => {}
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
    if type_has_concrete_trivial_copy_impl(arena, ctx, ty, span) {
        Ok(ResolvedValueArgPassing::Owned)
    } else if !needs_temp {
        Ok(ResolvedValueArgPassing::SharedRef {
            temp_cleanup: SharedRefTempCleanup::None,
        })
    } else {
        Ok(ResolvedValueArgPassing::SharedRef {
            temp_cleanup: SharedRefTempCleanup::Drop(resolve_temp_drop(arena, ctx, ty, span)?),
        })
    }
}

fn resolve_temp_drop(
    arena: &mut NodeArena,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    ty: Type,
    span: Location,
) -> Result<ResolvedLocalDrop, InternalCompilationError> {
    match resolve_local_drop(arena, ctx, ty, span)? {
        PendingLocalDrop::Resolved(drop) => Ok(drop),
        PendingLocalDrop::Unknown => unreachable!("resolve_local_drop always resolves"),
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
        resolve_generated_value_arg_passing,
    )
}

/// Build a generated static call whose visible argument passing is resolved from
/// the final argument types and the actual argument HIR nodes.
pub(crate) fn static_apply_generated(
    arena: &mut NodeArena,
    trait_solver: &mut TraitSolver<'_>,
    function: FunctionId,
    arguments: impl IntoIterator<Item = (NodeId, Type)>,
    ret_ty: Type,
    span: Location,
) -> Result<NodeKind, InternalCompilationError> {
    let (arguments, args_tys): (Vec<_>, Vec<_>) = arguments.into_iter().unzip();
    let fn_ty = FnType::new_by_val(args_tys, ret_ty, EffType::empty());
    let argument_passing = resolved_arg_passing_for_generated_call(
        arena,
        trait_solver,
        &arguments,
        &fn_ty.args,
        span,
    )?;
    Ok(hir::hir_syn::static_apply_with_argument_passing(
        function,
        fn_ty,
        arguments,
        argument_passing,
        span,
    ))
}

fn resolve_generated_value_arg_passing(
    arena: &mut NodeArena,
    trait_solver: &mut TraitSolver<'_>,
    ty: Type,
    needs_temp: bool,
    span: Location,
) -> Result<ResolvedValueArgPassing, InternalCompilationError> {
    if generated_type_has_trivial_copy_impl(arena, trait_solver, ty, span) {
        Ok(ResolvedValueArgPassing::Owned)
    } else if !needs_temp {
        Ok(ResolvedValueArgPassing::SharedRef {
            temp_cleanup: SharedRefTempCleanup::None,
        })
    } else {
        Ok(ResolvedValueArgPassing::SharedRef {
            temp_cleanup: SharedRefTempCleanup::Drop(resolve_generated_temp_drop(
                arena,
                trait_solver,
                ty,
                span,
            )?),
        })
    }
}

fn resolve_generated_temp_drop(
    arena: &mut NodeArena,
    trait_solver: &mut TraitSolver<'_>,
    ty: Type,
    span: Location,
) -> Result<ResolvedLocalDrop, InternalCompilationError> {
    if generated_type_has_trivial_copy_impl(arena, trait_solver, ty, span) {
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

fn generated_type_has_trivial_copy_impl(
    arena: &mut NodeArena,
    trait_solver: &mut TraitSolver<'_>,
    ty: Type,
    span: Location,
) -> bool {
    ty.is_constant()
        && trait_solver
            .solve_output_types(
                trait_solver.std_trait_id(TRIVIAL_COPY_TRAIT_NAME),
                &[ty],
                span,
                arena,
            )
            .is_ok()
}

fn type_has_concrete_trivial_copy_impl(
    arena: &mut NodeArena,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    ty: Type,
    span: Location,
) -> bool {
    ty.is_constant()
        && ctx
            .trait_solver
            .solve_output_types(
                ctx.trait_solver.std_trait_id(TRIVIAL_COPY_TRAIT_NAME),
                &[ty],
                span,
                arena,
            )
            .is_ok()
}
