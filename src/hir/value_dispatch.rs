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
    ast::{Path, UnnamedArg},
    compiler::error::InternalCompilationError,
    containers::{SVec2, b},
    hir::{
        self, NodeArena, NodeId, NodeKind,
        dictionary::{DictElaborationCtx, find_trait_impl_dict_index},
        elaboration::trait_dictionary_evidence_binding,
        emit_value_impl::function_value_method,
        function::{ArgConvention, arg_conventions_for_args},
    },
    internal_compilation_error,
    module::{
        self, EvidenceBindingId, FunctionId, LocalDecl, LocalDeclId, LocalStorage,
        PendingLocalClone, PendingLocalDrop, ResolvedLocalClone, ResolvedLocalDrop, id::Id,
    },
    std::{
        core_traits_names::VALUE_TRAIT_NAME,
        string::{STRING_FROM_STATIC_FUNCTION_NAME, static_str_type, string_type},
        value::{
            VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX, generated_value_evidence_types,
            is_function_surface_only_value_type,
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

/// Build the ordinary owned-value materialization for compiler string data.
pub(crate) fn materialize_static_string(
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    trait_solver: &mut TraitSolver<'_>,
    value: &str,
    span: Location,
) -> Result<NodeId, InternalCompilationError> {
    let representation = arena.alloc(hir::Node::new(
        hir::hir_syn::static_str(value),
        static_str_type(),
        EffType::empty(),
        span,
    ));
    let function = trait_solver.get_local_or_import_function(
        span,
        &module::Path::single_str("std"),
        crate::ustr(STRING_FROM_STATIC_FUNCTION_NAME),
    )?;
    static_apply_generated_with_locals(
        arena,
        locals,
        trait_solver,
        function,
        [(representation, static_str_type())],
        string_type(),
        span,
    )
}

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
    Dictionary(EvidenceBindingId),
}

/// Resolve a required `Value` method into either a static function or a runtime dictionary slot.
fn resolve_value_method_dispatch(
    arena: &mut NodeArena,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    ty: Type,
    method_index: TraitMethodIndex,
    span: Location,
) -> Result<ResolvedValueMethodDispatch, InternalCompilationError> {
    let current_module = ctx.trait_solver.current_type_items.module.id;
    if ty.is_function() {
        return Ok(ResolvedValueMethodDispatch::Static(FunctionId::new(
            current_module,
            function_value_method(ctx.trait_solver, method_index, span)?,
        )));
    }
    let value_trait_id = ctx.trait_solver.std_trait_id(VALUE_TRAIT_NAME);
    if let Some(dict_index) = find_trait_impl_dict_index(ctx.dicts, value_trait_id, &[ty]) {
        return Ok(ResolvedValueMethodDispatch::Dictionary(
            EvidenceBindingId::from_index(dict_index),
        ));
    }
    if ty.is_constant()
        || is_function_surface_only_value_type(ty)
        || generated_value_evidence_types(ty, ctx.trait_solver).is_some()
    {
        return Ok(ResolvedValueMethodDispatch::Dictionary(
            trait_dictionary_evidence_binding(arena, value_trait_id, &[ty], &[], &[], span, ctx)?,
        ));
    }
    // The type is still open but its function has no inferred `Value` requirement. This is missing
    // source evidence, even if a late best-effort derivation could manufacture some concrete
    // artifact from the partially known shape.
    Err(internal_compilation_error!(TraitImplNotFound {
        trait_ref: value_trait_id,
        input_tys: vec![ty],
        fn_span: span,
    }))
}

pub(crate) fn resolve_local_clone(
    arena: &mut NodeArena,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    ty: Type,
    span: Location,
) -> Result<ResolvedLocalClone, InternalCompilationError> {
    if ctx
        .trait_solver
        .solve_concrete_trivial_copy_layout(ty, span)?
        .is_some()
    {
        return Ok(ResolvedLocalClone::TrivialCopy);
    }
    let dispatch = resolve_value_method_dispatch(arena, ctx, ty, VALUE_CLONE_METHOD_INDEX, span)?;
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
    if ctx
        .trait_solver
        .solve_concrete_trivial_copy_layout(ty, span)?
        .is_some()
    {
        return Ok(PendingLocalDrop::Resolved(ResolvedLocalDrop::Skip));
    }
    let dispatch = resolve_value_method_dispatch(arena, ctx, ty, VALUE_DROP_METHOD_INDEX, span)?;
    Ok(PendingLocalDrop::Resolved(match dispatch {
        ResolvedValueMethodDispatch::Static(function) => ResolvedLocalDrop::Static(function),
        ResolvedValueMethodDispatch::Dictionary(dictionary) => {
            ResolvedLocalDrop::Dictionary(dictionary)
        }
    }))
}

/// Build a generated static call, materializing non-place indirect `Let`
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

/// Build a generated trait call without baking the selected implementation's hidden evidence into
/// the caller. Final elaboration projects the method from the closed dictionary, just like a
/// source-level trait call.
#[allow(clippy::too_many_arguments)]
pub(crate) fn trait_apply_generated_with_locals(
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    trait_solver: &mut TraitSolver<'_>,
    trait_id: crate::module::TraitId,
    input_tys: Vec<Type>,
    method_index: TraitMethodIndex,
    arguments: impl IntoIterator<Item = NodeId>,
    span: Location,
) -> Result<NodeId, InternalCompilationError> {
    let (method_name, definition) = {
        let trait_def = trait_solver.trait_def(trait_id);
        let method_name = trait_def.method(method_index).0;
        let definition = trait_def
            .instantiate_for_tys(&input_tys, &[], &[])
            .into_iter()
            .nth(method_index.as_index())
            .expect("the method index belongs to this trait");
        (method_name, definition)
    };
    let mut arguments: Vec<_> = arguments.into_iter().collect();
    let prepared = prepare_generated_call_arguments_with_locals(
        arena,
        locals,
        trait_solver,
        &mut arguments,
        &definition.ty_scheme.ty.args,
        span,
    )?;
    let arguments =
        hir::CallArgument::from_values_and_passing(arguments, prepared.argument_passing);
    let ret_ty = definition.ty_scheme.ty.ret;
    let effects = definition.ty_scheme.ty.effects.clone();
    let call = arena.alloc(hir::Node::new(
        NodeKind::TraitMethodApply(b(hir::TraitMethodApplication {
            trait_id,
            method_index,
            method_path: Path::single(method_name, span),
            method_span: span,
            arguments,
            arguments_unnamed: UnnamedArg::All,
            ty: crate::types::r#type::CallImplType::new(
                definition.ty_scheme.ty,
                definition.result_convention,
            ),
            input_tys,
            inst_data: hir::FnInstData::none(),
        })),
        ret_ty,
        effects,
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
    pub argument_passing: Vec<ArgConvention>,
    pub temp_stores: Vec<NodeId>,
    pub cleanup: Vec<LocalDeclId>,
}

/// Materialize generated non-place indirect `Let` arguments as locals.
pub(crate) fn prepare_generated_call_arguments_with_locals(
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    trait_solver: &mut TraitSolver<'_>,
    arguments: &mut [NodeId],
    arg_tys: &[FnArgType],
    span: Location,
) -> Result<GeneratedCallArgumentPreparation, InternalCompilationError> {
    assert_eq!(arguments.len(), arg_tys.len());
    let mut temp_stores = Vec::new();
    let mut cleanup = Vec::new();

    for (arg, arg_ty) in arguments.iter_mut().zip(arg_tys) {
        if arg_ty
            .mut_ty
            .as_resolved()
            .is_some_and(|mut_ty| mut_ty.is_mutable())
            || !generated_let_argument_needs_temp(arena, trait_solver, *arg, arg_ty.ty, span)?
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
        // The concrete `Value<T>` implementation selected here may itself be a
        // dictionary constructor.  Leave dispatch unresolved until final HIR
        // elaboration, where the function's evidence context is available.
        validate_generated_temp_drop(arena, trait_solver, ty, span)?;
        local.set_owned_storage(PendingLocalDrop::Unknown);
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

    let argument_passing = arg_conventions_for_args(arg_tys);
    Ok(GeneratedCallArgumentPreparation {
        argument_passing,
        temp_stores,
        cleanup,
    })
}

/// Preserve the source-error check performed while generated argument temporaries are introduced,
/// but defer recording the selected dispatch until final evidence elaboration can close it.
fn validate_generated_temp_drop(
    arena: &mut NodeArena,
    trait_solver: &mut TraitSolver<'_>,
    ty: Type,
    span: Location,
) -> Result<(), InternalCompilationError> {
    if trait_solver
        .solve_concrete_trivial_copy_layout(ty, span)?
        .is_some()
        || is_function_surface_only_value_type(ty)
        || generated_value_evidence_types(ty, trait_solver).is_some()
    {
        return Ok(());
    }
    let _validated_drop = trait_solver.solve_impl_method(
        trait_solver.std_trait_id(VALUE_TRAIT_NAME),
        &[ty],
        VALUE_DROP_METHOD_INDEX,
        span,
        arena,
    )?;
    Ok(())
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

fn generated_let_argument_needs_temp(
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
            .solve_concrete_trivial_copy_layout(ty, span)?
            .is_none())
}
