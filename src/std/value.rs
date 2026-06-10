// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::mem;

use ustr::ustr;

use crate::{
    FxHashSet, Location,
    ast::{Path, UnnamedArg},
    compiler::error::InternalCompilationError,
    containers::b,
    eval::{
        EvalControlFlowResult, EvalCtx, PlaceResult, RuntimeError, ValOrMut, ValOrMutArgs, cont,
    },
    hir::function::{
        BinaryNativeFnRWN, ContextNativeFn, Function, FunctionDefinition, PendingScriptFunction,
        ResolvedArgPassing, ResolvedValueArgPassing, UnaryNativeFnMN,
    },
    hir::value::{FunctionValue, LiteralValue, NativeValue, Value, ustr_to_isize},
    hir::{self, CallArgument, NodeArena, NodeId},
    hir::{
        emit_value_impl::function_value_method,
        value_dispatch::{
            prepare_generated_call_arguments_with_locals, static_apply_generated_with_locals,
            wrap_generated_call_with_temp_cleanup,
        },
    },
    internal_compilation_error,
    module::{
        self, ConcreteTraitImplKey, FunctionId, LocalDecl, LocalDeclId, Module, ModuleEnv,
        ModuleFunction, PendingFunctionBody, PendingModuleFunction, ProjectionIndex,
        ResolvedValueLayout, TraitId, TraitImpl, TraitImplId, TraitImpls, TypeDefId, id::Id,
    },
    std::{
        STD_MODULE_ID,
        core_traits_names::{INSPECT_TRAIT_NAME, VALUE_TRAIT_NAME},
        hash::hasher_type,
        logic::bool_type,
        math::int_type,
        string::string_type,
    },
    types::effects::{EffType, PrimitiveEffect},
    types::mutability::{MutType, MutVal},
    types::r#trait::{
        Deriver, Trait, TraitAssociatedConst, TraitAssociatedConstIndex, TraitMethodIndex,
    },
    types::trait_solver::TraitSolver,
    types::r#type::{
        FnArgType, FnReturnConvention, FnType, Type, TypeDef, TypeKind, bare_native_type,
        tuple_type,
    },
    types::type_like::TypeLike,
    types::type_scheme::TypeScheme,
};

pub(crate) fn equal<T>(lhs: T, rhs: T) -> bool
where
    T: std::cmp::Eq,
{
    lhs == rhs
}

pub(crate) const VALUE_EQ_METHOD_INDEX: TraitMethodIndex = TraitMethodIndex(0);
pub(crate) const VALUE_TO_STRING_METHOD_INDEX: TraitMethodIndex = TraitMethodIndex(1);
pub(crate) const VALUE_HASH_METHOD_INDEX: TraitMethodIndex = TraitMethodIndex(2);
pub(crate) const VALUE_CLONE_METHOD_INDEX: TraitMethodIndex = TraitMethodIndex(3);
pub(crate) const VALUE_DROP_METHOD_INDEX: TraitMethodIndex = TraitMethodIndex(4);
pub(crate) const VALUE_SIZE_ASSOC_CONST_INDEX: TraitAssociatedConstIndex =
    TraitAssociatedConstIndex(0);
pub(crate) const VALUE_ALIGN_ASSOC_CONST_INDEX: TraitAssociatedConstIndex =
    TraitAssociatedConstIndex(1);
pub(crate) const INSPECT_METHOD_INDEX: TraitMethodIndex = TraitMethodIndex(0);
pub(crate) const NO_DERIVE_VALUE_ATTRIBUTE: &str = "no_derive_value";
pub(crate) const UNINIT_TYPE_NAME: &str = "Uninit";

const SHARED_REF: ResolvedArgPassing =
    ResolvedArgPassing::Value(ResolvedValueArgPassing::SharedRef);
const MUTABLE_REF: ResolvedArgPassing = ResolvedArgPassing::MutableRef;

#[derive(Debug)]
pub(crate) struct UninitStorage;

pub(crate) fn uninit_type(inner: Type) -> Type {
    Type::native::<UninitStorage>([inner])
}

pub(crate) fn uninit_inner_type(ty: Type) -> Option<Type> {
    let data = ty.data();
    let native = data.as_native()?;
    if native.bare_ty == bare_native_type::<UninitStorage>() && native.arguments.len() == 1 {
        Some(native.arguments[0])
    } else {
        None
    }
}

pub(crate) fn native_layout_associated_consts<T>() -> Vec<LiteralValue> {
    let mut values = [0; 2];
    values[usize::from(VALUE_SIZE_ASSOC_CONST_INDEX)] = mem::size_of::<T>() as isize;
    values[usize::from(VALUE_ALIGN_ASSOC_CONST_INDEX)] = mem::align_of::<T>() as isize;
    values.into_iter().map(LiteralValue::new_native).collect()
}

pub(crate) fn native_value_clone<T: Clone + NativeValue>(source: &T, target: &mut Value) {
    assert!(
        matches!(target, Value::Uninit),
        "Value::clone target storage must be uninitialized"
    );
    *target = Value::native(source.clone());
}

pub(crate) fn native_value_clone_function<T: Clone + NativeValue>() -> Function {
    b(BinaryNativeFnRWN::new(native_value_clone::<T>)) as Function
}

pub(crate) fn native_value_drop<T>(_target: &mut T) {}

pub(crate) fn native_value_drop_function<T: 'static>() -> Function {
    b(UnaryNativeFnMN::new(native_value_drop::<T>)) as Function
}

fn take_init_value(arg: ValOrMut, ctx: &mut EvalCtx<'_>, op: &str) -> Result<Value, RuntimeError> {
    match arg {
        ValOrMut::Val(value) => {
            assert!(
                !matches!(value, Value::Uninit),
                "{op} received uninitialized value storage"
            );
            Ok(value)
        }
        ValOrMut::Mut(place) => {
            let source = place.target_mut(ctx).map_err(RuntimeError::new_native)?;
            let value = mem::replace(source, Value::uninit());
            assert!(
                !matches!(value, Value::Uninit),
                "{op} received uninitialized value storage"
            );
            Ok(value)
        }
        ValOrMut::Dictionary(_) => panic!("{op} cannot move trait dictionary metadata"),
        ValOrMut::Ref(_) => panic!("{op} requires owned or mutable storage"),
    }
}

fn uninit_native(_args: ValOrMutArgs, _ctx: &mut EvalCtx) -> EvalControlFlowResult {
    cont(Value::uninit())
}

fn write_init_native(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let target = args.next().unwrap().as_place().clone();
    let value = take_init_value(args.next().unwrap(), ctx, "write_init")?;
    let target_value = target.target_mut(ctx).map_err(RuntimeError::new_native)?;
    assert!(
        matches!(target_value, Value::Uninit),
        "write_init target storage must be uninitialized"
    );
    *target_value = value;
    cont(Value::unit())
}

fn assume_init_native(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let value = take_init_value(args.next().unwrap(), ctx, "assume_init")?;
    cont(value)
}

fn assume_init_mut_native(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let target = args.next().unwrap().as_place().clone();
    let target_value = target.target_mut(ctx).map_err(RuntimeError::new_native)?;
    assert!(
        !matches!(target_value, Value::Uninit),
        "assume_init_mut target storage must be initialized"
    );
    cont(Value::native(PlaceResult::new(target)))
}

#[derive(Debug, Clone, Copy)]
struct ValueLayout {
    size: usize,
    align: usize,
}

impl ValueLayout {
    fn new(size: usize, align: usize) -> Self {
        assert!(align > 0, "type alignment must be non-zero");
        Self { size, align }
    }

    fn native<T>() -> Self {
        Self::new(mem::size_of::<T>(), mem::align_of::<T>())
    }

    fn associated_const_values(
        self,
        span: Location,
    ) -> Result<[isize; 2], InternalCompilationError> {
        let mut values = [0; 2];
        values[usize::from(VALUE_SIZE_ASSOC_CONST_INDEX)] =
            isize::try_from(self.size).map_err(|_| {
                internal_compilation_error!(Internal {
                    error: format!("Value size {} does not fit in int", self.size),
                    span,
                })
            })?;
        values[usize::from(VALUE_ALIGN_ASSOC_CONST_INDEX)] =
            isize::try_from(self.align).map_err(|_| {
                internal_compilation_error!(Internal {
                    error: format!("Value alignment {} does not fit in int", self.align),
                    span,
                })
            })?;
        Ok(values)
    }

    fn product(fields: impl IntoIterator<Item = ValueLayout>) -> Self {
        let mut size = 0;
        let mut align = 1;
        for field in fields {
            size = align_to(size, field.align);
            size += field.size;
            align = align.max(field.align);
        }
        Self::new(align_to(size, align), align)
    }

    fn union(fields: impl IntoIterator<Item = ValueLayout>) -> Self {
        let mut size = 0;
        let mut align = 1;
        for field in fields {
            size = size.max(field.size);
            align = align.max(field.align);
        }
        Self::new(align_to(size, align), align)
    }

    fn variant(payloads: impl IntoIterator<Item = ValueLayout>) -> Self {
        let tag = Self::native::<isize>();
        let payload = Self::union(payloads);
        let align = tag.align.max(payload.align);
        let payload_offset = align_to(tag.size, payload.align);
        Self::new(align_to(payload_offset + payload.size, align), align)
    }
}

fn align_to(offset: usize, align: usize) -> usize {
    debug_assert!(align > 0);
    let rem = offset % align;
    if rem == 0 {
        offset
    } else {
        offset + (align - rem)
    }
}

pub(crate) trait TypeLayoutEnv {
    fn type_def(&self, id: TypeDefId) -> &TypeDef;
}

impl TypeLayoutEnv for ModuleEnv<'_> {
    fn type_def(&self, id: TypeDefId) -> &TypeDef {
        ModuleEnv::type_def(self, id)
    }
}

impl TypeLayoutEnv for TraitSolver<'_> {
    fn type_def(&self, id: TypeDefId) -> &TypeDef {
        TraitSolver::type_def(self, id)
    }
}

fn layout_for_value_type(
    ty: Type,
    span: Location,
    active: &mut FxHashSet<Type>,
    env: &impl TypeLayoutEnv,
) -> Result<ValueLayout, InternalCompilationError> {
    if let Some(inner_ty) = uninit_inner_type(ty) {
        return layout_for_value_type(inner_ty, span, active, env);
    }

    if !active.insert(ty) {
        // Recursive occurrences are represented indirectly at runtime, so their
        // inline layout is a value slot rather than another full copy.
        return Ok(ValueLayout::native::<usize>());
    }

    let ty_data = ty.data();
    use TypeKind::*;
    let layout = match &*ty_data {
        Native(native) => {
            ValueLayout::new(native.bare_ty.value_size(), native.bare_ty.value_align())
        }
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            let fields = member_tys
                .into_iter()
                .map(|member_ty| layout_for_value_type(member_ty, span, active, env))
                .collect::<Result<Vec<_>, _>>()?;
            active.remove(&ty);
            return Ok(ValueLayout::product(fields));
        }
        Record(fields) => {
            let field_tys = fields
                .iter()
                .map(|(_, field_ty)| *field_ty)
                .collect::<Vec<_>>();
            drop(ty_data);
            let fields = field_tys
                .into_iter()
                .map(|field_ty| layout_for_value_type(field_ty, span, active, env))
                .collect::<Result<Vec<_>, _>>()?;
            active.remove(&ty);
            return Ok(ValueLayout::product(fields));
        }
        Variant(variants) => {
            let payload_tys = variants
                .iter()
                .map(|(_, payload_ty)| *payload_ty)
                .collect::<Vec<_>>();
            drop(ty_data);
            let payloads = payload_tys
                .into_iter()
                .map(|payload_ty| layout_for_value_type(payload_ty, span, active, env))
                .collect::<Result<Vec<_>, _>>()?;
            active.remove(&ty);
            return Ok(ValueLayout::variant(payloads));
        }
        Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let shape_ty = env.type_def(named.def).instantiated_shape(&named.params);
            let layout = layout_for_value_type(shape_ty, span, active, env)?;
            active.remove(&ty);
            return Ok(layout);
        }
        Function(_) => ValueLayout::native::<FunctionValue>(),
        Never => ValueLayout::product([]),
        Variable(_) => {
            drop(ty_data);
            active.remove(&ty);
            return Err(internal_compilation_error!(Internal {
                error: format!("cannot compute Value layout for type {ty:?}"),
                span,
            }));
        }
    };
    drop(ty_data);
    active.remove(&ty);
    Ok(layout)
}

pub(crate) fn value_layout_for_type(
    ty: Type,
    span: Location,
    env: &impl TypeLayoutEnv,
) -> Result<ResolvedValueLayout, InternalCompilationError> {
    let layout = layout_for_value_type(ty, span, &mut FxHashSet::default(), env)?;
    let size = u32::try_from(layout.size).map_err(|_| {
        internal_compilation_error!(Internal {
            error: format!("Value size {} does not fit in u32", layout.size),
            span,
        })
    })?;
    let align = u32::try_from(layout.align).map_err(|_| {
        internal_compilation_error!(Internal {
            error: format!("Value alignment {} does not fit in u32", layout.align),
            span,
        })
    })?;
    Ok(ResolvedValueLayout { size, align })
}

pub(crate) fn value_layout_associated_const_values(
    ty: Type,
    span: Location,
    env: &impl TypeLayoutEnv,
) -> Result<[isize; 2], InternalCompilationError> {
    layout_for_value_type(ty, span, &mut FxHashSet::default(), env)?.associated_const_values(span)
}

/// Return whether all unresolved variables in `ty` appear only in function types.
/// `active` is the current recursion stack used to stop on recursive types.
fn value_type_is_resolved_ignoring_function_surface(
    ty: Type,
    active: &mut FxHashSet<Type>,
) -> bool {
    if ty.is_constant() {
        return true;
    }
    if !active.insert(ty) {
        return true;
    }

    let ty_data = ty.data();
    use TypeKind::*;
    let resolved = match &*ty_data {
        Function(_) => true,
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            let resolved = member_tys.into_iter().all(|member_ty| {
                value_type_is_resolved_ignoring_function_surface(member_ty, active)
            });
            active.remove(&ty);
            return resolved;
        }
        Record(fields) => {
            let field_tys = fields
                .iter()
                .map(|(_, field_ty)| *field_ty)
                .collect::<Vec<_>>();
            drop(ty_data);
            let resolved = field_tys
                .into_iter()
                .all(|field_ty| value_type_is_resolved_ignoring_function_surface(field_ty, active));
            active.remove(&ty);
            return resolved;
        }
        Variant(variants) => {
            let payload_tys = variants
                .iter()
                .map(|(_, payload_ty)| *payload_ty)
                .collect::<Vec<_>>();
            drop(ty_data);
            let resolved = payload_tys.into_iter().all(|payload_ty| {
                value_type_is_resolved_ignoring_function_surface(payload_ty, active)
            });
            active.remove(&ty);
            return resolved;
        }
        Named(named) => {
            let param_tys = named.params.clone();
            drop(ty_data);
            let resolved = param_tys
                .into_iter()
                .all(|param_ty| value_type_is_resolved_ignoring_function_surface(param_ty, active));
            active.remove(&ty);
            return resolved;
        }
        Native(_) => false,
        Never => true,
        Variable(_) => false,
    };
    drop(ty_data);
    active.remove(&ty);
    resolved
}

/// True when every unresolved part of `ty` appears under a function type.
/// Function `Value` impls are compiler-provided from their hidden closure env,
/// so these types can use generated structural `Value` code without requiring a
/// user-visible dictionary for the function surface.
pub(crate) fn is_function_surface_only_value_type(ty: Type) -> bool {
    !ty.is_constant()
        && value_type_is_resolved_ignoring_function_surface(ty, &mut FxHashSet::default())
}

/// Return whether this is `Value` for a type whose unresolved variables occur only inside function types.
pub(crate) fn is_function_surface_only_value_trait_application(
    trait_id: TraitId,
    trait_def: &Trait,
    input_tys: &[Type],
    output_tys: &[Type],
) -> bool {
    is_value_trait(trait_id, trait_def)
        && input_tys.len() == 1
        && output_tys.is_empty()
        && is_function_surface_only_value_type(input_tys[0])
}

/// Return whether this trait application is `Value` for a function type.
pub(crate) fn is_value_trait_for_function_type(
    trait_id: TraitId,
    trait_def: &Trait,
    input_tys: &[Type],
    output_tys: &[Type],
) -> bool {
    is_value_trait(trait_id, trait_def)
        && input_tys.len() == 1
        && output_tys.is_empty()
        && input_tys[0].is_function()
}

pub(crate) fn is_value_trait(trait_id: TraitId, trait_def: &Trait) -> bool {
    trait_id.module == STD_MODULE_ID && trait_def.name == VALUE_TRAIT_NAME
}

use FunctionDefinition as Def;

pub(crate) type ValueCodeEntries = Vec<(PendingFunctionBody, Vec<LocalDecl>)>;

struct ValueBodyCtx<'s, 'm> {
    solver: &'s mut TraitSolver<'m>,
    emit_generic_trait_calls: bool,
}

impl<'s, 'm> ValueBodyCtx<'s, 'm> {
    fn concrete(solver: &'s mut TraitSolver<'m>) -> Self {
        Self {
            solver,
            emit_generic_trait_calls: false,
        }
    }

    pub(crate) fn generic(solver: &'s mut TraitSolver<'m>) -> Self {
        Self {
            solver,
            emit_generic_trait_calls: true,
        }
    }

    fn get_local_or_import_function(
        &mut self,
        span: Location,
        module_path: &module::Path,
        function_name: ustr::Ustr,
    ) -> Result<FunctionId, InternalCompilationError> {
        self.solver
            .get_local_or_import_function(span, module_path, function_name)
    }

    fn value_method_call(
        &mut self,
        method: ValueMethod,
        span: Location,
        arena: &mut NodeArena,
        locals: &mut Vec<LocalDecl>,
        mut arguments: Vec<NodeId>,
    ) -> Result<NodeId, InternalCompilationError> {
        let ValueMethod {
            trait_id,
            input_ty,
            method_index,
        } = method;
        let (fn_ty, ret_ty, method_name, is_function_value) = {
            let trait_def = self.solver.trait_def(trait_id);
            let definition = trait_def
                .instantiate_for_tys(&[input_ty], &[])
                .into_iter()
                .nth(method_index.as_index())
                .expect("Value method index out of bounds");
            let fn_ty = definition.ty_scheme.ty;
            let ret_ty = fn_ty.ret;
            let method_name = trait_def.method(method_index).0;
            let is_function_value =
                is_value_trait_for_function_type(trait_id, trait_def, &[input_ty], &[]);
            (fn_ty, ret_ty, method_name, is_function_value)
        };

        if is_function_value {
            let function =
                FunctionId::Local(function_value_method(self.solver, method_index, span)?);
            let effects = fn_ty.effects.clone();
            let prepared = prepare_generated_call_arguments_with_locals(
                arena,
                locals,
                self.solver,
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
                effects,
                span,
            ));
            return Ok(wrap_generated_call_with_temp_cleanup(
                arena,
                prepared.temp_stores,
                prepared.cleanup,
                call,
                ret_ty,
                span,
            ));
        }

        if self.emit_generic_trait_calls && !input_ty.is_constant() {
            let effects = fn_ty.effects.clone();
            let prepared = prepare_generated_call_arguments_with_locals(
                arena,
                locals,
                self.solver,
                &mut arguments,
                &fn_ty.args,
                span,
            )?;
            let arguments =
                CallArgument::from_values_and_passing(arguments, prepared.argument_passing);
            let call = arena.alloc(hir::Node::new(
                hir::NodeKind::TraitMethodApply(crate::containers::b(
                    hir::TraitMethodApplication {
                        trait_id,
                        method_index,
                        method_path: Path::single(method_name, span),
                        method_span: span,
                        arguments,
                        arguments_unnamed: UnnamedArg::All,
                        ty: fn_ty,
                        input_tys: vec![input_ty],
                        inst_data: hir::FnInstData::none(),
                    },
                )),
                ret_ty,
                effects,
                span,
            ));
            return Ok(wrap_generated_call_with_temp_cleanup(
                arena,
                prepared.temp_stores,
                prepared.cleanup,
                call,
                ret_ty,
                span,
            ));
        }

        let function =
            self.solver
                .solve_impl_method(trait_id, &[input_ty], method_index, span, arena)?;
        let prepared = prepare_generated_call_arguments_with_locals(
            arena,
            locals,
            self.solver,
            &mut arguments,
            &fn_ty.args,
            span,
        )?;
        let effects = fn_ty.effects.clone();
        let call = arena.alloc(hir::Node::new(
            hir::hir_syn::static_apply_with_argument_passing(
                function,
                fn_ty,
                arguments,
                prepared.argument_passing,
                span,
            ),
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
}

#[derive(Clone, Copy)]
struct ValueMethod {
    trait_id: TraitId,
    input_ty: Type,
    method_index: TraitMethodIndex,
}

fn value_method_call_node(
    ctx: &mut ValueBodyCtx<'_, '_>,
    method: ValueMethod,
    span: Location,
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    arguments: Vec<NodeId>,
) -> Result<NodeId, InternalCompilationError> {
    ctx.value_method_call(method, span, arena, locals, arguments)
}

const FUNCTION_VALUE_METHOD_NAMES: [&str; 5] = [
    "$_ferlium_function_value_eq",
    "$_ferlium_function_value_to_string",
    "$_ferlium_function_value_hash",
    "$_ferlium_function_value_clone",
    "$_ferlium_function_value_drop",
];

pub(crate) fn function_value_method_name(method_index: TraitMethodIndex) -> ustr::Ustr {
    ustr::Ustr::from(FUNCTION_VALUE_METHOD_NAMES[usize::from(method_index)])
}

fn alloc_synth_node(arena: &mut NodeArena, kind: hir::NodeKind, ty: Type) -> NodeId {
    arena.alloc(hir::Node::new(
        kind,
        ty,
        EffType::empty(),
        Location::new_synthesized(),
    ))
}

fn variant_payload_storage_type(payload_ty: Type) -> Type {
    if payload_ty == Type::unit() {
        return payload_ty;
    }
    let payload_data = payload_ty.data();
    let stores_payload_directly =
        matches!(&*payload_data, TypeKind::Tuple(_) | TypeKind::Record(_));
    drop(payload_data);
    if stores_payload_directly {
        payload_ty
    } else {
        tuple_type([payload_ty])
    }
}

fn variant_payload_project(
    arena: &mut NodeArena,
    variant_value: NodeId,
    payload_ty: Type,
) -> NodeId {
    let storage_ty = variant_payload_storage_type(payload_ty);
    let storage = alloc_synth_node(
        arena,
        hir::hir_syn::project(variant_value, ProjectionIndex::from_index(0)),
        storage_ty,
    );
    if storage_ty == payload_ty {
        storage
    } else {
        alloc_synth_node(
            arena,
            hir::hir_syn::project(storage, ProjectionIndex::from_index(0)),
            payload_ty,
        )
    }
}

fn variant_payload_storage_node(
    arena: &mut NodeArena,
    payload: NodeId,
    payload_ty: Type,
) -> NodeId {
    let storage_ty = variant_payload_storage_type(payload_ty);
    if storage_ty == payload_ty {
        payload
    } else {
        alloc_synth_node(arena, hir::hir_syn::tuple([payload]), storage_ty)
    }
}

fn function_value_clone_root(
    ty: Type,
    source_id: LocalDeclId,
    target_id: LocalDeclId,
    arena: &mut NodeArena,
) -> NodeId {
    use hir::hir_syn::*;

    let source = alloc_synth_node(arena, load_local(source_id), ty);
    // The clone target is typed as `Uninit<T>` at the trait boundary. Generated
    // clone glue reinterprets it as `T` only after writing initialized storage.
    let target = alloc_synth_node(arena, load_local(target_id), ty);
    alloc_synth_node(
        arena,
        hir::NodeKind::CloneClosureEnv(hir::CloneClosureEnv { source, target }),
        Type::unit(),
    )
}

fn function_value_clone_body(ty: Type, arena: &mut NodeArena) -> (NodeId, Vec<LocalDecl>) {
    use hir::hir_syn::*;

    let source_id = LocalDeclId::from_index(0);
    let target_id = LocalDeclId::from_index(1);
    let uninit_ty = uninit_type(ty);
    let locals = vec![
        local("source", ty),
        LocalDecl::new(
            (crate::ustr("target"), Location::new_synthesized()),
            MutType::mutable(),
            uninit_ty,
            None,
            Location::new_synthesized(),
        ),
    ];
    let root = function_value_clone_root(ty, source_id, target_id, arena);
    (root, locals)
}

fn function_value_drop_root(ty: Type, target_id: LocalDeclId, arena: &mut NodeArena) -> NodeId {
    use hir::hir_syn::*;

    let target = alloc_synth_node(arena, load_local(target_id), ty);
    alloc_synth_node(
        arena,
        hir::NodeKind::DropClosureEnv(hir::DropClosureEnv { target }),
        Type::unit(),
    )
}

fn function_value_drop_body(ty: Type, arena: &mut NodeArena) -> (NodeId, Vec<LocalDecl>) {
    let target_id = LocalDeclId::from_index(0);
    let locals = vec![LocalDecl::new(
        (crate::ustr("target"), Location::new_synthesized()),
        MutType::mutable(),
        ty,
        None,
        Location::new_synthesized(),
    )];
    let root = function_value_drop_root(ty, target_id, arena);
    (root, locals)
}

pub(crate) fn function_value_method_function(
    method_index: TraitMethodIndex,
    span: Location,
    solver: &mut TraitSolver<'_>,
) -> Result<PendingModuleFunction, InternalCompilationError> {
    use hir::hir_syn::*;

    let mut arena = NodeArena::default();
    let ty = Type::variable_id(0);
    let unit_ty = Type::unit();
    let (definition, root, locals) = match method_index {
        VALUE_EQ_METHOD_INDEX => {
            let fn_ty = FnType::new_by_val([ty, ty], bool_type(), EffType::empty());
            let definition = Def::new_infer_quantifiers(
                fn_ty,
                ["left", "right"],
                "Compiler-generated function Value equality.",
            );
            let locals = vec![local("left", ty), local("right", ty)];
            let root = alloc_synth_node(&mut arena, native(false), bool_type());
            (definition, root, locals)
        }
        VALUE_TO_STRING_METHOD_INDEX => {
            let fn_ty = FnType::new_by_val([ty], string_type(), EffType::empty());
            let definition = Def::new_infer_quantifiers(
                fn_ty,
                ["self"],
                "Compiler-generated function Value string conversion.",
            );
            let locals = vec![local("self", ty)];
            let root = alloc_synth_node(&mut arena, native_str("<function>"), string_type());
            (definition, root, locals)
        }
        VALUE_HASH_METHOD_INDEX => {
            let hasher_ty = hasher_type();
            let hasher_write_string = solver.get_local_or_import_function(
                span,
                &module::Path::single_str("std"),
                crate::ustr("hasher_write_string"),
            )?;
            let fn_ty = FnType::new(
                vec![
                    FnArgType::new_by_val(ty),
                    FnArgType::new(hasher_ty, MutType::mutable()),
                ],
                unit_ty,
                EffType::empty(),
            );
            let definition = Def::new_infer_quantifiers(
                fn_ty,
                ["self", "state"],
                "Compiler-generated function Value hashing.",
            );
            let state_id = LocalDeclId::from_index(1);
            let mut locals = vec![
                local("self", ty),
                LocalDecl::new(
                    (crate::ustr("state"), Location::new_synthesized()),
                    MutType::mutable(),
                    hasher_ty,
                    None,
                    Location::new_synthesized(),
                ),
            ];
            let state = alloc_synth_node(&mut arena, load_local(state_id), hasher_ty);
            let marker = alloc_synth_node(&mut arena, native_str("<function>"), string_type());
            let write = static_apply_generated_with_locals(
                &mut arena,
                &mut locals,
                solver,
                hasher_write_string,
                [(state, hasher_ty), (marker, string_type())],
                unit_ty,
                span,
            )?;
            let unit = alloc_synth_node(&mut arena, native(()), unit_ty);
            let root = alloc_synth_node(&mut arena, block([write, unit]), unit_ty);
            (definition, root, locals)
        }
        VALUE_CLONE_METHOD_INDEX => {
            let fn_ty = FnType::new(
                vec![
                    FnArgType::new_by_val(ty),
                    FnArgType::new(ty, MutType::mutable()),
                ],
                unit_ty,
                EffType::empty(),
            );
            let definition = Def::new_infer_quantifiers(
                fn_ty,
                ["source", "target"],
                "Compiler-generated function Value clone.",
            );
            let (root, locals) = function_value_clone_body(ty, &mut arena);
            (definition, root, locals)
        }
        VALUE_DROP_METHOD_INDEX => {
            let fn_ty = FnType::new(
                vec![FnArgType::new(ty, MutType::mutable())],
                unit_ty,
                EffType::empty(),
            );
            let definition = Def::new_infer_quantifiers(
                fn_ty,
                ["target"],
                "Compiler-generated function Value drop.",
            );
            let (root, locals) = function_value_drop_body(ty, &mut arena);
            (definition, root, locals)
        }
        _ => panic!("function Value method index out of bounds"),
    };

    let runtime_arg_count = definition.arg_names.len();
    Ok(PendingModuleFunction::new(
        definition,
        PendingScriptFunction::new(arena, root, runtime_arg_count),
        None,
        locals,
    ))
}

fn derive_structural_text_body(
    trait_id: TraitId,
    method_index: TraitMethodIndex,
    input_types: &[Type],
    span: Location,
    arena: &mut NodeArena,
    ctx: &mut ValueBodyCtx<'_, '_>,
) -> Result<Option<(NodeId, Vec<LocalDecl>)>, InternalCompilationError> {
    use hir::hir_syn::*;

    assert!(input_types.len() == 1);
    let ty = input_types[0];
    assert!(ctx.emit_generic_trait_calls || ty.is_constant());

    let n = alloc_synth_node;

    let string_push_str = ctx.get_local_or_import_function(
        span,
        &module::Path::single_str("std"),
        crate::ustr("string_push_str"),
    )?;

    let string_lit = |arena: &mut NodeArena, text: &str| n(arena, native_str(text), string_type());
    macro_rules! build_text {
        ($arena:expr, $locals:expr, $value:expr, $value_ty:expr) => {
            value_method_call_node(
                ctx,
                ValueMethod {
                    trait_id,
                    input_ty: $value_ty,
                    method_index,
                },
                span,
                $arena,
                $locals,
                vec![$value],
            )
        };
    }
    let build_string_block = |arena: &mut NodeArena,
                              solver: &mut TraitSolver<'_>,
                              locals: &mut Vec<LocalDecl>,
                              initial: &str,
                              mut pieces: Vec<NodeId>|
     -> Result<NodeId, InternalCompilationError> {
        let initial_value = string_lit(arena, initial);
        let next_local = locals.len();
        let (store_rendered, l_rendered_id) = store_new_local(
            initial_value,
            next_local,
            "rendered",
            MutVal::mutable(),
            string_type(),
            locals,
        );
        let mut statements = Vec::with_capacity(pieces.len() + 2);
        statements.push(n(arena, store_rendered, Type::unit()));
        for piece in pieces.drain(..) {
            let target = n(arena, load_local(l_rendered_id), string_type());
            let push = static_apply_generated_with_locals(
                arena,
                locals,
                solver,
                string_push_str,
                [(target, string_type()), (piece, string_type())],
                Type::unit(),
                span,
            )?;
            statements.push(push);
        }
        let rendered = n(arena, take_local_value(l_rendered_id), string_type());
        statements.push(rendered);
        Ok(n(arena, block(statements), string_type()))
    };

    let locals = vec![local("self", ty)];
    let l_self_id = LocalDeclId::from_index(0);

    let ty_data = ty.data();
    use TypeKind::*;
    let root = match &*ty_data {
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            let load_self = n(arena, load_local(l_self_id), ty);
            let mut locals = locals;
            let mut pieces = Vec::with_capacity(member_tys.len() * 2 + 1);
            for (index, member_ty) in member_tys.into_iter().enumerate() {
                if index > 0 {
                    pieces.push(string_lit(arena, ", "));
                }
                let member = n(
                    arena,
                    project(load_self, ProjectionIndex::from_index(index)),
                    member_ty,
                );
                let member_str = build_text!(arena, &mut locals, member, member_ty)?;
                pieces.push(member_str);
            }
            pieces.push(string_lit(arena, ")"));
            Some((
                build_string_block(arena, ctx.solver, &mut locals, "(", pieces)?,
                locals,
            ))
        }
        Record(fields) => {
            let fields = fields.clone();
            drop(ty_data);
            let load_self = n(arena, load_local(l_self_id), ty);
            let mut locals = locals;
            let mut pieces = Vec::with_capacity(fields.len() * 4 + 1);
            for (index, (name, member_ty)) in fields.into_iter().enumerate() {
                if index > 0 {
                    pieces.push(string_lit(arena, ", "));
                }
                pieces.push(string_lit(arena, name.as_str()));
                pieces.push(string_lit(arena, ": "));
                let member = n(
                    arena,
                    project(load_self, ProjectionIndex::from_index(index)),
                    member_ty,
                );
                let member_str = build_text!(arena, &mut locals, member, member_ty)?;
                pieces.push(member_str);
            }
            pieces.push(string_lit(arena, " }"));
            Some((
                build_string_block(arena, ctx.solver, &mut locals, "{ ", pieces)?,
                locals,
            ))
        }
        Variant(variants) => {
            let variants = variants.clone();
            drop(ty_data);
            let self_value = n(arena, load_local(l_self_id), ty);
            let self_tag = n(arena, extract_tag(self_value), int_type());
            let mut locals = locals;
            let mut alternatives = Vec::with_capacity(variants.len());
            for (tag, payload_ty) in variants {
                let tag_val = LiteralValue::new_native(ustr_to_isize(tag));
                let rendered = if payload_ty == Type::unit() {
                    string_lit(arena, tag.as_str())
                } else {
                    let self_value = n(arena, load_local(l_self_id), ty);
                    let payload = variant_payload_project(arena, self_value, payload_ty);
                    let payload_str = build_text!(arena, &mut locals, payload, payload_ty)?;
                    if payload_ty.data().is_tuple() {
                        build_string_block(
                            arena,
                            ctx.solver,
                            &mut locals,
                            &format!("{} ", tag),
                            vec![payload_str],
                        )?
                    } else {
                        let close = string_lit(arena, ")");
                        build_string_block(
                            arena,
                            ctx.solver,
                            &mut locals,
                            &format!("{}(", tag),
                            vec![payload_str, close],
                        )?
                    }
                };
                alternatives.push((tag_val, rendered));
            }
            let default = string_lit(arena, "");
            Some((
                n(arena, case(self_tag, alternatives, default), string_type()),
                locals,
            ))
        }
        Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let type_def = ctx.solver.type_def(named.def);
            let type_name = type_def.name;
            let shape_ty = type_def.instantiated_shape(&named.params);
            let load_self = n(arena, load_local(l_self_id), ty);
            let mut locals = locals;
            let shape_data = shape_ty.data();
            let root = match &*shape_data {
                Tuple(member_tys) => {
                    let member_tys = member_tys.clone();
                    drop(shape_data);
                    let mut pieces = Vec::with_capacity(member_tys.len() * 2 + 1);
                    for (index, member_ty) in member_tys.into_iter().enumerate() {
                        if index > 0 {
                            pieces.push(string_lit(arena, ", "));
                        }
                        let member = n(
                            arena,
                            project(load_self, ProjectionIndex::from_index(index)),
                            member_ty,
                        );
                        pieces.push(build_text!(arena, &mut locals, member, member_ty)?);
                    }
                    pieces.push(string_lit(arena, ")"));
                    build_string_block(
                        arena,
                        ctx.solver,
                        &mut locals,
                        &format!("{} (", type_name),
                        pieces,
                    )?
                }
                Record(fields) => {
                    let fields = fields.clone();
                    drop(shape_data);
                    let mut pieces = Vec::with_capacity(fields.len() * 4 + 1);
                    for (index, (name, member_ty)) in fields.into_iter().enumerate() {
                        if index > 0 {
                            pieces.push(string_lit(arena, ", "));
                        }
                        pieces.push(string_lit(arena, name.as_str()));
                        pieces.push(string_lit(arena, ": "));
                        let member = n(
                            arena,
                            project(load_self, ProjectionIndex::from_index(index)),
                            member_ty,
                        );
                        pieces.push(build_text!(arena, &mut locals, member, member_ty)?);
                    }
                    pieces.push(string_lit(arena, " }"));
                    build_string_block(
                        arena,
                        ctx.solver,
                        &mut locals,
                        &format!("{} {{ ", type_name),
                        pieces,
                    )?
                }
                Variant(variants) => {
                    let variants = variants.clone();
                    drop(shape_data);
                    let self_tag = n(arena, extract_tag(load_self), int_type());
                    let mut alternatives = Vec::with_capacity(variants.len());
                    for (tag, payload_ty) in variants {
                        let tag_val = LiteralValue::new_native(ustr_to_isize(tag));
                        let rendered = if payload_ty == Type::unit() {
                            string_lit(arena, &format!("{}::{}", type_name, tag))
                        } else {
                            let self_value = n(arena, load_local(l_self_id), ty);
                            let payload = variant_payload_project(arena, self_value, payload_ty);
                            let payload_str = build_text!(arena, &mut locals, payload, payload_ty)?;
                            if payload_ty.data().is_tuple() {
                                build_string_block(
                                    arena,
                                    ctx.solver,
                                    &mut locals,
                                    &format!("{}::{} ", type_name, tag),
                                    vec![payload_str],
                                )?
                            } else {
                                let close = string_lit(arena, ")");
                                build_string_block(
                                    arena,
                                    ctx.solver,
                                    &mut locals,
                                    &format!("{}::{}(", type_name, tag),
                                    vec![payload_str, close],
                                )?
                            }
                        };
                        alternatives.push((tag_val, rendered));
                    }
                    let default = string_lit(arena, "");
                    n(arena, case(self_tag, alternatives, default), string_type())
                }
                Never => {
                    drop(shape_data);
                    string_lit(arena, &format!("{}::<empty>", type_name))
                }
                _ => {
                    drop(shape_data);
                    let load_self = n(arena, load_local(l_self_id), shape_ty);
                    let payload_str = build_text!(arena, &mut locals, load_self, shape_ty)?;
                    build_string_block(
                        arena,
                        ctx.solver,
                        &mut locals,
                        &format!("{} ", type_name),
                        vec![payload_str],
                    )?
                }
            };
            Some((root, locals))
        }
        Function(_) => {
            drop(ty_data);
            Some((string_lit(arena, "<function>"), locals))
        }
        _ => {
            drop(ty_data);
            None
        }
    };

    Ok(root)
}

fn derive_value_to_string_body(
    trait_id: TraitId,
    input_types: &[Type],
    span: Location,
    arena: &mut NodeArena,
    ctx: &mut ValueBodyCtx<'_, '_>,
) -> Result<Option<(NodeId, Vec<LocalDecl>)>, InternalCompilationError> {
    derive_structural_text_body(
        trait_id,
        VALUE_TO_STRING_METHOD_INDEX,
        input_types,
        span,
        arena,
        ctx,
    )
}

fn derive_inspect_body(
    trait_id: TraitId,
    input_types: &[Type],
    span: Location,
    arena: &mut NodeArena,
    ctx: &mut ValueBodyCtx<'_, '_>,
) -> Result<Option<(NodeId, Vec<LocalDecl>)>, InternalCompilationError> {
    derive_structural_text_body(
        trait_id,
        INSPECT_METHOD_INDEX,
        input_types,
        span,
        arena,
        ctx,
    )
}

#[derive(Debug, Clone)]
struct InspectDeriver;

impl Deriver for InspectDeriver {
    fn derive_impl(
        &self,
        trait_id: TraitId,
        input_types: &[Type],
        span: Location,
        _arena: &mut NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

        let snapshot = solver.snapshot_derived_impl_state();
        let impl_id =
            solver.reserve_concrete_impl_from_code_entries(trait_id, input_types, &[], []);
        let mut body_arena = NodeArena::default();
        let mut ctx = ValueBodyCtx::concrete(solver);
        let Some((root, locals)) =
            derive_inspect_body(trait_id, input_types, span, &mut body_arena, &mut ctx)?
        else {
            ctx.solver.rollback_derived_impl_state(snapshot);
            return Ok(None);
        };
        ctx.solver.replace_concrete_impl_code_entries(
            impl_id,
            trait_id,
            input_types,
            &[],
            [(PendingFunctionBody::new(body_arena, root), locals)],
        );
        Ok(Some(TraitImplId::Local(impl_id)))
    }
}

fn derive_value_eq_body(
    trait_id: TraitId,
    input_types: &[Type],
    span: Location,
    arena: &mut NodeArena,
    ctx: &mut ValueBodyCtx<'_, '_>,
) -> Result<Option<(NodeId, Vec<LocalDecl>)>, InternalCompilationError> {
    use hir::hir_syn::*;

    assert!(input_types.len() == 1);
    let ty = input_types[0];
    assert!(ctx.emit_generic_trait_calls || ty.is_constant());

    let n = alloc_synth_node;

    let bool_ty = bool_type();
    let mut locals = vec![local("left", ty), local("right", ty)];
    let l_left_id = LocalDeclId::from_index(0);
    let l_right_id = LocalDeclId::from_index(1);

    macro_rules! build_product_eq {
        ($arena:expr, $member_tys:expr) => {{
            let mut eq_pairs: Vec<NodeId> = Vec::new();
            for (index, member_ty) in $member_tys.into_iter().enumerate() {
                let load_left_i = n($arena, load_local(l_left_id), ty);
                let left_i = n(
                    $arena,
                    project(load_left_i, ProjectionIndex::from_index(index)),
                    member_ty,
                );
                let load_right_i = n($arena, load_local(l_right_id), ty);
                let right_i = n(
                    $arena,
                    project(load_right_i, ProjectionIndex::from_index(index)),
                    member_ty,
                );
                let eq_i = value_method_call_node(
                    ctx,
                    ValueMethod {
                        trait_id,
                        input_ty: member_ty,
                        method_index: VALUE_EQ_METHOD_INDEX,
                    },
                    span,
                    $arena,
                    &mut locals,
                    vec![left_i, right_i],
                )?;
                eq_pairs.push(eq_i);
            }
            let mut root = n($arena, native(true), bool_ty);
            for eq_i in eq_pairs.into_iter().rev() {
                let false_n = n($arena, native(false), bool_ty);
                root = n(
                    $arena,
                    case(eq_i, vec![(LiteralValue::new_native(true), root)], false_n),
                    bool_ty,
                );
            }
            root
        }};
    }
    macro_rules! build_variant_eq {
        ($arena:expr, $variants:expr) => {{
            let mut alternatives: Vec<(LiteralValue, NodeId)> = Vec::new();
            for (tag, payload_ty) in $variants {
                let tag_val = LiteralValue::new_native(ustr_to_isize(tag));
                let load_right_outer = n($arena, load_local(l_right_id), ty);
                let right_tag = n($arena, extract_tag(load_right_outer), int_type());
                let inner_body = if payload_ty == Type::unit() {
                    n($arena, native(true), bool_ty)
                } else {
                    let load_left_v = n($arena, load_local(l_left_id), ty);
                    let left_payload = variant_payload_project($arena, load_left_v, payload_ty);
                    let load_right_v = n($arena, load_local(l_right_id), ty);
                    let right_payload = variant_payload_project($arena, load_right_v, payload_ty);
                    value_method_call_node(
                        ctx,
                        ValueMethod {
                            trait_id,
                            input_ty: payload_ty,
                            method_index: VALUE_EQ_METHOD_INDEX,
                        },
                        span,
                        $arena,
                        &mut locals,
                        vec![left_payload, right_payload],
                    )?
                };
                let false_imm = n($arena, native(false), bool_ty);
                let inner_case = n(
                    $arena,
                    case(right_tag, vec![(tag_val.clone(), inner_body)], false_imm),
                    bool_ty,
                );
                alternatives.push((tag_val, inner_case));
            }
            let load_left_outer = n($arena, load_local(l_left_id), ty);
            let left_tag = n($arena, extract_tag(load_left_outer), int_type());
            let false_default = n($arena, native(false), bool_ty);
            n($arena, case(left_tag, alternatives, false_default), bool_ty)
        }};
    }

    let ty_data = ty.data();
    use TypeKind::*;
    let root = match &*ty_data {
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            Some(build_product_eq!(arena, member_tys))
        }
        Record(fields) => {
            let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
            drop(ty_data);
            Some(build_product_eq!(arena, member_tys))
        }
        Variant(variants) => {
            let variants = variants.clone();
            drop(ty_data);
            Some(build_variant_eq!(arena, variants))
        }
        Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let shape_ty = ctx
                .solver
                .type_def(named.def)
                .instantiated_shape(&named.params);
            let shape_data = shape_ty.data();
            match &*shape_data {
                Tuple(member_tys) => {
                    let member_tys = member_tys.clone();
                    drop(shape_data);
                    Some(build_product_eq!(arena, member_tys))
                }
                Record(fields) => {
                    let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
                    drop(shape_data);
                    Some(build_product_eq!(arena, member_tys))
                }
                Variant(variants) => {
                    let variants = variants.clone();
                    drop(shape_data);
                    Some(build_variant_eq!(arena, variants))
                }
                Never => {
                    drop(shape_data);
                    Some(n(arena, native(true), bool_ty))
                }
                _ => {
                    drop(shape_data);
                    let load_left = n(arena, load_local(l_left_id), shape_ty);
                    let load_right = n(arena, load_local(l_right_id), shape_ty);
                    Some(value_method_call_node(
                        ctx,
                        ValueMethod {
                            trait_id,
                            input_ty: shape_ty,
                            method_index: VALUE_EQ_METHOD_INDEX,
                        },
                        span,
                        arena,
                        &mut locals,
                        vec![load_left, load_right],
                    )?)
                }
            }
        }
        Function(_) => {
            drop(ty_data);
            Some(n(arena, native(false), bool_ty))
        }
        _ => {
            drop(ty_data);
            None
        }
    };

    Ok(root.map(|root| (root, locals)))
}

fn derive_value_hash_body(
    trait_id: TraitId,
    input_types: &[Type],
    span: Location,
    arena: &mut NodeArena,
    ctx: &mut ValueBodyCtx<'_, '_>,
) -> Result<Option<(NodeId, Vec<LocalDecl>)>, InternalCompilationError> {
    use hir::hir_syn::*;

    assert!(input_types.len() == 1);
    let ty = input_types[0];
    assert!(ctx.emit_generic_trait_calls || ty.is_constant());

    let n = alloc_synth_node;

    let unit_ty = Type::unit();
    let hasher_ty = hasher_type();
    let hasher_write_string = ctx.get_local_or_import_function(
        span,
        &module::Path::single_str("std"),
        crate::ustr("hasher_write_string"),
    )?;

    let mut locals = vec![
        local("self", ty),
        LocalDecl::new(
            (crate::ustr("state"), Location::new_synthesized()),
            MutType::mutable(),
            hasher_ty,
            None,
            Location::new_synthesized(),
        ),
    ];
    let l_self_id = LocalDeclId::from_index(0);
    let l_state_id = LocalDeclId::from_index(1);

    let build_write_string = |arena: &mut NodeArena,
                              solver: &mut TraitSolver<'_>,
                              locals: &mut Vec<LocalDecl>,
                              value: &str|
     -> Result<NodeId, InternalCompilationError> {
        let state = n(arena, load_local(l_state_id), hasher_ty);
        let value = n(arena, native_str(value), string_type());
        static_apply_generated_with_locals(
            arena,
            locals,
            solver,
            hasher_write_string,
            [(state, hasher_ty), (value, string_type())],
            unit_ty,
            span,
        )
    };
    macro_rules! build_hash_value {
        ($arena:expr, $value:expr, $value_ty:expr) => {{
            let state = n($arena, load_local(l_state_id), hasher_ty);
            value_method_call_node(
                ctx,
                ValueMethod {
                    trait_id,
                    input_ty: $value_ty,
                    method_index: VALUE_HASH_METHOD_INDEX,
                },
                span,
                $arena,
                &mut locals,
                vec![$value, state],
            )
        }};
    }

    macro_rules! build_product_hash {
        ($arena:expr, $member_tys:expr) => {{
            let load_self = n($arena, load_local(l_self_id), ty);
            let mut statements = Vec::with_capacity($member_tys.len() + 1);
            for (index, member_ty) in $member_tys.into_iter().enumerate() {
                let member = n(
                    $arena,
                    project(load_self, ProjectionIndex::from_index(index)),
                    member_ty,
                );
                statements.push(build_hash_value!($arena, member, member_ty)?);
            }
            statements.push(n($arena, native(()), unit_ty));
            n($arena, block(statements), unit_ty)
        }};
    }

    macro_rules! build_variant_hash {
        ($arena:expr, $variants:expr) => {{
            let self_value = n($arena, load_local(l_self_id), ty);
            let self_tag = n($arena, extract_tag(self_value), int_type());
            let mut alternatives = Vec::with_capacity($variants.len());

            for (tag, payload_ty) in $variants.into_iter() {
                let tag_val = LiteralValue::new_native(ustr_to_isize(tag));
                let mut statements = vec![build_write_string(
                    $arena,
                    ctx.solver,
                    &mut locals,
                    tag.as_str(),
                )?];
                if payload_ty != Type::unit() {
                    let self_value = n($arena, load_local(l_self_id), ty);
                    let payload = variant_payload_project($arena, self_value, payload_ty);
                    statements.push(build_hash_value!($arena, payload, payload_ty)?);
                }
                statements.push(n($arena, native(()), unit_ty));
                let branch = n($arena, block(statements), unit_ty);
                alternatives.push((tag_val, branch));
            }

            let default = n($arena, native(()), unit_ty);
            n($arena, case(self_tag, alternatives, default), unit_ty)
        }};
    }

    let ty_data = ty.data();
    use TypeKind::*;
    let root = match &*ty_data {
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            Some((build_product_hash!(arena, member_tys), locals))
        }
        Record(fields) => {
            let fields = fields.clone();
            drop(ty_data);
            let member_tys: Vec<Type> = fields.into_iter().map(|(_, ty)| ty).collect();
            Some((build_product_hash!(arena, member_tys), locals))
        }
        Variant(variants) => {
            let variants = variants.clone();
            drop(ty_data);
            Some((build_variant_hash!(arena, variants), locals))
        }
        Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let shape_ty = ctx
                .solver
                .type_def(named.def)
                .instantiated_shape(&named.params);
            let shape_data = shape_ty.data();
            match &*shape_data {
                Tuple(member_tys) => {
                    let member_tys = member_tys.clone();
                    drop(shape_data);
                    Some((build_product_hash!(arena, member_tys), locals))
                }
                Record(fields) => {
                    let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
                    drop(shape_data);
                    Some((build_product_hash!(arena, member_tys), locals))
                }
                Variant(variants) => {
                    let variants = variants.clone();
                    drop(shape_data);
                    Some((build_variant_hash!(arena, variants), locals))
                }
                Never => {
                    drop(shape_data);
                    Some((n(arena, native(()), unit_ty), locals))
                }
                _ => {
                    drop(shape_data);
                    let load_self = n(arena, load_local(l_self_id), shape_ty);
                    Some((build_hash_value!(arena, load_self, shape_ty)?, locals))
                }
            }
        }
        Function(_) => {
            drop(ty_data);
            let statements = vec![
                build_write_string(arena, ctx.solver, &mut locals, "<function>")?,
                n(arena, native(()), unit_ty),
            ];
            Some((n(arena, block(statements), unit_ty), locals))
        }
        _ => {
            drop(ty_data);
            None
        }
    };

    Ok(root)
}

fn derive_value_clone_body(
    trait_id: TraitId,
    input_types: &[Type],
    arena: &mut NodeArena,
    ctx: &mut ValueBodyCtx<'_, '_>,
) -> Result<Option<(NodeId, Vec<LocalDecl>)>, InternalCompilationError> {
    use hir::hir_syn::*;

    assert!(input_types.len() == 1);
    let ty = input_types[0];
    assert!(ctx.emit_generic_trait_calls || ty.is_constant());

    let n = alloc_synth_node;

    let source_id = LocalDeclId::from_index(0);
    let target_id = LocalDeclId::from_index(1);
    let uninit_ty = uninit_type(ty);
    let mut locals = vec![
        local("source", ty),
        LocalDecl::new(
            (crate::ustr("target"), Location::new_synthesized()),
            MutType::mutable(),
            uninit_ty,
            None,
            Location::new_synthesized(),
        ),
    ];
    let build_assign_whole = |arena: &mut NodeArena| {
        let target = n(arena, load_local(target_id), uninit_ty);
        let source = n(arena, load_local(source_id), ty);
        n(
            arena,
            hir::NodeKind::Assign(hir::Assignment {
                place: target,
                value: source,
                drop: None,
            }),
            Type::unit(),
        )
    };
    macro_rules! build_product_clone {
        ($arena:expr, $member_tys:expr) => {{
            let member_tys = $member_tys;
            let mut statements = Vec::with_capacity(member_tys.len() + 2);
            let target = n($arena, load_local(target_id), uninit_ty);
            let uninit_members = member_tys
                .iter()
                .map(|&member_ty| n($arena, hir::NodeKind::Uninit, member_ty))
                .collect::<Vec<_>>();
            let uninit_product = n($arena, tuple(uninit_members), ty);
            statements.push(n(
                $arena,
                hir::NodeKind::Assign(hir::Assignment {
                    place: target,
                    value: uninit_product,
                    drop: None,
                }),
                Type::unit(),
            ));
            for (index, &member_ty) in member_tys.iter().enumerate() {
                let source = n($arena, load_local(source_id), ty);
                let source_member = n(
                    $arena,
                    project(source, ProjectionIndex::from_index(index)),
                    member_ty,
                );
                let target = n($arena, load_local(target_id), ty);
                let target_member = n(
                    $arena,
                    project(target, ProjectionIndex::from_index(index)),
                    uninit_type(member_ty),
                );
                statements.push(value_method_call_node(
                    ctx,
                    ValueMethod {
                        trait_id,
                        input_ty: member_ty,
                        method_index: VALUE_CLONE_METHOD_INDEX,
                    },
                    Location::new_synthesized(),
                    $arena,
                    &mut locals,
                    vec![source_member, target_member],
                )?);
            }
            statements.push(n($arena, native(()), Type::unit()));
            n($arena, block(statements), Type::unit())
        }};
    }
    macro_rules! build_variant_clone {
        ($arena:expr, $variants:expr) => {{
            let source = n($arena, load_local(source_id), ty);
            let source_tag = n($arena, extract_tag(source), int_type());
            let mut alternatives = Vec::with_capacity($variants.len());
            for (tag, payload_ty) in $variants {
                let tag_val = LiteralValue::new_native(ustr_to_isize(tag));
                let target = n($arena, load_local(target_id), uninit_ty);
                let target_value = if payload_ty == Type::unit() {
                    let payload = n($arena, native(()), Type::unit());
                    n($arena, variant(tag, payload), ty)
                } else {
                    let uninit_payload = n($arena, hir::NodeKind::Uninit, payload_ty);
                    let payload = variant_payload_storage_node($arena, uninit_payload, payload_ty);
                    n($arena, variant(tag, payload), ty)
                };
                let init_target = n(
                    $arena,
                    hir::NodeKind::Assign(hir::Assignment {
                        place: target,
                        value: target_value,
                        drop: None,
                    }),
                    Type::unit(),
                );
                let branch = if payload_ty == Type::unit() {
                    init_target
                } else {
                    let mut statements = Vec::with_capacity(3);
                    statements.push(init_target);
                    let source = n($arena, load_local(source_id), ty);
                    let source_payload = variant_payload_project($arena, source, payload_ty);
                    let target = n($arena, load_local(target_id), ty);
                    let target_payload = variant_payload_project($arena, target, payload_ty);
                    let target_payload = {
                        let old = target_payload;
                        $arena[old].ty = uninit_type(payload_ty);
                        old
                    };
                    statements.push(value_method_call_node(
                        ctx,
                        ValueMethod {
                            trait_id,
                            input_ty: payload_ty,
                            method_index: VALUE_CLONE_METHOD_INDEX,
                        },
                        Location::new_synthesized(),
                        $arena,
                        &mut locals,
                        vec![source_payload, target_payload],
                    )?);
                    statements.push(n($arena, native(()), Type::unit()));
                    n($arena, block(statements), Type::unit())
                };
                alternatives.push((tag_val, branch));
            }
            let default = n($arena, native(()), Type::unit());
            n(
                $arena,
                case(source_tag, alternatives, default),
                Type::unit(),
            )
        }};
    }

    let ty_data = ty.data();
    use TypeKind::*;
    let root = match &*ty_data {
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            build_product_clone!(arena, member_tys)
        }
        Record(fields) => {
            let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
            drop(ty_data);
            build_product_clone!(arena, member_tys)
        }
        Variant(variants) => {
            let variants = variants.clone();
            drop(ty_data);
            build_variant_clone!(arena, variants)
        }
        Function(_) => {
            drop(ty_data);
            function_value_clone_root(ty, source_id, target_id, arena)
        }
        Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let shape_ty = ctx
                .solver
                .type_def(named.def)
                .instantiated_shape(&named.params);
            let shape_data = shape_ty.data();
            match &*shape_data {
                Tuple(member_tys) => {
                    let member_tys = member_tys.clone();
                    drop(shape_data);
                    build_product_clone!(arena, member_tys)
                }
                Record(fields) => {
                    let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
                    drop(shape_data);
                    build_product_clone!(arena, member_tys)
                }
                Variant(variants) => {
                    let variants = variants.clone();
                    drop(shape_data);
                    build_variant_clone!(arena, variants)
                }
                Never => {
                    drop(shape_data);
                    n(arena, native(()), Type::unit())
                }
                _ => {
                    drop(shape_data);
                    build_assign_whole(arena)
                }
            }
        }
        _ => {
            drop(ty_data);
            build_assign_whole(arena)
        }
    };

    Ok(Some((root, locals)))
}

fn derive_value_drop_body(
    trait_id: TraitId,
    input_types: &[Type],
    arena: &mut NodeArena,
    ctx: &mut ValueBodyCtx<'_, '_>,
) -> Result<(NodeId, Vec<LocalDecl>), InternalCompilationError> {
    use hir::hir_syn::*;

    assert!(input_types.len() == 1);
    let ty = input_types[0];
    assert!(ctx.emit_generic_trait_calls || ty.is_constant());

    let n = alloc_synth_node;
    let target_id = LocalDeclId::from_index(0);
    let mut locals = vec![LocalDecl::new(
        (crate::ustr("target"), Location::new_synthesized()),
        MutType::mutable(),
        ty,
        None,
        Location::new_synthesized(),
    )];
    let build_unit = |arena: &mut NodeArena| n(arena, native(()), Type::unit());
    macro_rules! build_product_drop {
        ($arena:expr, $member_tys:expr) => {{
            let mut statements = Vec::with_capacity($member_tys.len() + 1);
            for (index, member_ty) in $member_tys.into_iter().enumerate() {
                let target = n($arena, load_local(target_id), ty);
                let target_member = n(
                    $arena,
                    project(target, ProjectionIndex::from_index(index)),
                    member_ty,
                );
                statements.push(value_method_call_node(
                    ctx,
                    ValueMethod {
                        trait_id,
                        input_ty: member_ty,
                        method_index: VALUE_DROP_METHOD_INDEX,
                    },
                    Location::new_synthesized(),
                    $arena,
                    &mut locals,
                    vec![target_member],
                )?);
            }
            statements.push(n($arena, native(()), Type::unit()));
            n($arena, block(statements), Type::unit())
        }};
    }
    macro_rules! build_variant_drop {
        ($arena:expr, $variants:expr) => {{
            let target = n($arena, load_local(target_id), ty);
            let target_tag = n($arena, extract_tag(target), int_type());
            let mut alternatives = Vec::with_capacity($variants.len());
            for (tag, payload_ty) in $variants {
                let tag_val = LiteralValue::new_native(ustr_to_isize(tag));
                let branch = if payload_ty == Type::unit() {
                    n($arena, native(()), Type::unit())
                } else {
                    let target = n($arena, load_local(target_id), ty);
                    let target_payload = variant_payload_project($arena, target, payload_ty);
                    value_method_call_node(
                        ctx,
                        ValueMethod {
                            trait_id,
                            input_ty: payload_ty,
                            method_index: VALUE_DROP_METHOD_INDEX,
                        },
                        Location::new_synthesized(),
                        $arena,
                        &mut locals,
                        vec![target_payload],
                    )?
                };
                alternatives.push((tag_val, branch));
            }
            let default = n($arena, native(()), Type::unit());
            n(
                $arena,
                case(target_tag, alternatives, default),
                Type::unit(),
            )
        }};
    }

    let ty_data = ty.data();
    use TypeKind::*;
    let root = match &*ty_data {
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            build_product_drop!(arena, member_tys)
        }
        Record(fields) => {
            let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
            drop(ty_data);
            build_product_drop!(arena, member_tys)
        }
        Variant(variants) => {
            let variants = variants.clone();
            drop(ty_data);
            build_variant_drop!(arena, variants)
        }
        Function(_) => {
            drop(ty_data);
            function_value_drop_root(ty, target_id, arena)
        }
        Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let shape_ty = ctx
                .solver
                .type_def(named.def)
                .instantiated_shape(&named.params);
            let shape_data = shape_ty.data();
            match &*shape_data {
                Tuple(member_tys) => {
                    let member_tys = member_tys.clone();
                    drop(shape_data);
                    build_product_drop!(arena, member_tys)
                }
                Record(fields) => {
                    let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
                    drop(shape_data);
                    build_product_drop!(arena, member_tys)
                }
                Variant(variants) => {
                    let variants = variants.clone();
                    drop(shape_data);
                    build_variant_drop!(arena, variants)
                }
                Never => {
                    drop(shape_data);
                    build_unit(arena)
                }
                _ => {
                    drop(shape_data);
                    build_unit(arena)
                }
            }
        }
        _ => {
            drop(ty_data);
            build_unit(arena)
        }
    };
    Ok((root, locals))
}

fn derive_function_value_impl(
    trait_id: TraitId,
    input_types: &[Type],
    span: Location,
    solver: &mut TraitSolver<'_>,
) -> Result<TraitImplId, InternalCompilationError> {
    let associated_const_values: Vec<LiteralValue> =
        value_layout_associated_const_values(input_types[0], span, solver)?
            .into_iter()
            .map(LiteralValue::new_native)
            .collect();
    let (method_count, definitions) = {
        let trait_def = solver.trait_def(trait_id);
        (
            trait_def.methods.len(),
            trait_def.instantiate_for_tys(input_types, &[]),
        )
    };
    let methods = (0..method_count)
        .map(TraitMethodIndex::from_index)
        .map(|method_index| function_value_method(solver, method_index, span))
        .collect::<Result<Vec<_>, _>>()?;
    let tys = definitions
        .into_iter()
        .map(|definition| Type::function_type(definition.ty_scheme.ty))
        .collect::<Vec<_>>();
    let associated_const_tys = solver
        .trait_def(trait_id)
        .instantiate_associated_const_tys_for_tys(input_types, &[]);
    let dictionary_ty = TraitImpls::dictionary_ty(tys, associated_const_tys);
    let dictionary_value = module::build_dictionary_value(&methods, &associated_const_values);
    let imp = TraitImpl::new(
        Vec::new(),
        methods,
        dictionary_value,
        dictionary_ty,
        false,
        None,
    )
    .with_associated_const_values(associated_const_values);
    let key = ConcreteTraitImplKey::new(trait_id, input_types.to_vec());
    Ok(TraitImplId::Local(
        solver.impls.add_concrete_struct(key, imp),
    ))
}

fn derive_structural_value_impl(
    trait_id: TraitId,
    input_types: &[Type],
    span: Location,
    _arena: &mut NodeArena,
    solver: &mut TraitSolver,
) -> Result<Option<TraitImplId>, InternalCompilationError> {
    let ty_data = input_types[0].data();
    if let TypeKind::Named(named) = &*ty_data {
        let type_def = solver.type_def(named.def);
        if type_def
            .attributes
            .iter()
            .any(|attribute| attribute.path.0 == ustr(NO_DERIVE_VALUE_ATTRIBUTE))
        {
            return Ok(None);
        }
    }
    let can_derive = matches!(
        &*ty_data,
        TypeKind::Tuple(_)
            | TypeKind::Record(_)
            | TypeKind::Variant(_)
            | TypeKind::Function(_)
            | TypeKind::Named(_)
    );
    drop(ty_data);
    if !can_derive {
        return Ok(None);
    }

    if input_types[0].is_function() {
        return Ok(Some(derive_function_value_impl(
            trait_id,
            input_types,
            span,
            solver,
        )?));
    }

    let associated_const_values: Vec<LiteralValue> =
        value_layout_associated_const_values(input_types[0], span, solver)?
            .into_iter()
            .map(LiteralValue::new_native)
            .collect();
    let snapshot = solver.snapshot_derived_impl_state();
    let impl_id = solver.reserve_concrete_impl_from_code_entries(
        trait_id,
        input_types,
        &[],
        associated_const_values,
    );
    let mut ctx = ValueBodyCtx::concrete(solver);

    let mut eq_arena = NodeArena::default();
    let Some((eq_root, eq_locals)) =
        (match derive_value_eq_body(trait_id, input_types, span, &mut eq_arena, &mut ctx) {
            Ok(value) => value,
            Err(err) => {
                ctx.solver.rollback_derived_impl_state(snapshot);
                return Err(err);
            }
        })
    else {
        ctx.solver.rollback_derived_impl_state(snapshot);
        return Ok(None);
    };
    let eq = (PendingFunctionBody::new(eq_arena, eq_root), eq_locals);

    let mut to_string_arena = NodeArena::default();
    let Some((to_string_root, to_string_locals)) = (match derive_value_to_string_body(
        trait_id,
        input_types,
        span,
        &mut to_string_arena,
        &mut ctx,
    ) {
        Ok(value) => value,
        Err(err) => {
            ctx.solver.rollback_derived_impl_state(snapshot);
            return Err(err);
        }
    }) else {
        ctx.solver.rollback_derived_impl_state(snapshot);
        return Ok(None);
    };
    let to_string = (
        PendingFunctionBody::new(to_string_arena, to_string_root),
        to_string_locals,
    );

    let mut hash_arena = NodeArena::default();
    let Some((hash_root, hash_locals)) =
        (match derive_value_hash_body(trait_id, input_types, span, &mut hash_arena, &mut ctx) {
            Ok(value) => value,
            Err(err) => {
                ctx.solver.rollback_derived_impl_state(snapshot);
                return Err(err);
            }
        })
    else {
        ctx.solver.rollback_derived_impl_state(snapshot);
        return Ok(None);
    };
    let hash = (PendingFunctionBody::new(hash_arena, hash_root), hash_locals);

    let mut clone_arena = NodeArena::default();
    let Some((clone_root, clone_locals)) =
        derive_value_clone_body(trait_id, input_types, &mut clone_arena, &mut ctx)?
    else {
        ctx.solver.rollback_derived_impl_state(snapshot);
        return Ok(None);
    };
    let clone = (
        PendingFunctionBody::new(clone_arena, clone_root),
        clone_locals,
    );

    let mut drop_arena = NodeArena::default();
    let (drop_root, drop_locals) =
        derive_value_drop_body(trait_id, input_types, &mut drop_arena, &mut ctx)?;
    let drop = (PendingFunctionBody::new(drop_arena, drop_root), drop_locals);

    ctx.solver.replace_concrete_impl_code_entries(
        impl_id,
        trait_id,
        input_types,
        &[],
        [eq, to_string, hash, clone, drop],
    );
    Ok(Some(TraitImplId::Local(impl_id)))
}

pub(crate) fn derive_generic_value_code_entries(
    trait_id: TraitId,
    input_types: &[Type],
    span: Location,
    _arena: &mut NodeArena,
    solver: &mut TraitSolver,
) -> Result<Option<ValueCodeEntries>, InternalCompilationError> {
    let mut ctx = ValueBodyCtx::generic(solver);

    let mut eq_arena = NodeArena::default();
    let Some((eq_root, eq_locals)) =
        derive_value_eq_body(trait_id, input_types, span, &mut eq_arena, &mut ctx)?
    else {
        return Ok(None);
    };
    let eq = (PendingFunctionBody::new(eq_arena, eq_root), eq_locals);

    let mut to_string_arena = NodeArena::default();
    let Some((to_string_root, to_string_locals)) =
        derive_value_to_string_body(trait_id, input_types, span, &mut to_string_arena, &mut ctx)?
    else {
        return Ok(None);
    };
    let to_string = (
        PendingFunctionBody::new(to_string_arena, to_string_root),
        to_string_locals,
    );

    let mut hash_arena = NodeArena::default();
    let Some((hash_root, hash_locals)) =
        derive_value_hash_body(trait_id, input_types, span, &mut hash_arena, &mut ctx)?
    else {
        return Ok(None);
    };
    let hash = (PendingFunctionBody::new(hash_arena, hash_root), hash_locals);

    let mut clone_arena = NodeArena::default();
    let Some((clone_root, clone_locals)) =
        derive_value_clone_body(trait_id, input_types, &mut clone_arena, &mut ctx)?
    else {
        return Ok(None);
    };
    let clone = (
        PendingFunctionBody::new(clone_arena, clone_root),
        clone_locals,
    );

    let mut drop_arena = NodeArena::default();
    let (drop_root, drop_locals) =
        derive_value_drop_body(trait_id, input_types, &mut drop_arena, &mut ctx)?;
    let drop = (PendingFunctionBody::new(drop_arena, drop_root), drop_locals);

    Ok(Some(vec![eq, to_string, hash, clone, drop]))
}

/// A deriver for the `Value` trait that auto-derives the full impl for algebraic types.
#[derive(Debug, Clone)]
struct ValueDeriver;

impl Deriver for ValueDeriver {
    fn derive_impl(
        &self,
        trait_id: TraitId,
        input_types: &[Type],
        span: Location,
        arena: &mut NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

        derive_structural_value_impl(trait_id, input_types, span, arena, solver)
    }
}

pub fn value_trait() -> Trait {
    let var_ty = Type::variable_id(0);
    let binary_fn_ty = FnType::new_by_val([var_ty, var_ty], bool_type(), EffType::empty());
    let unary_to_string_ty = FnType::new_by_val([var_ty], string_type(), EffType::empty());
    let binary_hash_ty = FnType::new(
        vec![
            FnArgType::new_by_val(var_ty),
            FnArgType::new(hasher_type(), MutType::mutable()),
        ],
        Type::unit(),
        EffType::empty(),
    );
    let clone_ty = FnType::new(
        vec![
            FnArgType::new_by_val(var_ty),
            FnArgType::new(uninit_type(var_ty), MutType::mutable()),
        ],
        Type::unit(),
        EffType::empty(),
    );
    let drop_ty = FnType::new(
        vec![FnArgType::new(var_ty, MutType::mutable())],
        Type::unit(),
        EffType::empty(),
    );
    Trait::new_with_self_input_type(
        "Value",
        "A type that supports semantic equality, string conversion, hashing, and layout metadata.",
        [],
        [
            (
                "eq",
                Def::new_infer_quantifiers(
                    binary_fn_ty,
                    ["left", "right"],
                    "Returns whether `left` equals `right`.",
                ),
            ),
            (
                "to_string",
                Def::new_infer_quantifiers(
                    unary_to_string_ty,
                    ["value"],
                    "Returns the string representation of `value`.",
                ),
            ),
            (
                "hash",
                Def::new_infer_quantifiers(
                    binary_hash_ty,
                    ["value", "state"],
                    "Writes the hash of `value` into `state`.",
                ),
            ),
            (
                "clone",
                Def::new_infer_quantifiers(
                    clone_ty,
                    ["source", "target"],
                    "Compiler-owned method that clones `source` into already allocated `target` storage.",
                ),
            ),
            (
                "drop",
                Def::new_infer_quantifiers(
                    drop_ty,
                    ["target"],
                    "Compiler-owned method that drops `target` in place.",
                ),
            ),
        ],
    )
    .with_associated_consts([
        TraitAssociatedConst::new("SIZE", Type::primitive::<isize>(), "Size in bytes."),
        TraitAssociatedConst::new("ALIGN", Type::primitive::<isize>(), "Alignment in bytes."),
    ])
    .with_deriver(ValueDeriver)
}

pub fn inspect_trait() -> Trait {
    let var_ty = Type::variable_id(0);
    let inspect_ty = FnType::new_by_val(
        [var_ty],
        string_type(),
        EffType::single_primitive(PrimitiveEffect::Fallible),
    );
    Trait::new_with_self_input_type(
        INSPECT_TRAIT_NAME,
        "A type that can render values for interactive inspection and debugging.",
        [],
        [(
            "inspect",
            FunctionDefinition::new_infer_quantifiers(
                inspect_ty,
                ["value"],
                "Returns an inspection representation of `value`.",
            ),
        )],
    )
    .with_deriver(InspectDeriver)
}

fn trusted_uninit_function(
    debug_name: &'static str,
    ty: FnType,
    arg_names: impl IntoIterator<Item = &'static str>,
    doc: &'static str,
    passing: &'static [ResolvedArgPassing],
    code: fn(ValOrMutArgs, &mut EvalCtx) -> EvalControlFlowResult,
) -> ModuleFunction {
    ModuleFunction::new(
        FunctionDefinition::new(
            TypeScheme::new_infer_quantifiers(ty),
            arg_names.into_iter().map(ustr::Ustr::from).collect(),
            Some(String::from(doc)),
        ),
        Box::new(ContextNativeFn::new(debug_name, &[], passing, code)),
        None,
        Vec::new(),
    )
}

fn uninit_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    trusted_uninit_function(
        "uninit",
        FnType::new(Vec::new(), uninit_type(gen0), EffType::empty()),
        [],
        "Creates trusted uninitialized storage.",
        &[],
        uninit_native,
    )
}

fn write_init_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    trusted_uninit_function(
        "write_init",
        FnType::new(
            vec![
                FnArgType::new(uninit_type(gen0), MutType::mutable()),
                FnArgType::new_by_val(gen0),
            ],
            Type::unit(),
            EffType::empty(),
        ),
        ["target", "value"],
        "Moves a value into trusted uninitialized storage.",
        &[MUTABLE_REF, SHARED_REF],
        write_init_native,
    )
}

fn assume_init_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    trusted_uninit_function(
        "assume_init",
        FnType::new_by_val([uninit_type(gen0)], gen0, EffType::empty()),
        ["value"],
        "Moves an initialized value out of trusted storage.",
        &[SHARED_REF],
        assume_init_native,
    )
}

fn assume_init_mut_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    trusted_uninit_function(
        "assume_init_mut",
        FnType::new_with_return_convention(
            vec![FnArgType::new(uninit_type(gen0), MutType::mutable())],
            gen0,
            EffType::empty(),
            FnReturnConvention::Place,
        ),
        ["target"],
        "Reinterprets trusted storage as initialized mutable storage.",
        &[MUTABLE_REF],
        assume_init_mut_native,
    )
}

pub fn add_to_module(to: &mut Module) {
    to.add_bare_native_type_alias_str(UNINIT_TYPE_NAME, bare_native_type::<UninitStorage>());
    let value_trait_id = to.add_trait(value_trait());
    let value_trait_id = TraitId::new(to.module_id(), value_trait_id);
    debug_assert_eq!(to.trait_def(value_trait_id).name, VALUE_TRAIT_NAME);
    let inspect_trait_id = to.add_trait(inspect_trait());
    let inspect_trait_id = TraitId::new(to.module_id(), inspect_trait_id);
    debug_assert_eq!(to.trait_def(inspect_trait_id).name, INSPECT_TRAIT_NAME);
    to.add_private_unsafe_function(ustr("uninit"), uninit_descr());
    to.add_private_unsafe_function(ustr("write_init"), write_init_descr());
    to.add_private_unsafe_function(ustr("assume_init"), assume_init_descr());
    to.add_private_unsafe_function(ustr("assume_init_mut"), assume_init_mut_descr());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ModuleEnv,
        parser::location::SourceTable,
        std::{array::array_type, math::float_type, math::int_type},
    };

    fn assert_uninit_layout_matches_inner_type(ty: Type, env: &ModuleEnv<'_>) {
        let span = Location::new_synthesized();
        assert_eq!(
            value_layout_for_type(uninit_type(ty), span, env).unwrap(),
            value_layout_for_type(ty, span, env).unwrap()
        );
    }

    #[test]
    fn uninit_layout_matches_initialized_storage_layout() {
        let mut source_table = SourceTable::default();
        let std_module = crate::std::std_module(&mut source_table);
        let modules = crate::Modules::default();
        let env = ModuleEnv::new(&std_module, &modules);

        let int = int_type();
        assert_uninit_layout_matches_inner_type(int, &env);
        assert_uninit_layout_matches_inner_type(Type::tuple([int, float_type()]), &env);
        assert_uninit_layout_matches_inner_type(array_type(int), &env);
    }
}
