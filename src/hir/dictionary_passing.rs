// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::mem;

use crate::FxHashMap;

use crate::{
    Location,
    ast::Path,
    compiler::error::InternalCompilationError,
    format::FormatWith,
    module::{
        FunctionId, LocalClone, LocalDecl, LocalDeclId, LocalDrop, LocalFunctionId, ModuleEnv,
        id::Id,
    },
    parser::helpers::EMPTY_USTR,
    types::r#trait::TraitRef,
    types::trait_solver::TraitSolver,
    types::r#type::TypeVar,
    types::type_like::TypeLike,
    types::type_scheme::format_have_trait,
};
use derive_new::new;
use itertools::process_results;
use ustr::Ustr;

use crate::{
    containers::b,
    hir::emit_value_impl::{function_value_method, generic_value_methods_for_type},
    hir::value::Value,
    hir::{self, Node, NodeArena, NodeId, NodeKind},
    std::{
        math::int_type,
        value::{
            VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX, VALUE_TRAIT,
            function_value_method_name, is_function_surface_only_value_trait_application,
            is_function_surface_only_value_type, is_value_trait_for_function_type,
            value_layout_associated_const_values,
        },
    },
    types::effects::no_effects,
    types::mutability::MutType,
    types::r#type::{FnArgType, Type, TypeKind},
    types::type_inference::substitution::InstSubstitution,
};

/// A dictionary requirement, that will be passed as extra parameter to a function.
#[derive(Clone, Debug)]
pub enum DictionaryReq {
    FieldIndex {
        ty: Type,
        field: Ustr,
    },
    TraitImpl {
        trait_ref: TraitRef,
        input_tys: Vec<Type>,
        output_tys: Vec<Type>, // stored here for type generation, but not used in comparisons
                               // FIXME: maybe we need a span here for proper error reporting
    },
}

impl DictionaryReq {
    pub fn new_field_index(ty: Type, field: Ustr) -> Self {
        Self::FieldIndex { ty, field }
    }

    pub fn new_trait_impl(
        trait_ref: TraitRef,
        input_tys: Vec<Type>,
        output_tys: Vec<Type>,
    ) -> Self {
        Self::TraitImpl {
            trait_ref,
            input_tys,
            output_tys,
        }
    }

    pub fn instantiate(&self, subst: &InstSubstitution) -> DictionaryReq {
        use DictionaryReq::*;
        match self {
            FieldIndex { ty, field } => FieldIndex {
                ty: ty.instantiate(subst),
                field: *field,
            },
            TraitImpl {
                trait_ref,
                input_tys,
                output_tys,
            } => TraitImpl {
                trait_ref: trait_ref.clone(),
                input_tys: input_tys.iter().map(|ty| ty.instantiate(subst)).collect(),
                output_tys: output_tys.iter().map(|ty| ty.instantiate(subst)).collect(),
            },
        }
    }

    pub fn to_dict_name(&self, i: usize) -> String {
        use DictionaryReq::*;
        match self {
            FieldIndex { field, .. } => format!("_d{i}_{field}"),
            TraitImpl { trait_ref, .. } => {
                format!("_d{i}_impl_{}", trait_ref.name)
            }
        }
    }

    pub fn to_dict_type(&self) -> Type {
        match self {
            DictionaryReq::FieldIndex { .. } => int_type(),
            DictionaryReq::TraitImpl {
                trait_ref,
                input_tys,
                output_tys,
            } => trait_ref.get_dictionary_type_for_tys(input_tys, output_tys),
        }
    }
}

impl PartialEq for DictionaryReq {
    fn eq(&self, other: &Self) -> bool {
        use DictionaryReq::*;
        match (self, other) {
            (
                FieldIndex {
                    ty: ty1,
                    field: field1,
                },
                FieldIndex {
                    ty: ty2,
                    field: field2,
                },
            ) => ty1 == ty2 && field1 == field2,
            (
                TraitImpl {
                    trait_ref: tr1,
                    input_tys: in1,
                    ..
                },
                TraitImpl {
                    trait_ref: tr2,
                    input_tys: in2,
                    ..
                },
            ) => tr1 == tr2 && in1 == in2,
            _ => false,
        }
    }
}

impl Eq for DictionaryReq {}

impl FormatWith<ModuleEnv<'_>> for DictionaryReq {
    fn fmt_with(
        &self,
        f: &mut std::fmt::Formatter,
        env: &crate::module::ModuleEnv<'_>,
    ) -> std::fmt::Result {
        use DictionaryReq::*;
        match self {
            FieldIndex { ty, field } => write!(f, "{} field {}", ty.format_with(env), field),
            TraitImpl {
                trait_ref,
                input_tys,
                output_tys,
            } => format_have_trait(trait_ref, input_tys, output_tys, f, env),
        }
    }
}

pub type DictionariesReq = Vec<DictionaryReq>;

/// Data structure to hold extra parameters for a function.
#[derive(Clone, Debug)]
pub struct ExtraParameters {
    /// The dictionary requirements for the function.
    /// This is a list of dictionaries that will be passed as extra parameters to the function.
    pub requirements: Vec<DictionaryReq>,
    /// A map from type variables to other type variables containing their representation type.
    /// This is used to resolve type variables when looking up field dict indices.
    pub repr_map: FxHashMap<TypeVar, TypeVar>,
}

impl ExtraParameters {
    pub fn is_empty(&self) -> bool {
        self.requirements.is_empty()
    }
    pub fn len(&self) -> usize {
        self.requirements.len()
    }
}

pub fn find_field_dict_index(dicts: &ExtraParameters, var: TypeVar, field: &str) -> Option<usize> {
    // Resolve the variable to its representation type if it is a different type variable.
    let var = dicts.repr_map.get(&var).unwrap_or(&var);
    let ty = Type::variable(*var);
    // Find the index of the dictionary that matches the type and field.
    dicts.requirements.iter().position(|dict| {
        if let DictionaryReq::FieldIndex {
            ty: ty2,
            field: field2,
        } = &dict
        {
            *ty2 == ty && field2 == &field
        } else {
            false
        }
    })
}

pub fn find_trait_impl_dict_index(
    dicts: &ExtraParameters,
    trait_ref: &TraitRef,
    input_tys: &[Type],
) -> Option<usize> {
    dicts.requirements.iter().position(|dict| {
        if let DictionaryReq::TraitImpl {
            trait_ref: trait_ref2,
            input_tys: tys2,
            ..
        } = dict
        {
            input_tys == tys2 && trait_ref == trait_ref2
        } else {
            false
        }
    })
}

/// Build the use-site HIR expression for a generated `Value` dictionary.
fn value_dictionary_node_kind_from_methods(
    arena: &mut NodeArena,
    trait_ref: &TraitRef,
    input_tys: &[Type],
    span: Location,
    methods: &[LocalFunctionId],
    mut method_name: impl FnMut(usize) -> Ustr,
) -> Result<(NodeKind, Type), InternalCompilationError> {
    // This builds compiler-generated `Value` dictionaries. The associated
    // consts are layout metadata, so they are computed from the concrete HIR
    // type rather than read from a source impl.
    assert_eq!(methods.len(), trait_ref.functions.len());
    let definitions = trait_ref.instantiate_for_tys(input_tys, &[]);
    let mut entries =
        Vec::with_capacity(trait_ref.functions.len() + trait_ref.associated_const_count());
    for (method_index, definition) in definitions.into_iter().enumerate() {
        let method_ty = Type::function_type(definition.ty_scheme.ty);
        entries.push(arena.alloc(Node::new(
            NodeKind::GetFunction(b(hir::GetFunction {
                function: FunctionId::Local(methods[method_index]),
                function_path: Path::single(method_name(method_index), span),
                function_span: span,
                inst_data: hir::FnInstData::none(),
            })),
            method_ty,
            no_effects(),
            span,
        )));
    }
    let associated_const_values = value_layout_associated_const_values(input_tys[0], span)?;
    for value in associated_const_values {
        entries.push(arena.alloc(Node::new(
            hir::hir_syn::native(value),
            int_type(),
            no_effects(),
            span,
        )));
    }
    let ty = trait_ref.get_dictionary_type_for_tys(input_tys, &[]);
    Ok((hir::hir_syn::tuple(entries), ty))
}

/// Build the compiler-provided `Value` dictionary for a concrete function type.
fn function_value_dictionary_node_kind(
    arena: &mut NodeArena,
    trait_ref: &TraitRef,
    input_tys: &[Type],
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<(NodeKind, Type), InternalCompilationError> {
    let methods = (0..trait_ref.functions.len())
        .map(|method_index| function_value_method(ctx.trait_solver, method_index, span, arena))
        .collect::<Result<Vec<_>, _>>()?;
    value_dictionary_node_kind_from_methods(
        arena,
        trait_ref,
        input_tys,
        span,
        &methods,
        function_value_method_name,
    )
}

/// Build a generated `Value` dictionary for a structural type whose unresolved
/// type variables appear only inside function types.
fn generic_derived_value_dictionary_node_kind(
    arena: &mut NodeArena,
    trait_ref: &TraitRef,
    input_tys: &[Type],
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<(NodeKind, Type), InternalCompilationError> {
    let methods =
        generic_value_methods_for_type(ctx.trait_solver, trait_ref, input_tys, span, arena)?;
    value_dictionary_node_kind_from_methods(
        arena,
        trait_ref,
        input_tys,
        span,
        &methods,
        |method_index| trait_ref.functions[method_index].0,
    )
}

/// Build the HIR expression that provides the runtime dictionary for a trait requirement.
fn trait_dictionary_node_kind(
    arena: &mut NodeArena,
    trait_ref: &TraitRef,
    input_tys: &[Type],
    output_tys: &[Type],
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    local_count: usize,
) -> Result<(NodeKind, Type), InternalCompilationError> {
    if is_value_trait_for_function_type(trait_ref, input_tys, output_tys) {
        return function_value_dictionary_node_kind(arena, trait_ref, input_tys, span, ctx);
    }
    if is_function_surface_only_value_trait_application(trait_ref, input_tys, output_tys) {
        return generic_derived_value_dictionary_node_kind(arena, trait_ref, input_tys, span, ctx);
    }

    let node_kind = if input_tys.iter().all(Type::is_constant) {
        let dictionary = ctx
            .trait_solver
            .solve_impl(trait_ref, input_tys, span, arena)?;
        NodeKind::GetDictionary(hir::GetDictionary { dictionary })
    } else {
        let index = find_trait_impl_dict_index(ctx.dicts, trait_ref, input_tys)
            .expect("Dictionary for trait impl not found, type inference should have failed");
        let id = LocalDeclId::from_index(local_count + index);
        hir::hir_syn::load(index, id)
    };
    let ty = trait_ref.get_dictionary_type_for_tys(input_tys, output_tys);
    Ok((node_kind, ty))
}

/// Return the method slot and callable type from an already-instantiated dictionary type.
/// Currently the returned untry_index is the same as function_index.
fn dictionary_method_projection_data(
    trait_ref: &TraitRef,
    dictionary_ty: Type,
    function_index: usize,
) -> (usize, Type) {
    let entry_index = trait_ref.dictionary_method_index(function_index);
    let function_ty = dictionary_ty
        .data()
        .as_tuple()
        .expect("Trait impl dict should be a tuple type")[entry_index];
    (entry_index, function_ty)
}

/// Allocate a projection node that extracts a trait method function from a dictionary value.
fn alloc_dictionary_method_projection(
    arena: &mut NodeArena,
    dictionary_id: NodeId,
    dictionary_ty: Type,
    trait_ref: &TraitRef,
    function_index: usize,
    span: Location,
) -> NodeId {
    let (entry_index, function_ty) =
        dictionary_method_projection_data(trait_ref, dictionary_ty, function_index);
    arena.alloc(Node::new(
        NodeKind::Project(dictionary_id, entry_index),
        function_ty,
        no_effects(),
        span,
    ))
}

pub fn instantiate_dictionaries_req(
    dicts: &DictionariesReq,
    subst: &InstSubstitution,
) -> DictionariesReq {
    dicts.iter().map(|dict| dict.instantiate(subst)).collect()
}

fn extra_args_from_inst_data<'d, 'sr, 'sm>(
    arena: &mut NodeArena,
    inst_data: &hir::FnInstData,
    span: Location,
    ctx: &mut DictElaborationCtx<'d, 'sr, 'sm>,
    local_count: usize,
) -> Result<(Vec<NodeId>, Vec<FnArgType>), InternalCompilationError> {
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
                            K::Immediate(hir::Immediate::new(Value::native(index as isize)))
                        }
                        Variable(var) => {
                            // Variable, it must be in the input dictionaries, look for it.
                            let var = *var;
                            drop(ty_data);
                            let index = find_field_dict_index(ctx.dicts, var, name).unwrap_or_else(
                                || panic!("Dictionary for field \"{name}\" in type variable \"{var}\" not found, type inference should have failed"),
                            );
                            let id = LocalDeclId::from_index(local_count + index);
                            K::EnvLoad(hir::EnvLoad { index: index as u32, id })
                        }
                        _ => {
                            panic!("FieldIndex dictionary should have a variable or record type");
                        }
                    };
                    (node_kind, int_type())
                }
                TraitImpl { trait_ref, input_tys, output_tys, .. } => {
                    let (node_kind, ty) = trait_dictionary_node_kind(
                        arena,
                        trait_ref,
                        input_tys,
                        output_tys,
                        span,
                        ctx,
                        local_count,
                    )?;
                    (node_kind, ty)
                }
            };
            Ok((
                arena.alloc(Node::new(node_kind, node_ty, no_effects(), span)),
                FnArgType::new(node_ty, MutType::constant()),
            ))
        }), |iter| iter.unzip()
    )
}

fn extra_args_for_module_function(
    arena: &mut NodeArena,
    inst_data: &DictionariesReq,
    span: Location,
    dicts: &ExtraParameters,
    local_count: usize,
) -> (Vec<NodeId>, Vec<FnArgType>) {
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
            let ty = dict.to_dict_type();
            let id = LocalDeclId::from_index(local_count + index);
            (
                arena.alloc(Node::new(
                    NodeKind::EnvLoad(hir::EnvLoad {
                        index: index as u32,
                        id,
                    }),
                    ty,
                    no_effects(),
                    span,
                )),
                FnArgType::new(ty, MutType::constant()),
            )
        })
        .unzip()
}

/// The dictionaries for the current module.
/// This is a map from function pointers to the dictionaries required by the function.
/// This is necessary as recursive functions in the current modules could not get their
/// dictionary requirements during type inference as they were not known yet.
pub type ModuleInstData = FxHashMap<LocalFunctionId, ExtraParameters>;

/// The context for elaborating dictionaries.
/// All necessary information to perform dictionary elaboration.
// #[derive(Clone, Copy)]
#[derive(new)]
pub struct DictElaborationCtx<'d, 'sr, 'sm> {
    /// The dictionaries for the current expression being elaborated.
    pub dicts: &'d ExtraParameters,
    /// The dictionaries for the current module, if compiling a module.
    /// None if compiling an expression.
    pub module_inst_data: Option<&'d ModuleInstData>,
    /// The trait solver. The borrow lifetime is independent from `dicts`.
    pub trait_solver: &'sr mut TraitSolver<'sm>,
}

pub fn elaborate_dictionaries<'d, 'sr, 'sm>(
    arena: &mut NodeArena,
    node_id: NodeId,
    ctx: &mut DictElaborationCtx<'d, 'sr, 'sm>,
    local_count: usize,
) -> Result<(), InternalCompilationError> {
    Node::elaborate_dictionaries(arena, node_id, ctx, local_count)
}

/// Resolve local clone/drop placeholders into static calls or hidden dictionary slots.
pub fn elaborate_local_value_dispatches<'d, 'sr, 'sm>(
    arena: &mut NodeArena,
    locals: &mut [LocalDecl],
    ctx: &mut DictElaborationCtx<'d, 'sr, 'sm>,
) -> Result<(), InternalCompilationError> {
    for local in locals {
        if matches!(local.clone, Some(LocalClone::Required)) {
            local.clone = Some(
                resolve_local_value_dispatch(
                    arena,
                    ctx,
                    local.ty,
                    VALUE_CLONE_METHOD_INDEX,
                    local.scope,
                    "Value dictionary for mutable let binding not found, type inference should have failed",
                )?
                .into_clone(),
            );
        }

        if matches!(local.drop, Some(LocalDrop::Required)) {
            local.drop = Some(
                resolve_local_value_dispatch(
                    arena,
                    ctx,
                    local.ty,
                    VALUE_DROP_METHOD_INDEX,
                    local.scope,
                    "Value dictionary for local drop not found, type inference should have failed",
                )?
                .into_drop(),
            );
        }
    }
    Ok(())
}

/// Shared resolved form for local `Value` clone/drop dispatch.
enum LocalValueDispatch {
    Static(FunctionId),
    Dictionary(usize),
}

impl LocalValueDispatch {
    fn into_clone(self) -> LocalClone {
        match self {
            Self::Static(function) => LocalClone::Static(function),
            Self::Dictionary(index) => LocalClone::Dictionary(index),
        }
    }

    fn into_drop(self) -> LocalDrop {
        match self {
            Self::Static(function) => LocalDrop::Static(function),
            Self::Dictionary(index) => LocalDrop::Dictionary(index),
        }
    }
}

/// Resolve a required local clone/drop into either a static `Value` method or a runtime dictionary slot.
fn resolve_local_value_dispatch(
    arena: &mut NodeArena,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    ty: Type,
    method_index: usize,
    span: Location,
    missing_dictionary_msg: &str,
) -> Result<LocalValueDispatch, InternalCompilationError> {
    if ty.is_function() {
        return Ok(LocalValueDispatch::Static(FunctionId::Local(
            function_value_method(ctx.trait_solver, method_index, span, arena)?,
        )));
    }
    if is_function_surface_only_value_type(ty) {
        let methods =
            generic_value_methods_for_type(ctx.trait_solver, &VALUE_TRAIT, &[ty], span, arena)?;
        return Ok(LocalValueDispatch::Static(FunctionId::Local(
            methods[method_index],
        )));
    }
    if ty.is_constant() {
        return Ok(LocalValueDispatch::Static(
            ctx.trait_solver
                .solve_impl_method(&VALUE_TRAIT, &[ty], method_index, span, arena)?,
        ));
    }
    let dict_index =
        find_trait_impl_dict_index(ctx.dicts, &VALUE_TRAIT, &[ty]).expect(missing_dictionary_msg);
    Ok(LocalValueDispatch::Dictionary(dict_index))
}

impl Node {
    pub fn elaborate_dictionaries<'d, 'sr, 'sm>(
        arena: &mut NodeArena,
        node_id: NodeId,
        ctx: &mut DictElaborationCtx<'d, 'sr, 'sm>,
        local_count: usize,
    ) -> Result<(), InternalCompilationError> {
        use NodeKind::*;

        let node_span = arena[node_id].span;
        let node_ty = arena[node_id].ty;
        // Note: node_effects is cloned lazily only in the two branches that need it
        // (Immediate and GetFunction), to avoid an unconditional Vec clone on every node.
        // Put a placeholder in the arena while we are mutating ourself and adding new nodes.
        let mut kind = mem::replace(&mut arena[node_id].kind, NodeKind::Unimplemented);

        match &mut kind {
            Immediate(immediate) => {
                if immediate.value.is_function() {
                    // Build closure to capture the dictionaries of this function, if any.
                    if !ctx.dicts.is_empty() {
                        let captures = ctx
                            .dicts
                            .requirements
                            .iter()
                            .enumerate()
                            .map(|(index, req)| {
                                let ty = req.to_dict_type();
                                let id = LocalDeclId::from_index(local_count + index);
                                arena.alloc(Node::new(
                                    EnvLoad(hir::EnvLoad {
                                        index: index as u32,
                                        id,
                                    }),
                                    ty,
                                    no_effects(),
                                    node_span,
                                ))
                            })
                            .collect();
                        let node_effects = arena[node_id].effects.clone();
                        let original_kind = mem::replace(&mut kind, NodeKind::Unimplemented);
                        let function_id =
                            arena.alloc(Node::new(original_kind, node_ty, node_effects, node_span));
                        kind = BuildClosure(b(hir::BuildClosure {
                            function: function_id,
                            dictionary_captures: captures,
                            captures: Vec::new(),
                            captures_value_dictionary: None,
                        }));
                    }
                }
            }
            BuildClosure(build_closure) => {
                // Elaborate hidden dictionary captures first (they are metadata).
                for &capture_id in &build_closure.dictionary_captures {
                    elaborate_dictionaries(arena, capture_id, ctx, local_count)?;
                }

                // Elaborate captures first (they are in outer scope).
                for &capture_id in &build_closure.captures {
                    elaborate_dictionaries(arena, capture_id, ctx, local_count)?;
                }
                if let Some(dict_id) = build_closure.captures_value_dictionary {
                    elaborate_dictionaries(arena, dict_id, ctx, local_count)?;
                }

                // Elaborate the function (it is the closure body/value).
                let function_id = build_closure.function;
                elaborate_dictionaries(arena, function_id, ctx, local_count)?;

                // Optimization: flatten nested BuildClosure
                // Check if the function is a BuildClosure itself (due to dictionary capturing).
                let is_nested = matches!(arena[function_id].kind, NodeKind::BuildClosure(_));

                if is_nested {
                    // Extract the inner BuildClosure.
                    let inner_kind =
                        mem::replace(&mut arena[function_id].kind, NodeKind::Unimplemented);
                    let inner_build = inner_kind
                        .into_build_closure()
                        .expect("is_nested check failed");
                    // inner_build.captures are the dictionary captures (should be first)
                    // build_closure.captures are the variable captures (should be second)
                    let mut new_dictionary_captures = inner_build.dictionary_captures;
                    new_dictionary_captures.append(&mut build_closure.dictionary_captures);
                    build_closure.dictionary_captures = new_dictionary_captures;
                    if !inner_build.captures.is_empty() && !build_closure.captures.is_empty() {
                        panic!("Cannot flatten closures with two owned capture environments yet");
                    }
                    if build_closure.captures.is_empty() {
                        build_closure.captures = inner_build.captures;
                        build_closure.captures_value_dictionary =
                            inner_build.captures_value_dictionary;
                    }
                    build_closure.function = inner_build.function;
                }
            }
            Apply(app) => {
                elaborate_dictionaries(arena, app.function, ctx, local_count)?;
                for &arg_id in &app.arguments {
                    elaborate_dictionaries(arena, arg_id, ctx, local_count)?;
                }
            }
            FunctionClone(node) => {
                elaborate_dictionaries(arena, node.source, ctx, local_count)?;
                elaborate_dictionaries(arena, node.target, ctx, local_count)?;
            }
            FunctionDrop(node) => {
                elaborate_dictionaries(arena, node.target, ctx, local_count)?;
            }
            StaticApply(app) => {
                for &arg_id in &app.arguments {
                    elaborate_dictionaries(arena, arg_id, ctx, local_count)?;
                }
                if !app.inst_data.dicts_req.is_empty() {
                    // Build the dictionary requirements for the function by adding extra arguments before normal arguments.
                    let span = app.function_span;
                    let (extra_args, extra_args_ty) =
                        extra_args_from_inst_data(arena, &app.inst_data, span, ctx, local_count)?;
                    // First add the extra parameters, then the original arguments.
                    app.argument_names
                        .splice(0..0, extra_args.iter().map(|_| *EMPTY_USTR));
                    app.arguments.splice(0..0, extra_args);
                    // Adapt real function type as well
                    app.ty.args.splice(0..0, extra_args_ty);
                } else {
                    // Is the called function part of the current module being compiled?
                    if let FunctionId::Local(id) = app.function {
                        if let Some(inst_data) = ctx
                            .module_inst_data
                            .and_then(|inst_data| inst_data.get(&id))
                        {
                            let inst_data = &inst_data.requirements;
                            // Yes, build the dictionary requirements for the function.
                            let (extra_args, extra_args_ty) = extra_args_for_module_function(
                                arena,
                                inst_data,
                                node_span,
                                ctx.dicts,
                                local_count,
                            );
                            app.argument_names
                                .splice(0..0, extra_args.iter().map(|_| *EMPTY_USTR));
                            app.arguments.splice(0..0, extra_args);
                            app.ty.args.splice(0..0, extra_args_ty);
                        }
                    }
                }
            }
            TraitFnApply(app) => {
                for &arg_id in &app.arguments {
                    elaborate_dictionaries(arena, arg_id, ctx, local_count)?;
                }
                assert!(
                    app.inst_data.dicts_req.is_empty(),
                    "Instantiation data for trait function is not supported yet."
                );
                let resolved = app.input_tys.iter().all(Type::is_constant);
                if is_value_trait_for_function_type(&app.trait_ref, &app.input_tys, &[]) {
                    let function = FunctionId::Local(function_value_method(
                        ctx.trait_solver,
                        app.function_index,
                        app.function_span,
                        arena,
                    )?);
                    let definition = &app.trait_ref.functions[app.function_index].1;
                    let argument_names = app.arguments_unnamed.filter_args(&definition.arg_names);
                    let function_path = Some(app.function_path.clone());
                    let function_span = app.function_span;
                    let ty = app.ty.clone();
                    let arguments = mem::take(&mut app.arguments);
                    kind = StaticApply(b(hir::StaticApplication {
                        function,
                        function_path,
                        function_span,
                        arguments,
                        argument_names,
                        ty,
                        inst_data: hir::FnInstData::none(),
                    }));
                } else if resolved {
                    // Fully resolved, look up the trait implementation and replace the function directly.
                    let function = ctx.trait_solver.solve_impl_method(
                        &app.trait_ref,
                        &app.input_tys,
                        app.function_index,
                        app.function_span,
                        arena,
                    )?;
                    let definition = &app.trait_ref.functions[app.function_index].1;
                    let argument_names = app.arguments_unnamed.filter_args(&definition.arg_names);
                    let function_path = Some(app.function_path.clone());
                    let function_span = app.function_span;
                    let ty = app.ty.clone();
                    let arguments = mem::take(&mut app.arguments);
                    kind = StaticApply(b(hir::StaticApplication {
                        function,
                        function_path,
                        function_span,
                        arguments,
                        argument_names,
                        ty,
                        inst_data: hir::FnInstData::none(),
                    }));
                } else if is_function_surface_only_value_trait_application(
                    &app.trait_ref,
                    &app.input_tys,
                    &[],
                ) {
                    let function_span = app.function_span;
                    let dict_ty = app
                        .trait_ref
                        .get_dictionary_type_for_tys(&app.input_tys, &[]);
                    let (dict_kind, _) = trait_dictionary_node_kind(
                        arena,
                        &app.trait_ref,
                        &app.input_tys,
                        &[],
                        function_span,
                        ctx,
                        local_count,
                    )?;
                    let dict_id =
                        arena.alloc(Node::new(dict_kind, dict_ty, no_effects(), function_span));
                    let project_fn_id = alloc_dictionary_method_projection(
                        arena,
                        dict_id,
                        dict_ty,
                        &app.trait_ref,
                        app.function_index,
                        function_span,
                    );
                    let arguments = mem::take(&mut app.arguments);
                    kind = Apply(b(hir::Application {
                        function: project_fn_id,
                        arguments,
                    }));
                } else {
                    // Not fully resolved, use the dictionary to look up the trait method.
                    let dict_index = find_trait_impl_dict_index(
                        ctx.dicts,
                        &app.trait_ref,
                        &app.input_tys,
                    )
                    .expect(
                        "Dictionary for trait impl not found, type inference should have failed",
                    );
                    let dict_ty = ctx.dicts.requirements[dict_index].to_dict_type();
                    let function_span = app.function_span;
                    // Load that dictionary from the correct local variable.
                    let load_id = LocalDeclId::from_index(local_count + dict_index);
                    let load_dict_id = arena.alloc(Node::new(
                        hir::hir_syn::load(dict_index, load_id),
                        dict_ty,
                        no_effects(),
                        function_span,
                    ));
                    let project_fn_id = alloc_dictionary_method_projection(
                        arena,
                        load_dict_id,
                        dict_ty,
                        &app.trait_ref,
                        app.function_index,
                        function_span,
                    );
                    // Finally use the function pointer to call the function.
                    let arguments = mem::take(&mut app.arguments);
                    kind = Apply(b(hir::Application {
                        function: project_fn_id,
                        arguments,
                    }));
                }
            }
            GetFunction(get_fn) => {
                // Is it a function to instantiate?
                if get_fn.inst_data.dicts_req.is_empty() {
                    // No instantiation, check if it is a module function
                    if let FunctionId::Local(fn_local_id) = get_fn.function {
                        // Is the function part of the current module being compiled?
                        if let Some(inst_data) = ctx
                            .module_inst_data
                            .and_then(|inst_data| inst_data.get(&fn_local_id))
                        {
                            // Yes, build the dictionary requirements for the function if it has non-empty inst data
                            if !inst_data.is_empty() {
                                let inst_data = &inst_data.requirements;
                                // We have an instantiation, so we need a closure to pass dictionary requirements.
                                let (captures, _) = extra_args_for_module_function(
                                    arena,
                                    inst_data,
                                    node_span,
                                    ctx.dicts,
                                    local_count,
                                );
                                assert!(get_fn.inst_data.dicts_req.is_empty());
                                let node_effects = arena[node_id].effects.clone();
                                let original_kind =
                                    mem::replace(&mut kind, NodeKind::Unimplemented);
                                let function_id = arena.alloc(Node::new(
                                    original_kind,
                                    node_ty,
                                    node_effects,
                                    node_span,
                                ));
                                kind = BuildClosure(b(hir::BuildClosure {
                                    function: function_id,
                                    dictionary_captures: captures,
                                    captures: Vec::new(),
                                    captures_value_dictionary: None,
                                }));
                            }
                        }
                    }
                } else {
                    // We have an instantiation, so we need a closure to pass dictionary requirements.
                    let (captures, _) = extra_args_from_inst_data(
                        arena,
                        &get_fn.inst_data,
                        node_span,
                        ctx,
                        local_count,
                    )?;
                    get_fn.inst_data.dicts_req.clear();
                    let node_effects = arena[node_id].effects.clone();
                    let original_kind = mem::replace(&mut kind, NodeKind::Unimplemented);
                    let function_id =
                        arena.alloc(Node::new(original_kind, node_ty, node_effects, node_span));
                    kind = BuildClosure(b(hir::BuildClosure {
                        function: function_id,
                        dictionary_captures: captures,
                        captures: Vec::new(),
                        captures_value_dictionary: None,
                    }));
                }
            }
            GetTraitFunction(get_fn) => {
                assert!(
                    get_fn.inst_data.dicts_req.is_empty(),
                    "Instantiation data for trait function is not supported yet."
                );
                let resolved = get_fn.input_tys.iter().all(Type::is_constant);
                if is_value_trait_for_function_type(
                    &get_fn.trait_ref,
                    &get_fn.input_tys,
                    &get_fn.output_tys,
                ) {
                    let function = FunctionId::Local(function_value_method(
                        ctx.trait_solver,
                        get_fn.function_index,
                        get_fn.function_span,
                        arena,
                    )?);
                    kind = GetFunction(b(hir::GetFunction {
                        function,
                        function_path: get_fn.function_path.clone(),
                        function_span: get_fn.function_span,
                        inst_data: hir::FnInstData::none(),
                    }));
                } else if resolved {
                    let function = ctx.trait_solver.solve_impl_method(
                        &get_fn.trait_ref,
                        &get_fn.input_tys,
                        get_fn.function_index,
                        get_fn.function_span,
                        arena,
                    )?;
                    kind = GetFunction(b(hir::GetFunction {
                        function,
                        function_path: get_fn.function_path.clone(),
                        function_span: get_fn.function_span,
                        inst_data: hir::FnInstData::none(),
                    }));
                } else {
                    let dict_ty = get_fn
                        .trait_ref
                        .get_dictionary_type_for_tys(&get_fn.input_tys, &get_fn.output_tys);
                    let (dict_kind, _) = trait_dictionary_node_kind(
                        arena,
                        &get_fn.trait_ref,
                        &get_fn.input_tys,
                        &get_fn.output_tys,
                        get_fn.function_span,
                        ctx,
                        local_count,
                    )?;
                    let dict_id = arena.alloc(Node::new(
                        dict_kind,
                        dict_ty,
                        no_effects(),
                        get_fn.function_span,
                    ));
                    let (entry_index, _) = dictionary_method_projection_data(
                        &get_fn.trait_ref,
                        dict_ty,
                        get_fn.function_index,
                    );
                    kind = Project(dict_id, entry_index);
                }
            }
            GetTraitAssociatedConst(get_const) => {
                let resolved = get_const.input_tys.iter().all(Type::is_constant);
                if is_value_trait_for_function_type(
                    &get_const.trait_ref,
                    &get_const.input_tys,
                    &get_const.output_tys,
                ) || is_function_surface_only_value_trait_application(
                    &get_const.trait_ref,
                    &get_const.input_tys,
                    &get_const.output_tys,
                ) {
                    let values =
                        value_layout_associated_const_values(get_const.input_tys[0], node_span)?;
                    let value = values[get_const.associated_const_index];
                    kind = hir::hir_syn::native(value);
                } else if resolved {
                    let value = ctx.trait_solver.solve_associated_const(
                        &get_const.trait_ref,
                        &get_const.input_tys,
                        get_const.associated_const_index,
                        get_const.associated_const_span,
                        arena,
                    )?;
                    kind = hir::hir_syn::native(value);
                } else {
                    let dict_index = find_trait_impl_dict_index(
                        ctx.dicts,
                        &get_const.trait_ref,
                        &get_const.input_tys,
                    )
                    .expect(
                        "Dictionary for trait impl not found, type inference should have failed",
                    );
                    let dict_ty = ctx.dicts.requirements[dict_index].to_dict_type();
                    let load_id = LocalDeclId::from_index(local_count + dict_index);
                    let load_dict_id = arena.alloc(Node::new(
                        hir::hir_syn::load(dict_index, load_id),
                        dict_ty,
                        no_effects(),
                        get_const.associated_const_span,
                    ));
                    kind = Project(
                        load_dict_id,
                        get_const
                            .trait_ref
                            .dictionary_associated_const_index(get_const.associated_const_index),
                    );
                }
            }
            GetTraitDictionary(get_dict) => {
                let (node_kind, _) = trait_dictionary_node_kind(
                    arena,
                    &get_dict.trait_ref,
                    &get_dict.input_tys,
                    &get_dict.output_tys,
                    node_span,
                    ctx,
                    local_count,
                )?;
                kind = node_kind;
            }
            GetDictionary(_) => {
                // nothing to do
            }
            EnvStore(store) => {
                store.index += ctx.dicts.len() as u32;
                elaborate_dictionaries(arena, store.value, ctx, local_count)?;
            }
            EnvDrop(drop) => {
                drop.index += ctx.dicts.len() as u32;
            }
            EnvMove(load) => {
                load.index += ctx.dicts.len() as u32;
            }
            EnvLoad(load) => {
                load.index += ctx.dicts.len() as u32;
            }
            Return(node_id) => {
                elaborate_dictionaries(arena, *node_id, ctx, local_count)?;
            }
            Block(nodes) => {
                for &node_id in nodes.iter() {
                    elaborate_dictionaries(arena, node_id, ctx, local_count)?;
                }
            }
            Assign(assignment) => {
                elaborate_dictionaries(arena, assignment.place, ctx, local_count)?;
                elaborate_dictionaries(arena, assignment.value, ctx, local_count)?;
            }
            Tuple(nodes) => {
                for &node_id in nodes.iter() {
                    elaborate_dictionaries(arena, node_id, ctx, local_count)?;
                }
            }
            Project(data, _) => {
                elaborate_dictionaries(arena, *data, ctx, local_count)?;
            }
            Record(nodes) => {
                for &node_id in nodes.iter() {
                    elaborate_dictionaries(arena, node_id, ctx, local_count)?;
                }
            }
            FieldAccess(data, field) => {
                use TypeKind::*;
                let child_id = *data;
                let field_name = *field;
                elaborate_dictionaries(arena, child_id, ctx, local_count)?;
                let child_ty = arena[child_id].ty;
                let ty_data = child_ty.data();
                let ty_data = if let Some(named) = ty_data.as_named() {
                    let named = named.clone();
                    drop(ty_data);
                    named.instantiated_shape().data()
                } else {
                    ty_data
                };
                match &*ty_data {
                    Record(record) => {
                        // Known type, get the index from the type and replace the HIR instruction.
                        let index = record
                            .iter()
                            .position(|field| field.0 == field_name)
                            .expect("Field not found in type, type inference should have failed");
                        kind = Project(child_id, index);
                    }
                    Variable(var) => {
                        // Variable type, it must be in the type scheme, use the dictionary to lookup local variable.
                        let var = *var;
                        drop(ty_data);
                        let index = find_field_dict_index(ctx.dicts, var, &field_name).unwrap_or_else(
                            || panic!("Dictionary for field \"{field_name}\" in type variable \"{var}\" not found, type inference should have failed"),
                        );
                        kind = ProjectAt(child_id, index);
                    }
                    _ => {
                        panic!("FieldAccess should have a record or variable type");
                    }
                }
            }
            ProjectAt(_, _) => {
                panic!("ProjectAt should not be present at this stage");
            }
            Variant(_, payload) => {
                elaborate_dictionaries(arena, *payload, ctx, local_count)?;
            }
            ExtractTag(node_id) => {
                elaborate_dictionaries(arena, *node_id, ctx, local_count)?;
            }
            Array(nodes) => {
                for &node_id in nodes.iter() {
                    elaborate_dictionaries(arena, node_id, ctx, local_count)?;
                }
            }
            Index(array_id, index_id) => {
                elaborate_dictionaries(arena, *array_id, ctx, local_count)?;
                elaborate_dictionaries(arena, *index_id, ctx, local_count)?;
            }
            Case(case) => {
                elaborate_dictionaries(arena, case.value, ctx, local_count)?;
                for &(_, alt_id) in case.alternatives.iter() {
                    elaborate_dictionaries(arena, alt_id, ctx, local_count)?;
                }
                elaborate_dictionaries(arena, case.default, ctx, local_count)?;
            }
            Loop(body_id) => {
                elaborate_dictionaries(arena, *body_id, ctx, local_count)?;
            }
            SoftBreak | Unimplemented => {}
        }

        arena[node_id].kind = kind;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{
        FxHashMap, Location, Modules,
        containers::b,
        hir::GetTraitAssociatedConst,
        hir::function::Function,
        module::{FunctionCollector, LocalDecl, ModuleId, TraitImpls, id::Id},
        types::{
            r#trait::{TraitAssociatedConst, TraitRef},
            trait_solver::TraitSolver,
            r#type::Type,
        },
    };

    fn layout_trait() -> TraitRef {
        TraitRef::new_with_self_input_type(
            "Layout",
            "Compiler-only layout metadata.",
            Vec::<&str>::new(),
            Vec::<(&str, crate::hir::function::FunctionDefinition)>::new(),
        )
        .with_associated_consts([
            TraitAssociatedConst::new("SIZE", "Size in bytes."),
            TraitAssociatedConst::new("ALIGN", "Alignment in bytes."),
        ])
    }

    fn get_associated_const_node(
        trait_ref: TraitRef,
        associated_const_index: usize,
        input_tys: Vec<Type>,
    ) -> NodeKind {
        NodeKind::GetTraitAssociatedConst(b(GetTraitAssociatedConst {
            associated_const_name: trait_ref.associated_consts[associated_const_index].name,
            associated_const_span: Location::new_synthesized(),
            trait_ref,
            associated_const_index,
            input_tys,
            output_tys: vec![],
        }))
    }

    #[test]
    fn concrete_associated_const_elaborates_to_immediate() {
        let trait_ref = layout_trait();
        let mut arena = NodeArena::default();
        let span = Location::new_synthesized();
        let node = arena.alloc(Node::new(
            get_associated_const_node(trait_ref.clone(), 0, vec![Type::unit()]),
            int_type(),
            no_effects(),
            span,
        ));

        let mut impls = TraitImpls::new(ModuleId(0));
        let mut fn_collector = FunctionCollector::new(0);
        impls.add_concrete_raw(
            trait_ref,
            [Type::unit()],
            [],
            [8, 4],
            Vec::<(Function, Vec<LocalDecl>)>::new(),
            &mut fn_collector,
        );
        let modules = Modules::new();
        let mut import_fn_slots = Vec::new();
        let mut import_impl_slots = Vec::new();
        let mut solver = TraitSolver::new(
            &mut impls,
            FxHashMap::default(),
            &mut import_fn_slots,
            &mut import_impl_slots,
            FunctionCollector::new(0),
            &modules,
        );
        let dicts = ExtraParameters {
            requirements: vec![],
            repr_map: FxHashMap::default(),
        };
        let mut ctx = DictElaborationCtx::new(&dicts, None, &mut solver);

        elaborate_dictionaries(&mut arena, node, &mut ctx, 0).unwrap();

        let NodeKind::Immediate(immediate) = &arena[node].kind else {
            panic!("expected associated const to elaborate to an immediate");
        };
        assert_eq!(immediate.value.as_primitive_ty::<isize>(), Some(&8));
    }

    #[test]
    fn generic_associated_const_elaborates_to_dictionary_projection() {
        let trait_ref = layout_trait();
        let input_ty = Type::variable_id(0);
        let mut arena = NodeArena::default();
        let span = Location::new_synthesized();
        let node = arena.alloc(Node::new(
            get_associated_const_node(trait_ref.clone(), 1, vec![input_ty]),
            int_type(),
            no_effects(),
            span,
        ));

        let mut impls = TraitImpls::new(ModuleId(0));
        let modules = Modules::new();
        let mut import_fn_slots = Vec::new();
        let mut import_impl_slots = Vec::new();
        let mut solver = TraitSolver::new(
            &mut impls,
            FxHashMap::default(),
            &mut import_fn_slots,
            &mut import_impl_slots,
            FunctionCollector::new(0),
            &modules,
        );
        let dicts = ExtraParameters {
            requirements: vec![DictionaryReq::new_trait_impl(
                trait_ref,
                vec![input_ty],
                vec![],
            )],
            repr_map: FxHashMap::default(),
        };
        let mut ctx = DictElaborationCtx::new(&dicts, None, &mut solver);

        elaborate_dictionaries(&mut arena, node, &mut ctx, 3).unwrap();

        let NodeKind::Project(dictionary_node, index) = arena[node].kind else {
            panic!("expected associated const to elaborate to a dictionary projection");
        };
        assert_eq!(index, 1);
        let NodeKind::EnvLoad(load) = &arena[dictionary_node].kind else {
            panic!("expected dictionary projection source to load a dictionary");
        };
        assert_eq!(load.index, 0);
        assert_eq!(load.id.as_index(), 3);
    }
}
