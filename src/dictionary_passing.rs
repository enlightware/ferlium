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
    error::InternalCompilationError,
    format::FormatWith,
    ir_syn,
    module::{FunctionId, LocalDeclId, LocalFunctionId, ModuleEnv, id::Id},
    parser_helpers::EMPTY_USTR,
    r#trait::TraitRef,
    trait_solver::TraitSolver,
    r#type::TypeVar,
    type_like::TypeLike,
    type_scheme::format_have_trait,
};
use derive_new::new;
use itertools::process_results;
use ustr::Ustr;

use crate::{
    containers::b,
    effects::no_effects,
    ir::{self, Node, NodeArena, NodeId, NodeKind},
    mutability::MutType,
    std::math::int_type,
    r#type::{FnArgType, Type, TypeKind},
    type_inference::InstSubstitution,
    value::Value,
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

pub fn instantiate_dictionaries_req(
    dicts: &DictionariesReq,
    subst: &InstSubstitution,
) -> DictionariesReq {
    dicts.iter().map(|dict| dict.instantiate(subst)).collect()
}

fn extra_args_from_inst_data<'d, 'sr, 'sm>(
    arena: &mut NodeArena,
    inst_data: &ir::FnInstData,
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
                    let ty_data = ty.data().clone();
                    let node_kind = match ty_data {
                        Record(record) => {
                            // Known type, get the index from the type and create an immediate with it.
                            let index = record.iter().position(|field| field.0 == *name).expect(
                                "Field not found in type, type inference should have failed"
                            );
                            K::Immediate(ir::Immediate::new(Value::native(index as isize)))
                        }
                        Variable(var) => {
                            // Variable, it must be in the input dictionaries, look for it.
                            let index = find_field_dict_index(ctx.dicts, var, name).unwrap_or_else(
                            || panic!("Dictionary for field \"{name}\" in type variable \"{var}\" not found, type inference should have failed"),
                        );
                            let id = LocalDeclId::from_index(local_count + index);
                            K::EnvLoad(ir::EnvLoad { index: index as u32, id })
                        }
                        _ => {
                            panic!("FieldIndex dictionary should have a variable or record type");
                        }
                    };
                    (node_kind, int_type())
                }
                TraitImpl { trait_ref, input_tys, output_tys, .. } => {
                    // Is the trait fully resolved?
                    let resolved = input_tys.iter().all(Type::is_constant);
                    let node_kind = if resolved {
                        // Fully resolved, look up the trait implementation and build the trait function array.
                        let dictionary = ctx.trait_solver.solve_impl(trait_ref, input_tys, span)?;
                        K::GetDictionary(ir::GetDictionary { dictionary })
                    } else {
                        // Not fully resolved, it must be in the input dictionaries, look for it.
                        let index = find_trait_impl_dict_index(ctx.dicts, trait_ref, input_tys)
                            .expect(
                            "Dictionary for trait impl not found, type inference should have failed",
                        );
                        let id = LocalDeclId::from_index(local_count + index);
                        // Load the array of trait implementation functions from the dictionary
                        ir_syn::load(index, id)
                    };
                    let ty = trait_ref.get_dictionary_type_for_tys(input_tys, output_tys);
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
            let id = LocalDeclId::from_index(local_count + index);
            (
                arena.alloc(Node::new(
                    NodeKind::EnvLoad(ir::EnvLoad {
                        index: index as u32,
                        id,
                    }),
                    int_type(),
                    no_effects(),
                    span,
                )),
                FnArgType::new(int_type(), MutType::constant()),
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
                                    EnvLoad(ir::EnvLoad {
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
                        kind = BuildClosure(b(ir::BuildClosure {
                            function: function_id,
                            captures,
                        }));
                    }
                }
            }
            BuildClosure(build_closure) => {
                // Elaborate captures first (they are in outer scope).
                for &capture_id in &build_closure.captures {
                    elaborate_dictionaries(arena, capture_id, ctx, local_count)?;
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
                    let mut new_captures = inner_build.captures;
                    new_captures.append(&mut build_closure.captures);
                    build_closure.captures = new_captures;
                    build_closure.function = inner_build.function;
                }
            }
            Apply(app) => {
                elaborate_dictionaries(arena, app.function, ctx, local_count)?;
                for &arg_id in &app.arguments {
                    elaborate_dictionaries(arena, arg_id, ctx, local_count)?;
                }
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
                // Is the trait fully resolved?
                let resolved = app.input_tys.iter().all(Type::is_constant);
                if resolved {
                    // Fully resolved, look up the trait implementation and replace the function directly.
                    let function = ctx.trait_solver.solve_impl_method(
                        &app.trait_ref,
                        &app.input_tys,
                        app.function_index,
                        app.function_span,
                    )?;
                    let definition = &app.trait_ref.functions[app.function_index].1;
                    let argument_names = app.arguments_unnamed.filter_args(&definition.arg_names);
                    let function_path = Some(app.function_path.clone());
                    let function_span = app.function_span;
                    let ty = app.ty.clone();
                    let arguments = mem::take(&mut app.arguments);
                    kind = StaticApply(b(ir::StaticApplication {
                        function,
                        function_path,
                        function_span,
                        arguments,
                        argument_names,
                        ty,
                        inst_data: ir::FnInstData::none(),
                    }));
                } else {
                    // Not fully resolved, use the dictionary to look up the trait functions tuple...
                    let fns_tuple_index = find_trait_impl_dict_index(
                        ctx.dicts,
                        &app.trait_ref,
                        &app.input_tys,
                    )
                    .expect(
                        "Dictionary for trait impl not found, type inference should have failed",
                    );
                    // Build a tuple type where the app.function_index_th element is the function pointer
                    // and the rest never;
                    let fns_tuple_ty = ctx.dicts.requirements[fns_tuple_index].to_dict_type();
                    let function_span = app.function_span;
                    let function_index = app.function_index;
                    // Load that tuple from the correct local variable...
                    let load_id = LocalDeclId::from_index(local_count + fns_tuple_index);
                    let load_fns_tuple_id = arena.alloc(Node::new(
                        ir_syn::load(fns_tuple_index, load_id),
                        fns_tuple_ty,
                        no_effects(),
                        function_span,
                    ));
                    // ...and from it the function pointer.
                    let fn_ty = fns_tuple_ty
                        .data()
                        .as_tuple()
                        .expect("Trait impl dict should be a tuple type")[function_index];
                    let project_fn_id = arena.alloc(Node::new(
                        Project(load_fns_tuple_id, function_index),
                        fn_ty,
                        no_effects(),
                        function_span,
                    ));
                    // Finally use the function pointer to call the function.
                    let arguments = mem::take(&mut app.arguments);
                    kind = Apply(b(ir::Application {
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
                                kind = BuildClosure(b(ir::BuildClosure {
                                    function: function_id,
                                    captures,
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
                    kind = BuildClosure(b(ir::BuildClosure {
                        function: function_id,
                        captures,
                    }));
                }
            }
            GetDictionary(_) => {
                // nothing to do
            }
            EnvStore(store) => {
                store.index += ctx.dicts.len() as u32;
                elaborate_dictionaries(arena, store.value, ctx, local_count)?;
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
                let ty_data = child_ty.data().clone();
                let ty_data = if let Some(named) = ty_data.as_named() {
                    assert!(
                        named.params.is_empty(),
                        "Field access on named types with parameters is not supported yet"
                    );
                    named.def.shape.data().clone()
                } else {
                    ty_data
                };
                match ty_data {
                    Record(record) => {
                        // Known type, get the index from the type and replace the IR instruction.
                        let index = record
                            .iter()
                            .position(|field| field.0 == field_name)
                            .expect("Field not found in type, type inference should have failed");
                        kind = Project(child_id, index);
                    }
                    Variable(var) => {
                        // Variable type, it must be in the type scheme, use the dictionary to lookup local variable.
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
