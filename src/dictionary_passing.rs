// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::{collections::HashMap, mem};

use crate::{
    Location,
    error::InternalCompilationError,
    format::FormatWith,
    ir_syn,
    module::{FunctionId, LocalFunctionId, ModuleEnv},
    parser_helpers::EMPTY_USTR,
    r#trait::TraitRef,
    trait_solver::TraitSolver,
    r#type::TypeVar,
    type_like::TypeLike,
    type_scheme::format_have_trait,
};
use derive_new::new;
use itertools::process_results;
use ustr::{Ustr, ustr};

use crate::{
    containers::b,
    effects::no_effects,
    ir::{self, Node, NodeKind},
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
    pub repr_map: HashMap<TypeVar, TypeVar>,
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
    inst_data: &ir::FnInstData,
    span: Location,
    ctx: &mut DictElaborationCtx<'d, 'sr, 'sm>,
) -> Result<(Vec<Node>, Vec<FnArgType>), InternalCompilationError> {
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
                            K::EnvLoad(b(ir::EnvLoad { index, name: None }))
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
                        // Load the array of trait implementation functions from the dictionary
                        ir_syn::load(index)
                    };
                    let ty = trait_ref.get_dictionary_type_for_tys(input_tys, output_tys);
                    (node_kind, ty)
                }
            };
            Ok((
                Node::new(node_kind, node_ty, no_effects(), span),
                FnArgType::new(node_ty, MutType::constant()),
            ))
        }), |iter| iter.unzip()
    )
}

fn extra_args_for_module_function(
    inst_data: &DictionariesReq,
    span: Location,
    dicts: &ExtraParameters,
) -> (Vec<Node>, Vec<FnArgType>) {
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
            (
                Node::new(
                    NodeKind::EnvLoad(b(ir::EnvLoad { index, name: None })),
                    int_type(),
                    no_effects(),
                    span,
                ),
                FnArgType::new(int_type(), MutType::constant()),
            )
        })
        .unzip()
}

/// The dictionaries for the current module.
/// This is a map from function pointers to the dictionaries required by the function.
/// This is necessary as recursive functions in the current modules could not get their
/// dictionary requirements during type inference as they were not known yet.
pub type ModuleInstData = HashMap<LocalFunctionId, ExtraParameters>;

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

impl Node {
    pub fn elaborate_dictionaries<'d, 'sr, 'sm>(
        &mut self,
        ctx: &mut DictElaborationCtx<'d, 'sr, 'sm>,
    ) -> Result<(), InternalCompilationError> {
        use NodeKind::*;
        match &mut self.kind {
            Immediate(immediate) => {
                assert!(
                    !immediate.value.is_function(),
                    "Resolved functions should not be present at this stage"
                );
                if let Some(function) = immediate.value.as_pending_function_mut() {
                    // It is from the local scope, recurse to elaborate the function.
                    let mut function = function.borrow_mut();
                    let script_fn = function.as_script_mut().unwrap();
                    script_fn.code.elaborate_dictionaries(ctx)?;
                    if !ctx.dicts.is_empty() {
                        script_fn.arg_names.splice(
                            0..0,
                            ctx.dicts
                                .requirements
                                .iter()
                                .enumerate()
                                .map(|(i, r)| ustr(&r.to_dict_name(i))),
                        );
                    }
                    drop(function);
                    // Build closure to capture the dictionaries of this function, if any.
                    if !ctx.dicts.is_empty() {
                        let captures =
                            ctx.dicts
                                .requirements
                                .iter()
                                .enumerate()
                                .map(|(index, req)| {
                                    let ty = match req {
                                        DictionaryReq::FieldIndex { .. } => int_type(),
                                        DictionaryReq::TraitImpl {
                                            trait_ref,
                                            input_tys,
                                            output_tys,
                                        } => trait_ref
                                            .get_dictionary_type_for_tys(input_tys, output_tys),
                                    };
                                    Node::new(
                                        EnvLoad(b(ir::EnvLoad { index, name: None })),
                                        ty,
                                        no_effects(),
                                        self.span,
                                    )
                                })
                                .collect();
                        self.kind = BuildClosure(b(ir::BuildClosure {
                            function: self.clone(),
                            captures,
                        }));
                    }
                }
            }
            BuildClosure(build_closure) => {
                // Elaborate captures first (they are in outer scope).
                for capture in &mut build_closure.captures {
                    capture.elaborate_dictionaries(ctx)?;
                }

                // Elaborate the function (it is the closure body/value).
                build_closure.function.elaborate_dictionaries(ctx)?;

                // Optimization: flatten nested BuildClosure
                // Check if the function is a BuildClosure itself (due to dictionary capturing).
                let is_nested = matches!(build_closure.function.kind, NodeKind::BuildClosure(_));

                if is_nested {
                    // Extract the inner BuildClosure.
                    let inner_node = mem::replace(
                        &mut build_closure.function,
                        Node::new(
                            NodeKind::SoftBreak, // dummy
                            Type::unit(),
                            no_effects(),
                            self.span,
                        ),
                    );

                    let inner_build = inner_node
                        .kind
                        .into_build_closure()
                        .expect("is_nested check failed");
                    // inner_build.captures are the dictionary captures (should be first)
                    // build_closure.captures are the variable captures (should be second)
                    let inner_build = *inner_build;
                    let mut new_captures = inner_build.captures;
                    new_captures.append(&mut build_closure.captures);
                    build_closure.captures = new_captures;
                    build_closure.function = inner_build.function;
                }
            }
            Apply(app) => {
                app.function.elaborate_dictionaries(ctx)?;
                for arg in &mut app.arguments {
                    arg.elaborate_dictionaries(ctx)?;
                }
            }
            StaticApply(app) => {
                for arg in &mut app.arguments {
                    arg.elaborate_dictionaries(ctx)?;
                }
                if !app.inst_data.dicts_req.is_empty() {
                    // Build the dictionary requirements for the function by adding extra arguments before normal arguments.
                    let span = app.function_span;
                    let (extra_args, extra_args_ty) =
                        extra_args_from_inst_data(&app.inst_data, span, ctx)?;
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
                            let (extra_args, extra_args_ty) =
                                extra_args_for_module_function(inst_data, self.span, ctx.dicts);
                            app.argument_names
                                .splice(0..0, extra_args.iter().map(|_| *EMPTY_USTR));
                            app.arguments.splice(0..0, extra_args);
                            app.ty.args.splice(0..0, extra_args_ty);

                            // Debug dump
                            // let current = new_module_with_prelude();
                            // let others = crate::std::new_std_module_env();
                            // let module_env = crate::module::ModuleEnv::new(&current, &others);
                            // println!(
                            //     "StaticApply app fn type: {}",
                            //     app.ty.format_with(&module_env)
                            // );
                            // // TODO: use function ty
                            // print!("Extra params for that function: ");
                            // for param in extra_params {
                            //     print!("{}, ", param.format_with(&module_env));
                            // }
                            // println!();
                            // print!("Extra params for cur function: ");
                            // for dict in dicts {
                            //     print!("{}, ", dict.format_with(&module_env));
                            // }
                            // println!();
                        }
                    }
                }
            }
            TraitFnApply(app) => {
                for arg in &mut app.arguments {
                    arg.elaborate_dictionaries(ctx)?;
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
                    self.kind = StaticApply(b(ir::StaticApplication {
                        function,
                        function_path: Some(app.function_path.clone()),
                        function_span: app.function_span,
                        arguments: mem::take(&mut app.arguments),
                        argument_names,
                        ty: app.ty.clone(),
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
                    let mut fns_tuple_ty = vec![Type::never(); app.trait_ref.functions.len()];
                    let fn_ty = Type::function_type(app.ty.clone());
                    fns_tuple_ty[app.function_index] = fn_ty;
                    let fns_tuple_ty = Type::tuple(fns_tuple_ty);
                    // Load that tuple from the correct local variable...
                    let load_fns_tuple = Node::new(
                        ir_syn::load(fns_tuple_index),
                        fns_tuple_ty,
                        no_effects(),
                        app.function_span,
                    );
                    // ...and from it the function pointer.
                    let project_fn = Node::new(
                        ir_syn::project(load_fns_tuple, app.function_index),
                        fn_ty,
                        no_effects(),
                        app.function_span,
                    );
                    // Finally use the function pointer to call the function.
                    let arguments = mem::take(&mut app.arguments);
                    self.kind = Apply(b(ir::Application {
                        function: project_fn,
                        arguments,
                    }));
                }
            }
            GetFunction(get_fn) => {
                // Is it a function to instantiate?
                if get_fn.inst_data.dicts_req.is_empty() {
                    // No instantiation, check if it is a module function
                    if let FunctionId::Local(id) = get_fn.function {
                        // Is the function part of the current module being compiled?
                        if let Some(inst_data) = ctx
                            .module_inst_data
                            .and_then(|inst_data| inst_data.get(&id))
                        {
                            // Yes, build the dictionary requirements for the function if it has non-empty inst data
                            if !inst_data.is_empty() {
                                let inst_data = &inst_data.requirements;
                                // We have an instantiation, so we need a closure to pass dictionary requirements.
                                let (captures, _) =
                                    extra_args_for_module_function(inst_data, self.span, ctx.dicts);
                                assert!(get_fn.inst_data.dicts_req.is_empty());
                                self.kind = BuildClosure(b(ir::BuildClosure {
                                    function: self.clone(),
                                    captures,
                                }));
                            }
                        }
                    }
                } else {
                    // We have an instantiation, so we need a closure to pass dictionary requirements.
                    let (captures, _) =
                        extra_args_from_inst_data(&get_fn.inst_data, self.span, ctx)?;
                    get_fn.inst_data.dicts_req.clear();
                    self.kind = BuildClosure(b(ir::BuildClosure {
                        function: self.clone(),
                        captures,
                    }));
                }
            }
            GetDictionary(_) => {
                // nothing to do
            }
            EnvStore(store) => {
                store.index += ctx.dicts.len();
                store.value.elaborate_dictionaries(ctx)?;
            }
            EnvLoad(load) => {
                load.index += ctx.dicts.len();
            }
            Return(node) => {
                node.elaborate_dictionaries(ctx)?;
            }
            Block(nodes) => {
                for node in nodes.iter_mut() {
                    node.elaborate_dictionaries(ctx)?;
                }
            }
            Assign(assignment) => {
                assignment.place.elaborate_dictionaries(ctx)?;
                assignment.value.elaborate_dictionaries(ctx)?;
            }
            Tuple(nodes) => {
                for node in nodes.iter_mut() {
                    node.elaborate_dictionaries(ctx)?;
                }
            }
            Project(projection) => {
                projection.0.elaborate_dictionaries(ctx)?;
            }
            Record(nodes) => {
                for node in nodes.iter_mut() {
                    node.elaborate_dictionaries(ctx)?;
                }
            }
            FieldAccess(access) => {
                use TypeKind::*;
                access.0.elaborate_dictionaries(ctx)?;
                let name = access.1;
                let span = access.0.span;
                let ty = access.0.ty;
                let ty_data = ty.data().clone();
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
                            .position(|field| field.0 == name)
                            .expect("Field not found in type, type inference should have failed");
                        let node = mem::replace(
                            &mut access.as_mut().0,
                            Node::new(
                                Immediate(ir::Immediate::new(Value::unit())),
                                Type::unit(),
                                no_effects(),
                                span,
                            ),
                        );
                        self.kind = Project(b((node, index)));
                    }
                    Variable(var) => {
                        // Variable type, it must be in the type scheme, use the dictionary to lookup local variable.
                        let index = find_field_dict_index(ctx.dicts, var, &name).unwrap_or_else(
                            || panic!("Dictionary for field \"{name}\" in type variable \"{var}\" not found, type inference should have failed"),
                        );
                        let node = mem::replace(
                            &mut access.as_mut().0,
                            Node::new(
                                Immediate(ir::Immediate::new(Value::unit())),
                                Type::unit(),
                                no_effects(),
                                span,
                            ),
                        );
                        self.kind = ProjectAt(b((node, index)));
                    }
                    _ => {
                        panic!("FieldAccess should have a record or variable type");
                    }
                }
            }
            ProjectAt(_) => {
                panic!("ProjectAt should not be present at this stage");
            }
            Variant(variant) => {
                variant.1.elaborate_dictionaries(ctx)?;
            }
            ExtractTag(node) => {
                node.elaborate_dictionaries(ctx)?;
            }
            Array(nodes) => {
                for node in nodes.iter_mut() {
                    node.elaborate_dictionaries(ctx)?;
                }
            }
            Index(array, index) => {
                array.elaborate_dictionaries(ctx)?;
                index.elaborate_dictionaries(ctx)?;
            }
            Case(case) => {
                case.value.elaborate_dictionaries(ctx)?;
                for (_, node) in &mut case.alternatives {
                    node.elaborate_dictionaries(ctx)?;
                }
                case.default.elaborate_dictionaries(ctx)?;
            }
            Loop(body) => {
                body.elaborate_dictionaries(ctx)?;
            }
            SoftBreak => {}
        }
        Ok(())
    }
}
