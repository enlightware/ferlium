// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{collections::HashMap, mem};

use crate::{
    error::InternalCompilationError, format::write_with_separator_and_format_fn,
    parser_helpers::EMPTY_USTR, r#trait::TraitRef, trait_solver::TraitImpls, type_like::TypeLike,
    Location,
};
use itertools::process_results;
use ustr::Ustr;

use crate::{
    containers::b,
    effects::no_effects,
    function::FunctionPtr,
    ir::{self, Node, NodeKind},
    module::FmtWithModuleEnv,
    mutability::MutType,
    r#type::{FnArgType, Type, TypeKind},
    std::math::int_type,
    type_inference::InstSubstitution,
    value::Value,
};

/// A dictionary requirement, that will be passed as extra parameter to a function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DictionaryReq {
    FieldIndex(Type, Ustr),
    TraitImpl {
        trait_ref: TraitRef,
        input_tys: Vec<Type>,
        // FIXME: maybe we need a span here for proper error reporting
    },
}

impl DictionaryReq {
    pub fn new_field_index(ty: Type, field: Ustr) -> Self {
        Self::FieldIndex(ty, field)
    }
    pub fn new_trait_impl(trait_ref: TraitRef, input_tys: Vec<Type>) -> Self {
        Self::TraitImpl {
            trait_ref,
            input_tys,
        }
    }
}
impl DictionaryReq {
    pub fn instantiate(&self, subst: &InstSubstitution) -> DictionaryReq {
        use DictionaryReq::*;
        match self {
            FieldIndex(ty, field) => FieldIndex(ty.instantiate(subst), *field),
            TraitImpl {
                trait_ref,
                input_tys,
            } => TraitImpl {
                trait_ref: trait_ref.clone(),
                input_tys: input_tys.iter().map(|ty| ty.instantiate(subst)).collect(),
            },
        }
    }
}

impl FmtWithModuleEnv for DictionaryReq {
    fn fmt_with_module_env(
        &self,
        f: &mut std::fmt::Formatter,
        env: &crate::module::ModuleEnv<'_>,
    ) -> std::fmt::Result {
        use DictionaryReq::*;
        match self {
            FieldIndex(ty, field) => write!(f, "{} field {}", ty.format_with(env), field),
            TraitImpl {
                trait_ref,
                input_tys,
            } => {
                write_with_separator_and_format_fn(
                    input_tys.iter(),
                    ", ",
                    |ty, f| write!(f, "{}", ty.format_with(env)),
                    f,
                )?;
                write!(f, " impl {}", trait_ref.name)
            }
        }
    }
}

pub type DictionariesReq = Vec<DictionaryReq>;

pub fn find_field_dict_index(dicts: &DictionariesReq, ty: Type, field: &str) -> Option<usize> {
    dicts.iter().position(|dict| {
        if let DictionaryReq::FieldIndex(ty2, field2) = &dict {
            *ty2 == ty && field2 == &field
        } else {
            false
        }
    })
}

pub fn find_trait_impl_dict_index(
    dicts: &DictionariesReq,
    trait_ref: &TraitRef,
    input_tys: &[Type],
) -> Option<usize> {
    dicts.iter().position(|dict| {
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

fn extra_args_from_inst_data(
    inst_data: &ir::FnInstData,
    span: Location,
    ctx: DictElaborationCtx,
) -> Result<(Vec<Node>, Vec<FnArgType>), InternalCompilationError> {
    use NodeKind as K;
    use TypeKind::*;
    process_results(inst_data
        .dicts_req
        .iter()
        .map(|dict| {
            use DictionaryReq::*;
            let (node_kind, node_ty) = match dict {
                FieldIndex(ty, name) => {
                    let ty_data = ty.data().clone();
                    let node_kind = match ty_data {
                        Record(record) => {
                            // Known type, get the index from the type and create an immediate with it.
                            let index = record.iter().position(|field| field.0 == *name).expect(
                                "Field not found in type, type inference should have failed"
                            );
                            K::Immediate(ir::Immediate::new(Value::native(index as isize)))
                        }
                        Variable(_var) => {
                            // Variable, it must be in the input dictionaries, look for it.
                            let index = find_field_dict_index(ctx.dicts, *ty, name).expect(
                                "Dictionary for field not found, type inference should have failed",
                            );
                            K::EnvLoad(b(ir::EnvLoad { index, name: None }))
                        }
                        _ => {
                            panic!("FieldIndex dictionary should have a variable or record type");
                        }
                    };
                    (node_kind, int_type())
                }
                TraitImpl { trait_ref, input_tys, .. } => {
                    // Build a fake type for the trait function array as we might not know the trait output type at this point.
                    let fns_tuple_ty = vec![Type::never(); trait_ref.functions.len()];
                    // Is the trait fully resolved?
                    let resolved = input_tys.iter().all(Type::is_constant);
                    let node_kind = if resolved {
                        // Fully resolved, look up the trait implementation and build the trait function array.
                        let functions = ctx.trait_impls.get_functions(trait_ref, input_tys, span)?;
                        K::Immediate(ir::Immediate::new(functions.clone()))
                    } else {
                        // Not fully resolved, it must be in the input dictionaries, look for it.
                        let index = find_trait_impl_dict_index(ctx.dicts, trait_ref, input_tys)
                            .expect(
                            "Dictionary for trait impl not found, type inference should have failed",
                        );
                        // Load the array of trait implementation functions from the dictionary
                        K::EnvLoad(b(ir::EnvLoad { index, name: None }))
                    };
                    (node_kind, Type::tuple(fns_tuple_ty))
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
    dicts: &DictionariesReq,
) -> (Vec<Node>, Vec<FnArgType>) {
    inst_data
        .iter()
        .map(|dict| {
            // We find the index of the called function's requirement dict
            // in our requirement dicts. As dictionary passing is done
            // before type scheme simplification, they can be matched 1 to 1.
            let index = dicts
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
pub type ModuleInstData = HashMap<FunctionPtr, DictionariesReq>;

/// The context for elaborating dictionaries.
/// All necessary information to perform dictionary elaboration.
// #[derive(Clone, Copy)]
pub struct DictElaborationCtx<'a> {
    /// The dictionaries for the current expression being elaborated.
    pub dicts: &'a DictionariesReq,
    /// The dictionaries for the current module, if compiling a module.
    /// None if compiling an expression.
    pub module_inst_data: Option<&'a ModuleInstData>,
    /// All trait visible implementations.
    pub trait_impls: &'a mut TraitImpls,
}
impl<'a> DictElaborationCtx<'a> {
    pub fn new(
        dicts: &'a DictionariesReq,
        module_inst_data: Option<&'a ModuleInstData>,
        trait_impls: &'a mut TraitImpls,
    ) -> Self {
        Self {
            dicts,
            module_inst_data,
            trait_impls,
        }
    }

    pub fn reborrow(&mut self) -> DictElaborationCtx<'_> {
        DictElaborationCtx {
            dicts: self.dicts,
            module_inst_data: self.module_inst_data,
            trait_impls: &mut *self.trait_impls,
        }
    }
}

impl Node {
    pub fn elaborate_dictionaries(
        &mut self,
        mut ctx: DictElaborationCtx,
    ) -> Result<(), InternalCompilationError> {
        use NodeKind::*;
        match &mut self.kind {
            Immediate(immediate) => {
                if let Some(function) = immediate.value.as_function_mut() {
                    // Is this a function to instantiate?
                    if immediate.inst_data.dicts_req.is_empty() {
                        let function = function.0.get();
                        // No instantiation, check if it is a module function
                        let fn_ptr = function.as_ptr();
                        if let Some(inst_data) = ctx
                            .module_inst_data
                            .and_then(|inst_data| inst_data.get(&fn_ptr))
                        {
                            // Yes, build the dictionary requirements for the function if it has non-empty inst data
                            if !inst_data.is_empty() {
                                // We have an instantiation, so we need a closure to pass dictionary requirements.
                                let (captures, _) =
                                    extra_args_for_module_function(inst_data, self.span, ctx.dicts);
                                assert!(immediate.inst_data.dicts_req.is_empty());
                                self.kind = BuildClosure(b(ir::BuildClosure {
                                    function: self.clone(),
                                    captures,
                                }));
                            }
                        } else {
                            // It is not a module function, is it from the local scope?
                            if immediate.substitute_in_value_fn {
                                // Yes, recurse to elaborate the function.
                                let mut function = function.borrow_mut();
                                let script_fn = function.as_script_mut().unwrap();
                                script_fn.code.elaborate_dictionaries(ctx.reborrow())?;
                                // Build closure to capture the dictionaries of this function, if any.
                                if !ctx.dicts.is_empty() {
                                    let captures = (0..ctx.dicts.len())
                                        .map(|index| {
                                            Node::new(
                                                EnvLoad(b(ir::EnvLoad { index, name: None })),
                                                int_type(),
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
                    } else {
                        // We have an instantiation, so we need a closure to pass dictionary requirements.
                        let (captures, _) =
                            extra_args_from_inst_data(&immediate.inst_data, self.span, ctx)?;
                        immediate.inst_data.dicts_req.clear();
                        self.kind = BuildClosure(b(ir::BuildClosure {
                            function: self.clone(),
                            captures,
                        }));
                    }
                }
            }
            BuildClosure(_) => {
                panic!("BuildClosure should not be present at this stage");
            }
            Apply(app) => {
                app.function.elaborate_dictionaries(ctx.reborrow())?;
                for arg in &mut app.arguments {
                    arg.elaborate_dictionaries(ctx.reborrow())?;
                }
            }
            StaticApply(app) => {
                for arg in &mut app.arguments {
                    arg.elaborate_dictionaries(ctx.reborrow())?;
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
                    let fn_ptr = app.function.get().as_ptr();
                    if let Some(inst_data) = ctx
                        .module_inst_data
                        .and_then(|inst_data| inst_data.get(&fn_ptr))
                    {
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
            TraitFnApply(app) => {
                for arg in &mut app.arguments {
                    arg.elaborate_dictionaries(ctx.reborrow())?;
                }
                assert!(
                    app.inst_data.dicts_req.is_empty(),
                    "Instantiation data for trait function is not supported yet."
                );
                // Is the trait fully resolved?
                let resolved = app.input_tys.iter().all(Type::is_constant);
                if resolved {
                    // Fully resolved, look up the trait implementation and replace the function directly.
                    let functions = ctx.trait_impls.get_functions(
                        &app.trait_ref,
                        &app.input_tys,
                        app.function_span,
                    )?;
                    let fn_tuple = functions
                        .as_tuple()
                        .expect("Trait impl functions is not a tuple");
                    let function = fn_tuple[app.function_index]
                        .as_function()
                        .expect("Trait impl function is not a function")
                        .0
                        .clone();
                    self.kind = StaticApply(b(ir::StaticApplication {
                        function,
                        function_path: app.function_path,
                        function_span: app.function_span,
                        arguments: mem::take(&mut app.arguments),
                        argument_names: app.trait_ref.functions[app.function_index]
                            .1
                            .arg_names
                            .clone(),
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
                        NodeKind::EnvLoad(b(ir::EnvLoad {
                            index: fns_tuple_index,
                            name: None,
                        })),
                        fns_tuple_ty,
                        no_effects(),
                        app.function_span,
                    );
                    // ...and from it the function pointer.
                    let project_fn = Node::new(
                        NodeKind::Project(b((load_fns_tuple, app.function_index))),
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
            EnvStore(store) => {
                store.node.elaborate_dictionaries(ctx)?;
            }
            EnvLoad(load) => {
                load.index += ctx.dicts.len();
            }
            Block(nodes) => {
                for node in nodes.iter_mut() {
                    node.elaborate_dictionaries(ctx.reborrow())?;
                }
            }
            Assign(assignment) => {
                assignment.place.elaborate_dictionaries(ctx.reborrow())?;
                assignment.value.elaborate_dictionaries(ctx)?;
            }
            Tuple(nodes) => {
                for node in nodes.iter_mut() {
                    node.elaborate_dictionaries(ctx.reborrow())?;
                }
            }
            Project(projection) => {
                projection.0.elaborate_dictionaries(ctx)?;
            }
            Record(nodes) => {
                for node in nodes.iter_mut() {
                    node.elaborate_dictionaries(ctx.reborrow())?;
                }
            }
            FieldAccess(access) => {
                use TypeKind::*;
                access.0.elaborate_dictionaries(ctx.reborrow())?;
                let name = access.1;
                let span = access.0.span;
                let ty = access.0.ty;
                let ty_data = ty.data().clone();
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
                    Variable(_var) => {
                        // Variable type, it must be in the type scheme, use the dictionary to lookup local variable.
                        let index = find_field_dict_index(ctx.dicts, ty, &name).expect(
                            "Dictionary for field not found, type inference should have failed",
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
                    node.elaborate_dictionaries(ctx.reborrow())?;
                }
            }
            Index(array, index) => {
                array.elaborate_dictionaries(ctx.reborrow())?;
                index.elaborate_dictionaries(ctx)?;
            }
            Case(case) => {
                case.value.elaborate_dictionaries(ctx.reborrow())?;
                for (_, node) in &mut case.alternatives {
                    node.elaborate_dictionaries(ctx.reborrow())?;
                }
                case.default.elaborate_dictionaries(ctx)?;
            }
            Iterate(iteration) => {
                iteration.iterator.elaborate_dictionaries(ctx.reborrow())?;
                iteration.body.elaborate_dictionaries(ctx)?;
            }
        }
        Ok(())
    }
}
