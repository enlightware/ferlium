use std::{collections::HashMap, mem};

use lrpar::Span;
use ustr::Ustr;

use crate::{
    containers::B,
    function::FunctionPtr,
    ir::{self, FnInstData, Node, NodeKind},
    module::FmtWithModuleEnv,
    mutability::MutType,
    r#type::{FnArgType, Type, TypeKind, TypeLike, TypeSubstitution, TypeVar, TypeVarSubstitution},
    std::math::int_type,
    value::Value,
};

/// What kind of dictionary we are considering.
#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum DictionaryKind {
    FieldIndex(Ustr),
}

/// A dictionary requirement, that will be passed as extra parameter to a function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DictionaryReq<T> {
    pub ty: T,
    pub kind: DictionaryKind,
}

impl<T> DictionaryReq<T> {
    pub fn new(ty: T, kind: DictionaryKind) -> Self {
        Self { ty, kind }
    }
    pub fn new_field_index(ty: T, field: Ustr) -> Self {
        Self {
            ty,
            kind: DictionaryKind::FieldIndex(field),
        }
    }
}
impl DictionaryReq<TypeVar> {
    pub fn instantiate(&self, subst: &TypeSubstitution) -> DictionaryReq<Type> {
        DictionaryReq {
            ty: subst
                .get(&self.ty)
                .cloned()
                .unwrap_or_else(|| Type::variable(self.ty)),
            kind: self.kind,
        }
    }
}
impl DictionaryReq<Type> {
    pub fn substitute(&self, subst: &TypeVarSubstitution) -> Self {
        Self {
            ty: self.ty.substitute(subst),
            kind: self.kind,
        }
    }
}

impl FmtWithModuleEnv for DictionaryReq<TypeVar> {
    fn fmt_with_module_env(
        &self,
        f: &mut std::fmt::Formatter,
        _env: &crate::module::ModuleEnv<'_>,
    ) -> std::fmt::Result {
        write!(
            f,
            "{} {}",
            self.ty,
            match &self.kind {
                DictionaryKind::FieldIndex(field) => format!("field {}", field),
            }
        )
    }
}

impl FmtWithModuleEnv for DictionaryReq<Type> {
    fn fmt_with_module_env(
        &self,
        f: &mut std::fmt::Formatter,
        env: &crate::module::ModuleEnv<'_>,
    ) -> std::fmt::Result {
        write!(
            f,
            "{} {}",
            self.ty.format_with(env),
            match &self.kind {
                DictionaryKind::FieldIndex(field) => format!("field {}", field),
            }
        )
    }
}

pub type DictionariesVarReq = Vec<DictionaryReq<TypeVar>>;
pub type DictionariesTyReq = Vec<DictionaryReq<Type>>;

pub fn find_field_dict_index(
    dicts: &DictionariesVarReq,
    var: TypeVar,
    field: Ustr,
) -> Option<usize> {
    dicts.iter().position(|dict| {
        #[allow(irrefutable_let_patterns)] // later we'll also have type classes
        if let DictionaryKind::FieldIndex(f) = &dict.kind {
            dict.ty == var && f == &field
        } else {
            false
        }
    })
}

pub fn instantiate_dictionaries_req(
    dicts: &DictionariesVarReq,
    subst: &TypeSubstitution,
) -> DictionariesTyReq {
    dicts.iter().map(|dict| dict.instantiate(subst)).collect()
}

pub fn substitute_dictionaries_req(
    dicts: &DictionariesTyReq,
    subst: &TypeVarSubstitution,
) -> DictionariesTyReq {
    dicts.iter().map(|dict| dict.substitute(subst)).collect()
}

fn extra_args_from_inst_data(
    inst_data: &ir::FnInstData,
    span: Span,
    dicts: &DictionariesVarReq,
) -> (Vec<Node>, Vec<FnArgType>) {
    inst_data
        .dicts_req
        .iter()
        .map(|dict| {
            let (node_kind, node_ty) = match dict.kind {
                DictionaryKind::FieldIndex(name) => {
                    let ty_data = dict.ty.data().clone();
                    use NodeKind as K;
                    use TypeKind::*;
                    let node_kind = match ty_data {
                        Variable(var) => {
                            // Variable, it must be in the input dictionaries, look for it.
                            let index = find_field_dict_index(dicts, var, name).expect(
                                "Dictionary for field not found, type inference should have failed",
                            );
                            K::EnvLoad(B::new(ir::EnvLoad {
                                index,
                                inst_data: FnInstData::none(),
                            }))
                        }
                        Record(rec) => {
                            // Known type, get the index from the type and create an immediate with it.
                            let index = rec.iter().position(|field| field.0 == name).expect(
                                "Field not found in type, type inference should have failed",
                            );
                            K::Immediate(ir::Immediate::new(Value::native(index as isize)))
                        }
                        _ => {
                            panic!("FieldIndex dictionary should have a variable type");
                        }
                    };
                    (node_kind, int_type())
                }
            };
            (
                Node::new(node_kind, node_ty, span),
                FnArgType::new(node_ty, MutType::constant()),
            )
        })
        .unzip()
}

fn extra_args_for_module_function(
    inst_data: &DictionariesVarReq,
    span: Span,
    dicts: &DictionariesVarReq,
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
                    NodeKind::EnvLoad(B::new(ir::EnvLoad {
                        index,
                        inst_data: FnInstData::none(),
                    })),
                    int_type(),
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
pub type ModuleInstData = HashMap<FunctionPtr, DictionariesVarReq>;

impl Node {
    pub fn elaborate_dictionaries(
        &mut self,
        dicts: &DictionariesVarReq,
        module_inst_data: Option<&ModuleInstData>,
    ) {
        use NodeKind::*;
        match &mut self.kind {
            Immediate(immediate) => {
                if let Some(function) = immediate.value.as_function_mut() {
                    if immediate.inst_data.dicts_req.is_empty() {
                        let function = function.get();
                        // Note: this can fail if we are having a recursive function used as a value, in that case do not recurse.
                        let function = function.try_borrow_mut();
                        if let Ok(mut function) = function {
                            if let Some(script_fn) = function.as_script_mut() {
                                script_fn
                                    .code
                                    .elaborate_dictionaries(dicts, module_inst_data);
                            }
                        }
                    } else {
                        // We have an instantiation, so we need a closure to pass dictionary requirements.
                        let (captures, _) =
                            extra_args_from_inst_data(&immediate.inst_data, self.span, dicts);
                        immediate.inst_data.dicts_req.clear();
                        self.kind = BuildClosure(B::new(ir::BuildClosure {
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
                app.function.elaborate_dictionaries(dicts, module_inst_data);
                for arg in &mut app.arguments {
                    arg.elaborate_dictionaries(dicts, module_inst_data);
                }
            }
            StaticApply(app) => {
                for arg in &mut app.arguments {
                    arg.elaborate_dictionaries(dicts, module_inst_data);
                }
                if !app.inst_data.dicts_req.is_empty() {
                    // Build the dictionary requirements for the function by adding extra arguments before normal arguments.
                    let span = app.function_span;
                    let (extra_args, extra_args_ty) =
                        extra_args_from_inst_data(&app.inst_data, span, dicts);
                    // First add the extra parameters, then the original arguments.
                    app.arguments.splice(0..0, extra_args);
                    // Adapt real function type as well
                    app.ty.args.splice(0..0, extra_args_ty);
                } else {
                    // Is the called function part of the current module being compiled?
                    let fn_ptr = app.function.get().as_ptr();
                    if let Some(inst_data) =
                        module_inst_data.and_then(|inst_data| inst_data.get(&fn_ptr))
                    {
                        // Yes, build the dictionary requirements for the function.
                        let (extra_args, extra_args_ty) =
                            extra_args_for_module_function(inst_data, self.span, dicts);
                        app.arguments.splice(0..0, extra_args);
                        app.ty.args.splice(0..0, extra_args_ty);

                        // Dump
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
            EnvStore(store) => {
                // As we have no capture at the moment, this let expression is fully shielded from the outer scope.
                // So we can consider its type scheme to elaborate the corresponding dictionaries.
                let dicts = store.ty_scheme.extra_parameters();
                store.node.elaborate_dictionaries(&dicts, module_inst_data);
            }
            EnvLoad(load) => {
                load.index += dicts.len();
                if load.inst_data.any() {
                    // This load has dictionary requirements, so we need a closure to pass them.
                    let (captures, _) =
                        extra_args_from_inst_data(&load.inst_data, self.span, dicts);
                    load.inst_data.dicts_req.clear();
                    self.kind = BuildClosure(B::new(ir::BuildClosure {
                        function: self.clone(),
                        captures,
                    }));
                }
            }
            Block(nodes) => {
                for node in nodes.iter_mut() {
                    node.elaborate_dictionaries(dicts, module_inst_data);
                }
            }
            Assign(assignment) => {
                assignment
                    .place
                    .elaborate_dictionaries(dicts, module_inst_data);
                assignment
                    .value
                    .elaborate_dictionaries(dicts, module_inst_data);
            }
            Tuple(nodes) => {
                for node in nodes.iter_mut() {
                    node.elaborate_dictionaries(dicts, module_inst_data);
                }
            }
            Project(projection) => {
                projection.0.elaborate_dictionaries(dicts, module_inst_data);
            }
            Record(nodes) => {
                for node in nodes.iter_mut() {
                    node.elaborate_dictionaries(dicts, module_inst_data);
                }
            }
            FieldAccess(access) => {
                access.0.elaborate_dictionaries(dicts, module_inst_data);
                let field_name = access.1;
                let span = access.0.span;
                let ty_data = access.0.ty.data().clone();
                if let Some(record) = ty_data.as_record() {
                    // Known type, get the index from the type and replace the IR instruction.
                    let index = record
                        .iter()
                        .position(|field| field.0 == field_name)
                        .expect("Field not found, type inference should have failed");
                    let node = mem::replace(
                        &mut access.as_mut().0,
                        Node::new(
                            Immediate(ir::Immediate::new(Value::unit())),
                            Type::unit(),
                            span,
                        ),
                    );
                    self.kind = Project(B::new((node, index)));
                } else if let Some(var) = ty_data.as_variable() {
                    // Variable type, it must be in the type scheme, use the dictionary to lookup local variable.
                    let index = find_field_dict_index(dicts, *var, field_name).expect(
                        "Dictionary for field not found, type inference should have failed",
                    );
                    let node = mem::replace(
                        &mut access.as_mut().0,
                        Node::new(
                            Immediate(ir::Immediate::new(Value::unit())),
                            Type::unit(),
                            span,
                        ),
                    );
                    self.kind = ProjectAt(B::new((node, index)));
                } else {
                    panic!("FieldAccess should have a record or variable type");
                }
            }
            ProjectAt(_) => {
                panic!("ProjectAt should not be present at this stage");
            }
            Array(nodes) => {
                for node in nodes.iter_mut() {
                    node.elaborate_dictionaries(dicts, module_inst_data);
                }
            }
            Index(array, index) => {
                array.elaborate_dictionaries(dicts, module_inst_data);
                index.elaborate_dictionaries(dicts, module_inst_data);
            }
            Case(case) => {
                case.value.elaborate_dictionaries(dicts, module_inst_data);
                for (_, node) in &mut case.alternatives {
                    node.elaborate_dictionaries(dicts, module_inst_data);
                }
                case.default.elaborate_dictionaries(dicts, module_inst_data);
            }
            Iterate(iteration) => {
                iteration
                    .iterator
                    .elaborate_dictionaries(dicts, module_inst_data);
                iteration
                    .body
                    .elaborate_dictionaries(dicts, module_inst_data);
            }
        }
    }
}
