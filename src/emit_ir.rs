use std::{cell::RefCell, rc::Rc};

use crate::{
    ast::{self, *},
    containers::{SVec2, B},
    function::{FunctionDescription, FunctionDescriptionRc, FunctionRef, ScriptFunction},
    ir,
    module::{Module, Modules},
    r#type::{FnType, Type},
    type_inference::TypingEnv,
    value::Value,
};
use ustr::Ustr;

#[derive(Clone, Copy, Debug)]
pub struct Local {
    name: Ustr,
    mutable: bool,
}
impl Local {
    fn new(name: Ustr, mutable: bool) -> Self {
        Self { name, mutable }
    }
}

pub type EmissionError = String;

#[derive(Clone, Copy)]
pub struct ModuleEnv<'m> {
    current: &'m Module,
    others: &'m Modules,
}
impl<'m> ModuleEnv<'m> {
    pub fn new(current: &'m Module, others: &'m Modules) -> Self {
        Self { current, others }
    }
}

pub struct EmitIrEnv<'m> {
    locals: Vec<Local>,
    modules: ModuleEnv<'m>,
}

impl<'m> EmitIrEnv<'m> {
    pub fn with_module_env(modules: ModuleEnv<'m>) -> Self {
        Self {
            locals: vec![],
            modules,
        }
    }

    pub fn new(locals: Vec<Local>, modules: ModuleEnv<'m>) -> Self {
        Self { locals, modules }
    }

    pub fn get_locals_and_drop(self) -> Vec<Local> {
        self.locals
    }

    fn new_function(args: &[Ustr], modules: ModuleEnv<'m>) -> Self {
        let locals = args.iter().map(|name| Local::new(*name, false)).collect();
        EmitIrEnv { locals, modules }
    }

    /// Emit IR for the given module
    pub fn emit_module(
        source: &ast::Module,
        others: &Modules,
        merge_with: Option<Module>,
    ) -> Result<Module, EmissionError> {
        let mut output = merge_with.unwrap_or_default();
        let mut ty_inf = TypingEnv::default();
        // first pass, populate the function table and allocate fresh mono type variables
        for (name, args, _body) in &source.functions {
            let args_ty: Vec<_> = args
                .iter()
                .map(|_| Type::variable(ty_inf.fresh_type_var()))
                .collect();
            let f_descr = FunctionDescription {
                ty: FnType::new_by_val(&args_ty, Type::variable(ty_inf.fresh_type_var())),
                code: B::new(ScriptFunction::new(ir::Node::Literal(Value::unit()))), // fake code
            };
            output
                .functions
                .insert(*name, Rc::new(RefCell::new(f_descr)));
        }

        // second pass, infer types
        // TODO: add type inference

        // third pass, generate the functions bodies
        for (name, args, body) in &source.functions {
            let mut env = EmitIrEnv::new_function(args, ModuleEnv::new(&output, others));
            let code = env.emit_expr(body)?;
            let descr = output.functions.get_mut(name).unwrap();
            descr.borrow_mut().code = B::new(ScriptFunction::new(code));
        }

        // substitute the remaining mono type variables as poly type variales in function definitions
        Ok(output)
    }

    /// Emit IR for an expression
    pub fn emit_expr(&mut self, expr: &Expr) -> Result<ir::Node, EmissionError> {
        use ir::Node as N;
        use ExprKind::*;
        match &expr.kind {
            Literal(value) => Ok(N::Literal(value.clone())),
            Variable(name) => Ok(N::EnvLoad(self.get_variable_index(*name)?)),
            LetVar(name, mutable, expr) => {
                let store_node = N::EnvStore(B::new(self.emit_expr(expr)?));
                // Note: to allow recursion, we would env.insert before the store_node
                self.locals.push(Local::new(*name, *mutable));
                Ok(store_node)
            }
            Abstract(args, body) => {
                // Setup a new environment for the function
                // TODO: capture the outer environment
                let mut f_env = EmitIrEnv::new_function(args, self.modules);
                let f_body = f_env.emit_expr(body)?;
                // FIXME: this is a hack as we need to provide types but we do not do typing yet
                let args_ty: Vec<_> = args
                    .iter()
                    .enumerate()
                    .map(|(i, _)| Type::variable_id(i as u32))
                    .collect();
                let f_descr = FunctionDescription {
                    ty: FnType::new_by_val(&args_ty, Type::variable_id(args_ty.len() as u32)),
                    code: B::new(ScriptFunction::new(f_body)),
                };
                Ok(N::Literal(Value::function(f_descr)))
            }
            Apply(function, args) => {
                // do we have a global function?
                if let Variable(name) = function.kind {
                    if !self.has_variable_name(name) {
                        return self.emit_static_apply(name, args);
                    }
                }
                // no, we emit code to evaluate function
                let function = self.emit_expr(function)?;
                let arguments = self.emit_irs(args)?;
                Ok(N::Apply(B::new(ir::Application {
                    function,
                    arguments,
                })))
            }
            StaticApply(name, args) => self.emit_static_apply(*name, args),
            Block(exprs) => {
                let env_size = self.locals.len();
                let nodes = exprs
                    .iter()
                    .map(|expr| self.emit_expr(expr))
                    .collect::<Result<_, _>>()?;
                self.locals.truncate(env_size);
                Ok(N::BlockExpr(B::new(nodes)))
            }
            Assign(place, expr) => {
                let value = self.emit_expr(expr)?;
                let place = self.emit_expr(place)?;
                Ok(N::Assign(B::new(ir::Assignment { place, value })))
            }
            Tuple(exprs) => {
                let exprs = self.emit_irs(exprs)?;
                Ok(N::Tuple(B::new(SVec2::from_vec(exprs))))
            }
            Project(expr, index) => {
                let expr = self.emit_expr(expr)?;
                Ok(N::Project(B::new((expr, *index))))
            }
            Array(exprs) => {
                let exprs = self.emit_irs(exprs)?;
                Ok(N::Array(B::new(SVec2::from_vec(exprs))))
            }
            Index(array, index) => {
                let array = self.emit_expr(array)?;
                let index = self.emit_expr(index)?;
                Ok(N::Index(B::new(array), B::new(index)))
            }
            Match(expr, alternatives, default) => {
                let value = self.emit_expr(expr)?;
                // convert optional default to mandatory one
                if let Some(default) = default {
                    let default = self.emit_expr(default)?;
                    let alternatives = self.emit_patterns(alternatives)?;
                    Ok(N::Case(B::new(ir::Case {
                        value,
                        alternatives,
                        default,
                    })))
                } else if alternatives.is_empty() {
                    panic!("empty match without default");
                } else {
                    let default = self.emit_expr(&alternatives.last().unwrap().1)?;
                    let alternatives =
                        self.emit_patterns(&alternatives[0..alternatives.len() - 1])?;
                    Ok(N::Case(B::new(ir::Case {
                        value,
                        alternatives,
                        default,
                    })))
                }
            }
            Error(msg) => {
                panic!("attempted to emit IR for error node: {msg}");
            }
        }
    }

    fn emit_static_apply(&mut self, name: Ustr, args: &[Expr]) -> Result<ir::Node, EmissionError> {
        let function = FunctionRef::new_weak(&self.get_function(name)?);
        let arguments = self.emit_irs(args)?;
        Ok(ir::Node::StaticApply(B::new(ir::StaticApplication {
            function,
            arguments,
        })))
    }

    fn emit_irs(&mut self, exprs: &[Expr]) -> Result<Vec<ir::Node>, EmissionError> {
        exprs.iter().map(|expr| self.emit_expr(expr)).collect()
    }

    fn emit_patterns<U: std::iter::FromIterator<(Value, ir::Node)>>(
        &mut self,
        pairs: &[(Expr, Expr)],
    ) -> Result<U, EmissionError> {
        pairs
            .iter()
            .map(|(pattern, expr)| {
                if let ExprKind::Literal(literal) = &pattern.kind {
                    Ok((literal.clone(), self.emit_expr(expr)?))
                } else {
                    Err("Expect literal, found another expr kind".to_string())
                }
            })
            .collect::<Result<U, EmissionError>>()
    }

    fn has_variable_name(&self, name: Ustr) -> bool {
        self.locals.iter().any(|local| local.name == name)
    }

    fn get_variable_index(&self, name: Ustr) -> Result<usize, EmissionError> {
        self.locals
            .iter()
            .rev()
            .position(|local| local.name == name)
            .map(|index| self.locals.len() - 1 - index)
            .ok_or_else(|| format!("variable {name} not found"))
    }

    fn get_function(&self, name: Ustr) -> Result<FunctionDescriptionRc, EmissionError> {
        // TODO: add support for looking up in other modules with qualified path
        self.modules
            .current
            .get_function(name, self.modules.others)
            .ok_or_else(|| format!("function {name} not found"))
    }
}
