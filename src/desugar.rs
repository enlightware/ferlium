use itertools::process_results;
use std::{
    collections::{HashMap, HashSet},
    mem,
};
use ustr::Ustr;

use crate::{
    ast::{
        DExpr, DModule, DModuleFunction, ExprKind, FnDepGraphNode, Module, ModuleFunction, PExpr,
        PModule, PModuleFunction,
    },
    containers::B,
    error::InternalCompilationError,
    format_string::emit_format_string_ast,
    graph::{find_strongly_connected_components, topological_sort_sccs},
};

type FnMap = HashMap<Ustr, usize>;
type FnDeps = HashSet<usize>;

pub type FnSccs = Vec<Vec<usize>>;

impl PModule {
    /// Desugar a module parsed AST into a desugared AST and a list of strongly
    /// connected components of its function dependency graph, sorted topologically.
    pub fn desugar(self) -> Result<(DModule, FnSccs), InternalCompilationError> {
        let fn_map = self
            .functions
            .iter()
            .enumerate()
            .map(|(index, func)| (func.name.0, index))
            .collect::<HashMap<_, _>>();
        let (functions, dependency_graph): (_, Vec<_>) = process_results(
            self.functions.into_iter().map(|f| f.desugar(&fn_map)),
            |iter| iter.unzip(),
        )?;
        let sccs = find_strongly_connected_components(&dependency_graph);
        let sorted_sccs = topological_sort_sccs(&dependency_graph, &sccs);
        let module = Module {
            functions,
            types: self.types,
        };
        Ok((module, sorted_sccs))
    }
}

impl PModuleFunction {
    pub fn desugar(
        self,
        fn_map: &FnMap,
    ) -> Result<(DModuleFunction, FnDepGraphNode), InternalCompilationError> {
        let locals = self.args.iter().map(|(name, _)| *name).collect();
        let mut ctx = DesugarCtx::new_with_locals(fn_map, locals);
        let body = self.body.desugar(&mut ctx)?;
        let function = ModuleFunction {
            name: self.name,
            args: self.args,
            args_span: self.args_span,
            body: B::new(body),
            span: self.span,
            doc: self.doc,
        };
        let deps = FnDepGraphNode(ctx.fn_deps.into_iter().collect());
        Ok((function, deps))
    }
}

/// Context used for desugaring and collecting function dependencies
#[derive(Debug)]
struct DesugarCtx<'a> {
    /// All functions in the current module, set empty if we are not in a module
    fn_map: &'a FnMap,
    /// Indices from fn_map's keys that are used in this expression
    fn_deps: FnDeps,
    /// Locals for desugaring and function dependencies collection
    locals: Vec<Ustr>,
}

impl<'a> DesugarCtx<'a> {
    fn new(fn_map: &'a FnMap) -> Self {
        Self {
            fn_map,
            fn_deps: HashSet::new(),
            locals: Vec::new(),
        }
    }
    fn new_with_locals(fn_map: &'a FnMap, locals: Vec<Ustr>) -> Self {
        Self {
            fn_map,
            fn_deps: HashSet::new(),
            locals,
        }
    }
}

impl PExpr {
    /// Desugar without a context, to be used outside modules.
    pub fn desugar_with_empty_ctx(self) -> Result<DExpr, InternalCompilationError> {
        let empty_fn_map = HashMap::new();
        let mut ctx = DesugarCtx::new(&empty_fn_map);
        self.desugar(&mut ctx)
    }

    fn desugar(self, ctx: &mut DesugarCtx) -> Result<DExpr, InternalCompilationError> {
        use ExprKind::*;
        let kind = match self.kind {
            Literal(value, ty) => Literal(value, ty),
            FormattedString(s) => emit_format_string_ast(&s, self.span, &ctx.locals)?,
            Identifier(name) => {
                if !ctx.locals.iter().rev().any(|&local| local == name) {
                    // there is *NOT* a local variable shadowing a function definition
                    if let Some(index) = ctx.fn_map.get(&name) {
                        // this is a know function part of this module
                        ctx.fn_deps.insert(*index);
                    }
                }
                Identifier(name)
            }
            Let(name, mut_val, expr) => {
                let expr = Let(name, mut_val, expr.desugar_boxed(ctx)?);
                ctx.locals.push(name.0);
                expr
            }
            Abstract(args, expr) => {
                // we swap the locals with the lambda arguments, as we do not capture the outer scope
                let mut other_vars = args.iter().map(|(name, _)| *name).collect::<Vec<_>>();
                mem::swap(&mut other_vars, &mut ctx.locals);
                let expr = Abstract(args, expr.desugar_boxed(ctx)?);
                mem::swap(&mut other_vars, &mut ctx.locals);
                expr
            }
            Apply(expr, args, synthesized) => {
                Apply(expr.desugar_boxed(ctx)?, desugar(args, ctx)?, synthesized)
            }
            Block(stmts) => {
                let env_size = ctx.locals.len();
                let block = Block(desugar(stmts, ctx)?);
                ctx.locals.truncate(env_size);
                block
            }
            Assign(place, sign_loc, value) => Assign(
                place.desugar_boxed(ctx)?,
                sign_loc,
                value.desugar_boxed(ctx)?,
            ),
            PropertyPath(scope, var) => PropertyPath(scope, var),
            Tuple(elements) => Tuple(desugar(elements, ctx)?),
            Project(expr, index) => Project(expr.desugar_boxed(ctx)?, index),
            Record(elements) => Record(
                elements
                    .into_iter()
                    .map(|(k, v)| Ok((k, v.desugar(ctx)?)))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            FieldAccess(expr, name) => FieldAccess(expr.desugar_boxed(ctx)?, name),
            Array(elements) => Array(desugar(elements, ctx)?),
            Index(array, index) => Index(array.desugar_boxed(ctx)?, index.desugar_boxed(ctx)?),
            Match(expr, alternatives, default) => Match(
                expr.desugar_boxed(ctx)?,
                alternatives
                    .into_iter()
                    .map(|(pat, expr)| {
                        let env_size = ctx.locals.len();
                        if let Some((_tag, vars)) = pat.kind.as_variant() {
                            for var in vars {
                                ctx.locals.push(var.0);
                            }
                        }
                        let expr = expr.desugar(ctx)?;
                        ctx.locals.truncate(env_size);
                        Ok((pat, expr))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                default.map(|e| e.desugar_boxed(ctx)).transpose()?,
            ),
            ForLoop(var, iterator, body) => {
                ForLoop(var, iterator.desugar_boxed(ctx)?, body.desugar_boxed(ctx)?)
            }
            Error => Error,
        };
        Ok(DExpr {
            kind,
            span: self.span,
        })
    }

    fn desugar_boxed(self, ctx: &mut DesugarCtx) -> Result<B<DExpr>, InternalCompilationError> {
        self.desugar(ctx).map(B::new)
    }
}

fn desugar(args: Vec<PExpr>, ctx: &mut DesugarCtx) -> Result<Vec<DExpr>, InternalCompilationError> {
    args.into_iter()
        .map(|arg| PExpr::desugar(arg, ctx))
        .collect()
}
