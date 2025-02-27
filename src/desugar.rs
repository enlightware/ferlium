// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use itertools::process_results;
use std::{
    collections::{HashMap, HashSet},
    mem,
};
use ustr::{ustr, Ustr};

use crate::{
    ast::{
        DExpr, DModule, DModuleFunction, DTraitImpl, ExprKind, Module, ModuleFunction, PExpr,
        PModule, PModuleFunction, PTraitImpl,
    },
    containers::{b, B},
    error::InternalCompilationError,
    format_string::emit_format_string_ast,
    graph::{find_strongly_connected_components, topological_sort_sccs},
    std::math::int_type,
};

/// A node of a function dependency graph
#[derive(Debug)]
pub struct FnDepGraphNode(pub Vec<usize>);

impl crate::graph::Node for FnDepGraphNode {
    type Index = usize;
    fn neighbors(&self) -> impl Iterator<Item = Self::Index> {
        self.0.iter().copied()
    }
}

type FnMap = HashMap<Ustr, usize>;
type FnDeps = HashSet<usize>;

pub type FnSccs = Vec<Vec<usize>>;

impl PTraitImpl {
    pub fn desugar(self) -> Result<DTraitImpl, InternalCompilationError> {
        let fn_map = self
            .functions
            .iter()
            .enumerate()
            .map(|(index, func)| (func.name.0, index))
            .collect::<HashMap<_, _>>();
        let functions = self
            .functions
            .into_iter()
            .map(|f| f.desugar(&fn_map).map(|(f, _dep_graph)| f))
            .collect::<Result<_, _>>()?;
        Ok(DTraitImpl {
            span: self.span,
            trait_name: self.trait_name,
            functions,
        })
    }
}

impl PModule {
    /// Desugar a module parsed AST into a desugared AST and a list of strongly
    /// connected components of its function dependency graph, sorted topologically.
    pub fn desugar(self) -> Result<(DModule, FnSccs), InternalCompilationError> {
        // Desugar functions
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

        // Desugar trait implementations
        let impls = self
            .impls
            .into_iter()
            .map(|i| i.desugar())
            .collect::<Result<_, _>>()?;

        // Build result
        let module = Module {
            functions,
            impls,
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
        let locals = self.args.iter().map(|arg| arg.0 .0).collect();
        let mut ctx = DesugarCtx::new_with_locals(fn_map, locals);
        let body = self.body.desugar(&mut ctx)?;
        let function = ModuleFunction {
            name: self.name,
            args: self.args,
            args_span: self.args_span,
            ret_ty: self.ret_ty,
            body: b(body),
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
            Literal(value, ty) => {
                if ty == int_type() {
                    // convert integer literals to from_int(literal)
                    Apply(
                        b(DExpr::new(Identifier(ustr("from_int")), self.span)),
                        vec![DExpr::new(Literal(value, ty), self.span)],
                        false,
                    )
                } else {
                    Literal(value, ty)
                }
            }
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
            Let(name, mut_val, expr, ty_ascription) => {
                let expr = Let(name, mut_val, expr.desugar_boxed(ctx)?, ty_ascription);
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
            Index(array, index) => {
                let index = match index.kind {
                    Literal(value, ty) => b(DExpr::new(Literal(value, ty), index.span)),
                    _ => index.desugar_boxed(ctx)?,
                };
                Index(array.desugar_boxed(ctx)?, index)
            }
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
            TypeAscription(expr, ty, span) => TypeAscription(expr.desugar_boxed(ctx)?, ty, span),
            Error => Error,
        };
        Ok(DExpr {
            kind,
            span: self.span,
        })
    }

    fn desugar_boxed(self, ctx: &mut DesugarCtx) -> Result<B<DExpr>, InternalCompilationError> {
        self.desugar(ctx).map(b)
    }
}

fn desugar(args: Vec<PExpr>, ctx: &mut DesugarCtx) -> Result<Vec<DExpr>, InternalCompilationError> {
    args.into_iter()
        .map(|arg| PExpr::desugar(arg, ctx))
        .collect()
}
