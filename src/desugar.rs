// Copyright 2026 Enlightware GmbH
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
use ustr::{Ustr, ustr};

use crate::{
    Location,
    ast::{
        self, AbstractData, ApplyData, AssignData, DExpr, DModule, DModuleFunction,
        DModuleFunctionArg, DTraitImpl, Expr, ExprKind, FieldAccessData, ForLoopData, IndexData,
        LetData, MatchData, ModuleFunction, ModuleFunctionArg, PExpr, PModule, PModuleFunction,
        PModuleFunctionArg, PTraitImpl, PTypeDef, PTypeSpan, Pattern, PatternKind, PatternVar,
        ProjectData, StructLiteralData, TypeAscriptionData, UnnamedArg, UstrSpan,
    },
    containers::b,
    effects::EffType,
    error::{DuplicatedFieldContext, DuplicatedVariantContext, InternalCompilationError},
    format_string::emit_format_string_ast,
    graph::{find_strongly_connected_components, topological_sort_sccs},
    import_resolver::{ModulesResolver, resolve_imports},
    internal_compilation_error,
    module::{Module, ModuleEnv, ModuleId, Modules},
    mutability::{MutType, MutVal},
    parser_helpers::syn_static_apply,
    std::{array::array_type, math::int_type},
    r#type::{FnArgType, FnType, Type, TypeDefRef},
    type_like::TypeLike,
};

/// A node of a function dependency graph
#[derive(Debug)]
pub struct DepGraphNode(pub Vec<usize>);

impl crate::graph::Node for DepGraphNode {
    type Index = usize;
    fn neighbors(&self) -> impl Iterator<Item = Self::Index> {
        self.0.iter().copied()
    }
}

type FnMap = HashMap<Ustr, usize>;
type FnDeps = HashSet<usize>;

pub type FnSccs = Vec<Vec<usize>>;

impl ast::PFnArgType {
    pub fn desugar(
        &self,
        env: &ModuleEnv<'_>,
        modules_used: &mut HashSet<ModuleId>,
    ) -> Result<FnArgType, InternalCompilationError> {
        let ty = self.ty.0.desugar(self.ty.1, false, env, modules_used)?;
        let mut_ty = match self.mut_ty {
            Some(mut_ty) => match mut_ty {
                ast::PMutType::Mut => MutType::mutable(),
                // if placeholder, always emit variable id 0 that will be replaced by fresh variables in type inference
                ast::PMutType::Infer => MutType::variable_id(0),
            },
            None => MutType::constant(),
        };
        Ok(FnArgType::new(ty, mut_ty))
    }
}

impl ast::PFnType {
    pub fn desugar(
        &self,
        env: &ModuleEnv<'_>,
        modules_used: &mut HashSet<ModuleId>,
    ) -> Result<FnType, InternalCompilationError> {
        let args = self
            .args
            .iter()
            .map(|arg| arg.desugar(env, modules_used))
            .collect::<Result<Vec<_>, _>>()?;
        let ret = self.ret.0.desugar(self.ret.1, false, env, modules_used)?;
        // if this function has generic effects, always emit variable id 0 that will be replaced by fresh variables in type inference
        let effects = if self.effects {
            EffType::single_variable_id(0)
        } else {
            EffType::empty()
        };
        Ok(FnType::new(args, ret, effects))
    }
}

impl ast::PType {
    pub fn desugar(
        &self,
        span: Location,
        in_ty_def: bool,
        env: &ModuleEnv<'_>,
        modules_used: &mut HashSet<ModuleId>,
    ) -> Result<Type, InternalCompilationError> {
        use ast::PType::*;
        Ok(match self {
            Never => Type::never(),
            Unit => Type::unit(),
            Resolved(ty) => *ty,
            Infer => Type::variable_id(0), // always emit variable id 0 that will be replaced by fresh variables in type inference
            Path(path) => {
                if let Some((module_id, ty)) = env.type_alias_type_with_module(path)? {
                    if let Some(module_id) = module_id {
                        modules_used.insert(module_id);
                    }
                    ty
                } else if let Some((module_id, ty)) = env.type_def_type_with_module(path)? {
                    if let Some(module_id) = module_id {
                        modules_used.insert(module_id);
                    }
                    ty
                } else if let [(name, _)] = &path.segments[..] {
                    Type::variant([(*name, Type::unit())])
                } else {
                    return Err(internal_compilation_error!(TypeNotFound(span)));
                }
            }
            Variant(types) => {
                let mut seen = HashMap::new();
                Type::variant(
                    types
                        .iter()
                        .map(|((name, name_span), (ty, ty_span))| {
                            if let Some(prev_span) = seen.get(&name) {
                                Err(internal_compilation_error!(DuplicatedVariant {
                                    first_occurrence: *prev_span,
                                    second_occurrence: *name_span,
                                    ctx_span: span,
                                    ctx: if in_ty_def {
                                        DuplicatedVariantContext::Enum
                                    } else {
                                        DuplicatedVariantContext::Variant
                                    },
                                }))
                            } else {
                                seen.insert(name, *name_span);
                                Ok((*name, ty.desugar(*ty_span, false, env, modules_used)?))
                            }
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                )
            }
            Tuple(elements) => Type::tuple(
                elements
                    .iter()
                    .map(|(ty, span)| ty.desugar(*span, false, env, modules_used))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Record(fields) => {
                let mut seen = HashMap::new();
                Type::record(
                    fields
                        .iter()
                        .map(|((name, name_span), (ty, ty_span))| {
                            if let Some(prev_span) = seen.get(&name) {
                                Err(internal_compilation_error!(DuplicatedField {
                                    first_occurrence: *prev_span,
                                    second_occurrence: *name_span,
                                    constructor_span: span,
                                    ctx: if in_ty_def {
                                        DuplicatedFieldContext::Struct
                                    } else {
                                        DuplicatedFieldContext::Record
                                    },
                                }))
                            } else {
                                seen.insert(name, *name_span);
                                Ok((*name, ty.desugar(*ty_span, false, env, modules_used)?))
                            }
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                )
            }
            Array(array) => array_type(array.0.desugar(array.1, false, env, modules_used)?),
            Function(fn_type) => Type::function_type(fn_type.desugar(env, modules_used)?),
        })
    }
}

impl PTypeDef {
    pub fn desugar(
        &self,
        env: &ModuleEnv<'_>,
        modules_used: &mut HashSet<ModuleId>,
    ) -> Result<TypeDefRef, InternalCompilationError> {
        assert!(self.generic_params.is_empty());
        assert!(self.doc_comments.is_empty());
        let shape = self.shape.desugar(self.span, true, env, modules_used)?;
        Ok(TypeDefRef::new(crate::r#type::TypeDef {
            name: self.name.0,
            param_names: vec![],
            shape,
            span: self.span,
            attributes: self.attributes.clone(),
        }))
    }
}

impl PModuleFunctionArg {
    pub fn desugar(
        self,
        env: &ModuleEnv<'_>,
        modules_used: &mut HashSet<ModuleId>,
    ) -> Result<DModuleFunctionArg, InternalCompilationError> {
        let ty = self
            .ty
            .map(|(mut_ty, ty, span)| {
                Ok((
                    mut_ty.map(|m| match m {
                        ast::PMutType::Mut => MutType::mutable(),
                        // if placeholder, always emit variable id 0 that will be replaced by fresh variables in type inference
                        ast::PMutType::Infer => MutType::variable_id(0),
                    }),
                    ty.desugar(span, false, env, modules_used)?,
                    span,
                ))
            })
            .transpose()?;
        Ok(ModuleFunctionArg {
            name: self.name,
            ty,
        })
    }
}

impl PTraitImpl {
    pub fn desugar(
        self,
        env: &ModuleEnv<'_>,
        modules_used: &mut HashSet<ModuleId>,
    ) -> Result<DTraitImpl, InternalCompilationError> {
        let fn_map = self
            .functions
            .iter()
            .enumerate()
            .map(|(index, func)| (func.name.0, index))
            .collect::<HashMap<_, _>>();
        let functions = self
            .functions
            .into_iter()
            .map(|f| {
                f.desugar(&fn_map, env, modules_used)
                    .map(|(f, _dep_graph)| f)
            })
            .collect::<Result<_, _>>()?;
        let for_ty = self
            .for_tys
            .map(|tys| {
                tys.into_iter()
                    .map(|(ty, span)| {
                        ty.desugar(span, false, env, modules_used)
                            .map(|t| (t, span))
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .transpose()?;
        Ok(DTraitImpl {
            span: self.span,
            trait_name: self.trait_name,
            for_tys: for_ty,
            functions,
        })
    }
}

/// A reference to name of a type, either an alias or a definition, in parsed AST.
enum NamedTypeData {
    Alias(UstrSpan, PTypeSpan),
    Def(PTypeDef),
}
impl NamedTypeData {
    fn collect_refs(
        &self,
        ty_names: &HashMap<Ustr, usize>,
        collected: &mut HashSet<usize>,
    ) -> Result<(), InternalCompilationError> {
        use NamedTypeData::*;
        match self {
            Alias(name, alias) => alias.0.collect_refs(name.0, ty_names, collected),
            Def(def) => def.shape.collect_refs(def.name.0, ty_names, collected),
        }
    }
    fn name(&self) -> Ustr {
        use NamedTypeData::*;
        match self {
            Alias(name, _) => name.0,
            Def(def) => def.name.0,
        }
    }
    fn name_span(&self) -> Location {
        use NamedTypeData::*;
        match self {
            Alias(name, _) => name.1,
            Def(def) => def.name.1,
        }
    }
}

impl PModule {
    /// Desugars a parsed module and resolve its types and write them into output.
    /// Returns a desugared AST and a list of strongly connected components of its
    /// function dependency graph, sorted topologically.
    pub fn desugar(
        self,
        output: &mut Module,
        others: &Modules,
    ) -> Result<(DModule, FnSccs), InternalCompilationError> {
        // Flatten uses from self and check for conflicts with local definitions.
        let local_names = self.own_symbols().collect();
        let resolver = ModulesResolver::new(others);
        resolve_imports(&self.uses, &local_names, &resolver, &mut output.uses)?;

        // Build a map of type names to their location and definitions or aliases.
        // The ty_names map holds indices to the ty_refs vector, which contains the data.
        let (ty_names, ty_refs): (HashMap<_, _>, Vec<_>) = self
            .type_aliases
            .into_iter()
            .map(|alias| (alias.name.0, NamedTypeData::Alias(alias.name, alias.ty)))
            .chain(
                self.type_defs
                    .into_iter()
                    .map(|def| (def.name.0, NamedTypeData::Def(def))),
            )
            .enumerate()
            .map(|(index, (name, ty_data))| ((name, index), ty_data))
            .unzip();

        // Create the dependency graph of the named types in this module.
        let ty_dep_graph = ty_refs
            .iter()
            .map(|ty_ref| {
                let mut collected = HashSet::new();
                ty_ref.collect_refs(&ty_names, &mut collected)?;
                Ok(DepGraphNode(collected.into_iter().collect()))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let sccs = find_strongly_connected_components(&ty_dep_graph);
        for scc in &sccs {
            if scc.len() > 1 {
                // If there are multiple types in the same SCC, we have a cycle.
                // This is currently not allowed in type definitions.
                let ty_ref = &ty_refs[scc[0]];
                return Err(internal_compilation_error!(Unsupported {
                    reason: format!(
                        "Cyclic types are not supported, but `{}` indirectly refers to itself",
                        ty_ref.name()
                    ),
                    span: ty_ref.name_span(),
                }));
            }
        }

        // Build a module environment with the current module and the others.
        let mut env = ModuleEnv::new(output, others);

        // Process types in order of their dependencies and resolve type aliases and type definitions.
        // Directly insert them into the output module once they are resolved.
        let sorted_sccs = topological_sort_sccs(&ty_dep_graph, &sccs);
        let mut modules_used = HashSet::<ModuleId>::new();
        for scc in sorted_sccs.into_iter().rev() {
            assert_eq!(scc.len(), 1);
            let ty_ref = &ty_refs[scc[0]];
            match ty_ref {
                NamedTypeData::Alias(name, alias) => {
                    let ty = alias.0.desugar(alias.1, false, &env, &mut modules_used)?;
                    output.add_type_alias(name.0, ty);
                }
                NamedTypeData::Def(def) => {
                    output.add_type_def(def.name.0, def.desugar(&env, &mut modules_used)?);
                }
            }
            env = ModuleEnv::new(output, others);
        }

        // Desugar functions
        let fn_map = self
            .functions
            .iter()
            .enumerate()
            .map(|(index, func)| (func.name.0, index))
            .collect::<HashMap<_, _>>();
        let (functions, fn_dep_graph): (_, Vec<_>) = process_results(
            self.functions
                .into_iter()
                .map(|f| f.desugar(&fn_map, &env, &mut modules_used)),
            |iter| iter.unzip(),
        )?;
        let sccs = find_strongly_connected_components(&fn_dep_graph);
        let sorted_sccs = topological_sort_sccs(&fn_dep_graph, &sccs);

        // Desugar trait implementations
        let impls = self
            .impls
            .into_iter()
            .map(|i| i.desugar(&env, &mut modules_used))
            .collect::<Result<_, _>>()?;

        // Build result
        output.type_deps.extend(modules_used);
        let module = DModule {
            functions,
            impls,
            type_aliases: vec![],
            type_defs: vec![],
            uses: self.uses,
        };
        Ok((module, sorted_sccs))
    }
}

impl PModuleFunction {
    pub fn desugar(
        self,
        fn_map: &FnMap,
        env: &ModuleEnv<'_>,
        modules_used: &mut HashSet<ModuleId>,
    ) -> Result<(DModuleFunction, DepGraphNode), InternalCompilationError> {
        let locals = self.args.iter().map(|arg| arg.name.0).collect();
        let mut ctx = DesugarCtx::new_with_locals(fn_map, locals, env);
        let body = self.body.desugar(&mut ctx, modules_used)?;
        let args = self
            .args
            .into_iter()
            .map(|arg| arg.desugar(env, modules_used))
            .collect::<Result<Vec<_>, _>>()?;
        // Collect function dependencies
        let ret_ty = self
            .ret_ty
            .map(|(ty, span)| Ok((ty.desugar(span, false, env, modules_used)?, span)))
            .transpose()?;
        let function = ModuleFunction {
            name: self.name,
            args,
            args_span: self.args_span,
            ret_ty,
            body: b(body),
            span: self.span,
            doc: self.doc,
        };
        let deps = DepGraphNode(ctx.fn_deps.into_iter().collect());
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
    /// Module environment, used for desugaring types
    module_env: &'a ModuleEnv<'a>,
}

impl<'a> DesugarCtx<'a> {
    fn new(fn_map: &'a FnMap, module_env: &'a ModuleEnv<'a>) -> Self {
        Self {
            fn_map,
            fn_deps: HashSet::new(),
            locals: Vec::new(),
            module_env,
        }
    }
    fn new_with_locals(
        fn_map: &'a FnMap,
        locals: Vec<Ustr>,
        module_env: &'a ModuleEnv<'a>,
    ) -> Self {
        Self {
            fn_map,
            fn_deps: HashSet::new(),
            locals,
            module_env,
        }
    }
}

impl PExpr {
    /// Desugar without a context, to be used outside modules.
    pub fn desugar_with_empty_ctx(
        self,
        module_env: &ModuleEnv<'_>,
        modules_used: &mut HashSet<ModuleId>,
    ) -> Result<DExpr, InternalCompilationError> {
        let empty_fn_map = HashMap::new();
        let mut ctx = DesugarCtx::new(&empty_fn_map, module_env);
        self.desugar(&mut ctx, modules_used)
    }

    fn desugar(
        self,
        ctx: &mut DesugarCtx,
        modules_used: &mut HashSet<ModuleId>,
    ) -> Result<DExpr, InternalCompilationError> {
        use ExprKind::*;
        let kind = match self.kind {
            Literal(value, ty) => {
                if ty == int_type() {
                    // Convert integer literals to from_int(literal).
                    ExprKind::apply(
                        DExpr::single_identifier(ustr("from_int"), self.span),
                        vec![DExpr::new(ExprKind::literal(value, ty), self.span)],
                        UnnamedArg::All,
                    )
                } else {
                    Literal(value, ty)
                }
            }
            FormattedString(s) => emit_format_string_ast(&s, self.span, &ctx.locals)?,
            Identifier(path) => {
                let is_local = match path.segments.as_slice() {
                    [(name, _)] => ctx.locals.contains(name),
                    _ => false,
                };
                if !is_local {
                    // There is *NOT* a local variable shadowing a function definition.
                    if let [(name, _)] = &path.segments[..]
                        && let Some(index) = ctx.fn_map.get(name)
                    {
                        // This is a known function part of this module.
                        ctx.fn_deps.insert(*index);
                    }
                }
                Identifier(path)
            }
            Let(data) => {
                let LetData {
                    name,
                    mut_val,
                    expr,
                    ty_ascription,
                } = *data;
                let expr = expr.desugar(ctx, modules_used)?;
                // Look inside the type ascription node to see if the type is constant, to be used later for display.
                let ty_ascription = ty_ascription.map(|(span, _)| {
                    let ty = expr
                        .kind
                        .as_type_ascription()
                        .map(|ty_asc| ty_asc.ty)
                        .unwrap_or_else(|| *expr.kind.as_literal().unwrap().1);
                    let is_constant = ty.is_constant();
                    (span, is_constant)
                });
                let result = ExprKind::let_(name, mut_val, expr, ty_ascription);
                ctx.locals.push(name.0);
                result
            }
            Return(expr) => ExprKind::return_(expr.desugar(ctx, modules_used)?),
            Abstract(data) => {
                let AbstractData { args, body } = *data;
                // we swap the locals with the lambda arguments, as we do not capture the outer scope
                let mut other_vars = args.iter().map(|(name, _)| *name).collect::<Vec<_>>();
                mem::swap(&mut other_vars, &mut ctx.locals);
                let body = body.desugar(ctx, modules_used)?;
                let result = ExprKind::abstract_(args, body);
                mem::swap(&mut other_vars, &mut ctx.locals);
                result
            }
            Apply(data) => {
                let ApplyData {
                    func,
                    args,
                    unnamed_arg,
                } = *data;
                ExprKind::apply(
                    func.desugar(ctx, modules_used)?,
                    desugar(args, ctx, modules_used)?,
                    unnamed_arg,
                )
            }
            Block(stmts) => {
                let env_size = ctx.locals.len();
                let block = Block(desugar(stmts, ctx, modules_used)?);
                ctx.locals.truncate(env_size);
                block
            }
            Assign(data) => {
                let AssignData {
                    place,
                    sign_span: sign_loc,
                    value,
                } = *data;
                let place = place.desugar(ctx, modules_used)?;
                let value = value.desugar(ctx, modules_used)?;
                if let Some(index) = place.kind.as_index() {
                    if index.array.kind.is_property_path() {
                        /*
                            Desugar:
                                @scope.property[expr1] = expr2
                            into:
                                {
                                    let mut tmp = @scope.property;
                                    tmp[expr1] = expr2;
                                    @scope.property = tmp;
                                }
                        */
                        let let_stmt = Expr::new(
                            ExprKind::let_(
                                (ustr("tmp"), self.span),
                                MutVal::mutable(),
                                index.array.clone(),
                                None,
                            ),
                            self.span,
                        );
                        let index_expr = Expr::new(
                            ExprKind::index(
                                Expr::single_identifier(ustr("tmp"), self.span),
                                index.index.clone(),
                            ),
                            self.span,
                        );
                        let assign_tmp_stmt =
                            Expr::new(ExprKind::assign(index_expr, sign_loc, value), self.span);
                        let assign_back_stmt = Expr::new(
                            ExprKind::assign(
                                index.array.clone(),
                                sign_loc,
                                Expr::single_identifier(ustr("tmp"), self.span),
                            ),
                            self.span,
                        );
                        return Ok(Expr::new(
                            Block(vec![let_stmt, assign_tmp_stmt, assign_back_stmt]),
                            self.span,
                        ));
                    }
                }
                ExprKind::assign(place, sign_loc, value)
            }
            PropertyPath(data) => PropertyPath(data),
            Tuple(elements) => Tuple(desugar(elements, ctx, modules_used)?),
            Project(data) => {
                let ProjectData { expr, index } = *data;
                ExprKind::project(expr.desugar(ctx, modules_used)?, index)
            }
            StructLiteral(data) => {
                let StructLiteralData { path, fields } = *data;
                ExprKind::struct_literal(
                    path,
                    fields
                        .into_iter()
                        .map(|(k, v)| Ok((k, v.desugar(ctx, modules_used)?)))
                        .collect::<Result<Vec<_>, _>>()?,
                )
            }
            Record(elements) => Record(
                elements
                    .into_iter()
                    .map(|(k, v)| Ok((k, v.desugar(ctx, modules_used)?)))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            FieldAccess(data) => {
                let FieldAccessData { expr, name } = *data;
                ExprKind::field_access(expr.desugar(ctx, modules_used)?, name)
            }
            Array(elements) => Array(desugar(elements, ctx, modules_used)?),
            Index(data) => {
                let IndexData { array, index } = *data;
                let index_span = index.span;
                let desugared_index = match index.kind {
                    Literal(value, ty) => DExpr::new(Literal(value, ty), index_span),
                    kind => Expr::new(kind, index_span).desugar(ctx, modules_used)?,
                };
                ExprKind::index(array.desugar(ctx, modules_used)?, desugared_index)
            }
            Match(data) => {
                let MatchData {
                    cond_expr: expr,
                    alternatives,
                    default,
                } = *data;
                ExprKind::match_(
                    expr.desugar(ctx, modules_used)?,
                    alternatives
                        .into_iter()
                        .map(|(pat, expr)| {
                            let env_size = ctx.locals.len();
                            if let Some((_tag, _kind, vars)) = pat.kind.as_variant() {
                                for var in vars {
                                    if let Some(name) = var.as_named() {
                                        ctx.locals.push(name.0);
                                    }
                                }
                            }
                            let expr = expr.desugar(ctx, modules_used)?;
                            ctx.locals.truncate(env_size);
                            Ok((pat, expr))
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                    default.map(|e| e.desugar(ctx, modules_used)).transpose()?,
                )
            }
            ForLoop(for_loop) => {
                let ForLoopData {
                    var_name,
                    iterator,
                    body,
                } = *for_loop;
                let iterator_start_span = iterator.span;
                let body_span: Location = body.span;
                let body_start_span =
                    Location::new(body_span.start(), body_span.start(), body_span.source_id());
                let body_end_span =
                    Location::new(body_span.end(), body_span.end(), body_span.source_id());
                let it_store = Expr::new(
                    ExprKind::let_(
                        (ustr("@it"), iterator_start_span),
                        MutVal::mutable(),
                        iterator.desugar(ctx, modules_used)?,
                        None,
                    ),
                    iterator_start_span,
                );
                let it_next = Expr::new(
                    syn_static_apply(
                        (ustr("next"), body_start_span),
                        vec![Expr::single_identifier(ustr("@it"), body_start_span)],
                    ),
                    body_start_span,
                );
                let it_match = Expr::new(
                    ExprKind::match_(
                        it_next,
                        vec![
                            (
                                Pattern::new(
                                    PatternKind::tuple_variant(
                                        (ustr("Some"), body_start_span),
                                        vec![PatternVar::Named(var_name)],
                                    ),
                                    var_name.1,
                                ),
                                {
                                    let env_size = ctx.locals.len();
                                    ctx.locals.push(var_name.0);
                                    let desugared_body = body.desugar(ctx, modules_used)?;
                                    ctx.locals.truncate(env_size);
                                    desugared_body
                                },
                            ),
                            (
                                Pattern::new(
                                    PatternKind::empty_tuple_variant((ustr("None"), body_end_span)),
                                    body_end_span,
                                ),
                                Expr::new(ExprKind::soft_break(), body_end_span),
                            ),
                        ],
                        None,
                    ),
                    body_span,
                );
                let loop_expr = Expr::new(ExprKind::loop_(it_match), body_span);
                Block(vec![it_store, loop_expr])
            }
            Loop(body) => ExprKind::loop_(body.desugar(ctx, modules_used)?),
            SoftBreak => SoftBreak,
            TypeAscription(data) => {
                let TypeAscriptionData { expr, ty, span } = *data;
                let ty = ty.desugar(span, false, ctx.module_env, modules_used)?;
                if let Some((value, lit_ty)) = expr.kind.as_literal() {
                    // If the expression is a literal and the type of the literal matches
                    // the type we want to ascribe, we can just emit the literal.
                    if *lit_ty == ty {
                        Literal(value.clone(), *lit_ty)
                    } else {
                        // Otherwise, we need to emit a type ascription node.
                        ExprKind::type_ascription(expr.desugar(ctx, modules_used)?, ty, span)
                    }
                } else {
                    // Otherwise, we need to emit a type ascription node.
                    ExprKind::type_ascription(expr.desugar(ctx, modules_used)?, ty, span)
                }
            }
            Error => Error,
        };
        Ok(DExpr {
            kind,
            span: self.span,
        })
    }
}

fn desugar(
    args: Vec<PExpr>,
    ctx: &mut DesugarCtx,
    modules_used: &mut HashSet<ModuleId>,
) -> Result<Vec<DExpr>, InternalCompilationError> {
    args.into_iter()
        .map(|arg| PExpr::desugar(arg, ctx, modules_used))
        .collect()
}
