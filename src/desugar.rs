// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use itertools::process_results;
use std::mem;

use crate::{FxHashMap, FxHashSet, Modules};
use ustr::{Ustr, ustr};

use crate::{
    Location,
    ast::{
        self, AbstractData, ApplyData, AssignData, DExpr, DExprArena, DExprId, DLetPattern,
        DModule, DModuleFunction, DModuleFunctionArg, DTraitImpl, ExprId, ExprKind,
        FieldAccessData, ForLoopData, IndexData, LetData, LetPatternKind, LetRecordPatternField,
        MatchData, ModuleFunction, ModuleFunctionArg, PExprArena, PLetPattern as LetPattern,
        PModule, PModuleFunction, PModuleFunctionArg, PTraitImpl, PTypeDef, PTypeSpan, Parsed,
        Pattern, PatternConstraintKind, PatternKind, PatternVar, ProjectData, StructLiteralData,
        TypeAscriptionData, UnnamedArg, UstrSpan,
    },
    containers::b,
    effects::EffType,
    error::{
        DuplicatedFieldContext, DuplicatedVariantContext, InternalCompilationError,
        WhatIsNotAProductType, WhichProductTypeIsNot,
    },
    format_string::emit_format_string_ast,
    graph::{find_strongly_connected_components, topological_sort_sccs},
    import_resolver::{ModulesResolver, resolve_imports},
    internal_compilation_error,
    module::{Module, ModuleEnv, ModuleId, TypeDefLookupResult},
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

type FnMap = FxHashMap<Ustr, usize>;
type FnDeps = FxHashSet<usize>;

pub type FnSccs = Vec<Vec<usize>>;

impl ast::PFnArgType {
    pub fn desugar(
        &self,
        env: &ModuleEnv<'_>,
        modules_used: &mut FxHashSet<ModuleId>,
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
        modules_used: &mut FxHashSet<ModuleId>,
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
        modules_used: &mut FxHashSet<ModuleId>,
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
                let mut seen = FxHashMap::default();
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
                let mut seen = FxHashMap::default();
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
        modules_used: &mut FxHashSet<ModuleId>,
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
        modules_used: &mut FxHashSet<ModuleId>,
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
        parsed_arena: &PExprArena,
        desugared_arena: &mut DExprArena,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<DTraitImpl, InternalCompilationError> {
        let fn_map = self
            .functions
            .iter()
            .enumerate()
            .map(|(index, func)| (func.name.0, index))
            .collect::<FxHashMap<_, _>>();
        let functions = self
            .functions
            .into_iter()
            .map(|f| {
                f.desugar(&fn_map, env, parsed_arena, desugared_arena, modules_used)
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
        ty_names: &FxHashMap<Ustr, usize>,
        collected: &mut FxHashSet<usize>,
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
    /// Returns a desugared AST, the desugared expression arena, and a list of
    /// strongly connected components of its function dependency graph, sorted topologically.
    pub fn desugar(
        self,
        output: &mut Module,
        others: &Modules,
        parsed_arena: &PExprArena,
    ) -> Result<(DModule, DExprArena, FnSccs), InternalCompilationError> {
        // Flatten uses from self and check for conflicts with local definitions.
        let local_names = self.own_symbols().collect();
        let resolver = ModulesResolver::new(others);
        resolve_imports(&self.uses, &local_names, &resolver, &mut output.uses)?;

        // Build a map of type names to their location and definitions or aliases.
        // The ty_names map holds indices to the ty_refs vector, which contains the data.
        let (ty_names, ty_refs): (FxHashMap<_, _>, Vec<_>) = self
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
                let mut collected = FxHashSet::default();
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
        let mut modules_used = FxHashSet::<ModuleId>::default();
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
            .collect::<FxHashMap<_, _>>();
        let mut desugared_arena = new_desugared_arena_sized_from_parsed_arena(parsed_arena);
        let (functions, fn_dep_graph): (_, Vec<_>) = process_results(
            self.functions.into_iter().map(|f| {
                f.desugar(
                    &fn_map,
                    &env,
                    parsed_arena,
                    &mut desugared_arena,
                    &mut modules_used,
                )
            }),
            |iter| iter.unzip(),
        )?;
        let sccs = find_strongly_connected_components(&fn_dep_graph);
        let sorted_sccs = topological_sort_sccs(&fn_dep_graph, &sccs);

        // Desugar trait implementations
        let impls = self
            .impls
            .into_iter()
            .map(|i| i.desugar(&env, parsed_arena, &mut desugared_arena, &mut modules_used))
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
        Ok((module, desugared_arena, sorted_sccs))
    }
}

impl PModuleFunction {
    pub fn desugar(
        self,
        fn_map: &FnMap,
        env: &ModuleEnv<'_>,
        parsed_arena: &PExprArena,
        desugared_arena: &mut DExprArena,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<(DModuleFunction, DepGraphNode), InternalCompilationError> {
        let locals = self.args.iter().map(|arg| arg.name.0).collect();
        let mut ctx = DesugarCtx::new_with_locals(fn_map, locals, env);
        let body = desugar(
            self.body,
            &mut ctx,
            parsed_arena,
            desugared_arena,
            modules_used,
        )?;
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
            body,
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
    /// Counter for generated local names
    temp_counter: usize,
}

impl<'a> DesugarCtx<'a> {
    fn new(fn_map: &'a FnMap, module_env: &'a ModuleEnv<'a>) -> Self {
        Self {
            fn_map,
            fn_deps: FxHashSet::default(),
            locals: Vec::new(),
            module_env,
            temp_counter: 0,
        }
    }
    fn new_with_locals(
        fn_map: &'a FnMap,
        locals: Vec<Ustr>,
        module_env: &'a ModuleEnv<'a>,
    ) -> Self {
        Self {
            fn_map,
            fn_deps: FxHashSet::default(),
            locals,
            module_env,
            temp_counter: 0,
        }
    }

    fn fresh_generated_local(&mut self, prefix: &str, span: Location) -> UstrSpan {
        let name = ustr(&format!("@{prefix}{}", self.temp_counter));
        self.temp_counter += 1;
        (name, span)
    }
}

/// Desugar a single parsed expression ID into a desugared expression ID.
/// Reads from `parsed_arena` and writes into `desugared_arena`.
pub fn desugar_expr_with_empty_ctx(
    id: ExprId<Parsed>,
    parsed_arena: &PExprArena,
    module_env: &ModuleEnv<'_>,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<(DExprId, DExprArena), InternalCompilationError> {
    let empty_fn_map = FxHashMap::default();
    let mut ctx = DesugarCtx::new(&empty_fn_map, module_env);
    let mut desugared_arena = new_desugared_arena_sized_from_parsed_arena(parsed_arena);
    let result = desugar(
        id,
        &mut ctx,
        parsed_arena,
        &mut desugared_arena,
        modules_used,
    )?;
    Ok((result, desugared_arena))
}

/// Desugar an expression
fn desugar(
    id: ExprId<Parsed>,
    ctx: &mut DesugarCtx,
    parsed_arena: &PExprArena,
    desugared_arena: &mut DExprArena,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<DExprId, InternalCompilationError> {
    use ExprKind::*;
    // Clone the kind and span so we can release the borrow on parsed_arena
    let expr_span = parsed_arena[id].span;
    let expr_kind = parsed_arena[id].kind.clone();
    let kind = match expr_kind {
        Literal(value, ty) => {
            if ty == int_type() {
                // Convert integer literals to from_int(literal).
                let lit =
                    desugared_arena.alloc(DExpr::new(ExprKind::literal(value, ty), expr_span));
                let from_int =
                    desugared_arena.alloc(DExpr::single_identifier(ustr("from_int"), expr_span));
                ExprKind::apply(from_int, vec![lit], UnnamedArg::All)
            } else {
                Literal(value, ty)
            }
        }
        FormattedString(s) => emit_format_string_ast(&s, expr_span, &ctx.locals, desugared_arena)?,
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
            let statements = desugar_let_exprs(
                *data,
                expr_span,
                ctx,
                parsed_arena,
                desugared_arena,
                modules_used,
            )?;
            return Ok(if let [stmt] = statements.as_slice() {
                *stmt
            } else {
                desugared_arena.alloc(DExpr::new(Block(statements), expr_span))
            });
        }
        Return(expr) => ExprKind::return_(desugar(
            expr,
            ctx,
            parsed_arena,
            desugared_arena,
            modules_used,
        )?),
        Abstract(data) => {
            let AbstractData { args, body } = *data;
            // we swap the locals with the lambda arguments, as we do not capture the outer scope
            let mut other_vars = args.iter().map(|(name, _)| *name).collect::<Vec<_>>();
            mem::swap(&mut other_vars, &mut ctx.locals);
            let body = desugar(body, ctx, parsed_arena, desugared_arena, modules_used)?;
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
                desugar(func, ctx, parsed_arena, desugared_arena, modules_used)?,
                desugar_exprs(args, ctx, parsed_arena, desugared_arena, modules_used)?,
                unnamed_arg,
            )
        }
        Block(stmts) => {
            let env_size = ctx.locals.len();
            let block = Block(desugar_block_exprs(
                stmts,
                ctx,
                parsed_arena,
                desugared_arena,
                modules_used,
            )?);
            ctx.locals.truncate(env_size);
            block
        }
        Assign(data) => {
            let AssignData {
                place,
                sign_span,
                value,
            } = *data;
            let place = desugar(place, ctx, parsed_arena, desugared_arena, modules_used)?;
            let value = desugar(value, ctx, parsed_arena, desugared_arena, modules_used)?;
            let index_data = desugared_arena[place].kind.as_index().cloned();
            if let Some(index) = index_data {
                if desugared_arena[index.array].kind.is_property_path() {
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
                    let let_stmt = desugared_arena.alloc(DExpr::new(
                        ExprKind::let_(
                            DLetPattern::binding((ustr("tmp"), expr_span), MutVal::mutable()),
                            index.array,
                            None,
                        ),
                        expr_span,
                    ));
                    let tmp_expr =
                        desugared_arena.alloc(DExpr::single_identifier(ustr("tmp"), expr_span));
                    let index_expr = desugared_arena.alloc(DExpr::new(
                        ExprKind::index(tmp_expr, index.index),
                        expr_span,
                    ));
                    let assign_tmp_stmt = desugared_arena.alloc(DExpr::new(
                        ExprKind::assign(index_expr, sign_span, value),
                        expr_span,
                    ));
                    let assign_back_stmt = desugared_arena.alloc(DExpr::new(
                        ExprKind::assign(index.array, sign_span, tmp_expr),
                        expr_span,
                    ));
                    return Ok(desugared_arena.alloc(DExpr::new(
                        Block(vec![let_stmt, assign_tmp_stmt, assign_back_stmt]),
                        expr_span,
                    )));
                }
            }
            ExprKind::assign(place, sign_span, value)
        }
        PropertyPath(data) => PropertyPath(data),
        Tuple(elements) => Tuple(desugar_exprs(
            elements,
            ctx,
            parsed_arena,
            desugared_arena,
            modules_used,
        )?),
        Project(data) => {
            let ProjectData { expr, index } = *data;
            ExprKind::project(
                desugar(expr, ctx, parsed_arena, desugared_arena, modules_used)?,
                index,
            )
        }
        StructLiteral(data) => {
            let StructLiteralData { path, fields } = *data;
            ExprKind::struct_literal(
                path,
                fields
                    .into_iter()
                    .map(|(k, v)| {
                        Ok((
                            k,
                            desugar(v, ctx, parsed_arena, desugared_arena, modules_used)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            )
        }
        Record(elements) => Record(
            elements
                .into_iter()
                .map(|(k, v)| {
                    Ok((
                        k,
                        desugar(v, ctx, parsed_arena, desugared_arena, modules_used)?,
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?,
        ),
        FieldAccess(data) => {
            let FieldAccessData { expr, name } = *data;
            ExprKind::field_access(
                desugar(expr, ctx, parsed_arena, desugared_arena, modules_used)?,
                name,
            )
        }
        Array(elements) => Array(desugar_exprs(
            elements,
            ctx,
            parsed_arena,
            desugared_arena,
            modules_used,
        )?),
        Index(data) => {
            let IndexData { array, index } = data;
            // Check if the index is a literal directly, to avoid re-desugaring
            let index_kind = parsed_arena[index].kind.clone();
            let index_span = parsed_arena[index].span;
            let desugared_index = match index_kind {
                // To avoid generating from_int for array access, we process literals directly here.
                Literal(value, ty) => {
                    desugared_arena.alloc(DExpr::new(Literal(value, ty), index_span))
                }
                _ => desugar(index, ctx, parsed_arena, desugared_arena, modules_used)?,
            };
            ExprKind::index(
                desugar(array, ctx, parsed_arena, desugared_arena, modules_used)?,
                desugared_index,
            )
        }
        Match(data) => {
            let MatchData {
                cond_expr: expr,
                alternatives,
                default,
            } = *data;
            ExprKind::match_(
                desugar(expr, ctx, parsed_arena, desugared_arena, modules_used)?,
                alternatives
                    .into_iter()
                    .map(|(pat, expr_id)| {
                        let env_size = ctx.locals.len();
                        if let Some((_tag, _kind, vars)) = pat.kind.as_variant() {
                            for var in vars {
                                if let Some(name) = var.as_named() {
                                    ctx.locals.push(name.0);
                                }
                            }
                        }
                        let expr =
                            desugar(expr_id, ctx, parsed_arena, desugared_arena, modules_used)?;
                        ctx.locals.truncate(env_size);
                        Ok((pat, expr))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                default
                    .map(|e| desugar(e, ctx, parsed_arena, desugared_arena, modules_used))
                    .transpose()?,
            )
        }
        ForLoop(for_loop) => {
            let ForLoopData {
                var_name,
                iterator,
                body,
            } = *for_loop;
            let iterator_start_span = parsed_arena[iterator].span;
            let body_span: Location = parsed_arena[body].span;
            let body_start_span =
                Location::new(body_span.start(), body_span.start(), body_span.source_id());
            let body_end_span =
                Location::new(body_span.end(), body_span.end(), body_span.source_id());
            let desugared_iter =
                desugar(iterator, ctx, parsed_arena, desugared_arena, modules_used)?;
            let it_store = desugared_arena.alloc(DExpr::new(
                ExprKind::let_(
                    DLetPattern::binding((ustr("@it"), iterator_start_span), MutVal::mutable()),
                    desugared_iter,
                    None,
                ),
                iterator_start_span,
            ));
            let it_name =
                desugared_arena.alloc(DExpr::single_identifier(ustr("@it"), body_start_span));
            let it_next = syn_static_apply(
                (ustr("next"), body_start_span),
                vec![it_name],
                desugared_arena,
            );
            let it_next = desugared_arena.alloc(DExpr::new(it_next, body_start_span));
            let desugared_body = {
                let env_size = ctx.locals.len();
                ctx.locals.push(var_name.0);
                let desugared_body =
                    desugar(body, ctx, parsed_arena, desugared_arena, modules_used)?;
                ctx.locals.truncate(env_size);
                desugared_body
            };
            let soft_break =
                desugared_arena.alloc(DExpr::new(ExprKind::soft_break(), body_end_span));
            let it_match = desugared_arena.alloc(DExpr::new(
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
                            desugared_body,
                        ),
                        (
                            Pattern::new(
                                PatternKind::empty_tuple_variant((ustr("None"), body_end_span)),
                                body_end_span,
                            ),
                            soft_break,
                        ),
                    ],
                    None,
                ),
                body_span,
            ));
            let loop_id = desugared_arena.alloc(DExpr::new(ExprKind::loop_(it_match), body_span));
            Block(vec![it_store, loop_id])
        }
        Loop(body) => ExprKind::loop_(desugar(
            body,
            ctx,
            parsed_arena,
            desugared_arena,
            modules_used,
        )?),
        SoftBreak => SoftBreak,
        PatternConstraint(_) => {
            unreachable!("pattern constraints are introduced during desugaring")
        }
        TypeAscription(data) => {
            let TypeAscriptionData { expr, ty, span } = *data;
            let ty = ty.desugar(span, false, ctx.module_env, modules_used)?;
            let expr_node = &parsed_arena[expr];
            if let Some((value, lit_ty)) = expr_node.kind.as_literal() {
                // If the expression is a literal and the type of the literal matches
                // the type we want to ascribe, we can just emit the literal.
                if *lit_ty == ty {
                    Literal(value.clone(), *lit_ty)
                } else {
                    // Otherwise, we need to emit a type ascription node.
                    let desugared_expr =
                        desugar(expr, ctx, parsed_arena, desugared_arena, modules_used)?;
                    ExprKind::type_ascription(desugared_expr, ty, span)
                }
            } else {
                // Otherwise, emit a type ascription node.
                let desugared_expr =
                    desugar(expr, ctx, parsed_arena, desugared_arena, modules_used)?;
                ExprKind::type_ascription(desugared_expr, ty, span)
            }
        }
        Error => Error,
    };
    Ok(desugared_arena.alloc(DExpr::new(kind, expr_span)))
}

fn desugar_exprs(
    ids: Vec<ExprId<Parsed>>,
    ctx: &mut DesugarCtx,
    parsed_arena: &PExprArena,
    desugared_arena: &mut DExprArena,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<Vec<DExprId>, InternalCompilationError> {
    ids.into_iter()
        .map(|id| desugar(id, ctx, parsed_arena, desugared_arena, modules_used))
        .collect()
}

fn completed_let_ty_ascription(
    expr: DExprId,
    span: Option<Location>,
    desugared_arena: &DExprArena,
) -> Option<(Location, bool)> {
    span.map(|span| {
        let ty = match &desugared_arena[expr].kind {
            ExprKind::PatternConstraint(data) => match &desugared_arena[data.expr].kind {
                ExprKind::TypeAscription(data) => data.ty,
                // Desugaring deliberately drops no-op type ascriptions on matching literals.
                ExprKind::Literal(_, ty) => *ty,
                _ => unreachable!(
                    "completed let type ascription without an underlying type ascription node"
                ),
            },
            ExprKind::TypeAscription(data) => data.ty,
            // Desugaring deliberately drops no-op type ascriptions on matching literals.
            ExprKind::Literal(_, ty) => *ty,
            _ => unreachable!("completed let type ascription without a type ascription node"),
        };
        (span, ty.is_constant())
    })
}

fn bind_local_stmt(
    name: UstrSpan,
    mut_val: MutVal,
    expr: DExprId,
    ty_ascription_span: Option<Location>,
    stmt_span: Location,
    ctx: &mut DesugarCtx,
    desugared_arena: &mut DExprArena,
) -> DExprId {
    let ty_ascription = completed_let_ty_ascription(expr, ty_ascription_span, desugared_arena);
    let let_id = desugared_arena.alloc(DExpr::new(
        ExprKind::let_(DLetPattern::binding(name, mut_val), expr, ty_ascription),
        stmt_span,
    ));
    ctx.locals.push(name.0);
    let_id
}

fn pattern_consumes_source(pattern: &LetPattern) -> bool {
    !matches!(pattern.kind, LetPatternKind::Ignore)
}

fn tuple_pattern_source_uses(elements: &[LetPattern]) -> usize {
    elements
        .iter()
        .filter(|pattern| pattern_consumes_source(pattern))
        .count()
}

fn record_pattern_source_uses(fields: &[LetRecordPatternField]) -> usize {
    fields
        .iter()
        .filter(|field| pattern_consumes_source(&field.pattern))
        .count()
}

fn is_replayable_destructuring_source(expr: DExprId, desugared_arena: &DExprArena) -> bool {
    use ExprKind::*;
    match &desugared_arena[expr].kind {
        Identifier(_) | Literal(_, _) => true,
        Project(data) => is_replayable_destructuring_source(data.expr, desugared_arena),
        FieldAccess(data) => is_replayable_destructuring_source(data.expr, desugared_arena),
        PatternConstraint(data) => is_replayable_destructuring_source(data.expr, desugared_arena),
        TypeAscription(data) => is_replayable_destructuring_source(data.expr, desugared_arena),
        _ => false,
    }
}

fn maybe_materialize_destructuring_source(
    source_expr: DExprId,
    source_ty_ascription_span: Option<Location>,
    stmt_span: Location,
    source_uses: usize,
    ctx: &mut DesugarCtx,
    desugared_arena: &mut DExprArena,
) -> (DExprId, Vec<DExprId>) {
    if source_uses <= 1 || is_replayable_destructuring_source(source_expr, desugared_arena) {
        return (source_expr, Vec::new());
    }

    let temp_name = ctx.fresh_generated_local("destructure", desugared_arena[source_expr].span);
    let temp_stmt = bind_local_stmt(
        temp_name,
        MutVal::constant(),
        source_expr,
        source_ty_ascription_span,
        stmt_span,
        ctx,
        desugared_arena,
    );
    let temp_expr = desugared_arena.alloc(DExpr::single_identifier(temp_name.0, temp_name.1));
    (temp_expr, vec![temp_stmt])
}

fn collect_let_pattern_bindings(
    pattern: &LetPattern,
    root_span: Location,
    seen_bindings: &mut FxHashMap<Ustr, Location>,
) -> Result<(), InternalCompilationError> {
    use LetPatternKind::*;
    match &pattern.kind {
        Binding { name, .. } => {
            if let Some(first_occurrence) = seen_bindings.insert(name.0, name.1) {
                return Err(internal_compilation_error!(
                    IdentifierBoundMoreThanOnceInAPattern {
                        first_occurrence,
                        second_occurrence: name.1,
                        pattern_span: root_span,
                    }
                ));
            }
        }
        Ignore => {}
        Tuple { elements, .. } => {
            for element in elements {
                collect_let_pattern_bindings(element, root_span, seen_bindings)?;
            }
        }
        Record { fields, .. } => {
            for field in fields {
                collect_let_pattern_bindings(&field.pattern, root_span, seen_bindings)?;
            }
        }
    }
    Ok(())
}

fn ensure_unique_let_pattern_bindings(
    pattern: &LetPattern,
) -> Result<(), InternalCompilationError> {
    let mut seen_bindings = FxHashMap::default();
    collect_let_pattern_bindings(pattern, pattern.span, &mut seen_bindings)
}

fn sort_record_pattern_fields(
    fields: &[LetRecordPatternField],
    ctx_span: Location,
    ctx: DuplicatedFieldContext,
) -> Result<Vec<&LetRecordPatternField>, InternalCompilationError> {
    let mut seen_fields = FxHashMap::default();
    for field in fields {
        if let Some(first_occurrence) = seen_fields.insert(field.name.0, field.name.1) {
            return Err(internal_compilation_error!(DuplicatedField {
                first_occurrence,
                second_occurrence: field.name.1,
                constructor_span: ctx_span,
                ctx,
            }));
        }
    }

    let mut sorted_fields = fields.iter().collect::<Vec<_>>();
    sorted_fields.sort_by_key(|field| field.name.0);
    Ok(sorted_fields)
}

fn resolve_struct_pattern_type(
    path: &ast::Path,
    ctx: &DesugarCtx,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<TypeDefRef, InternalCompilationError> {
    let path_span = path.span().unwrap();
    match ctx.module_env.type_def_for_construction(path)? {
        Some((module_id, TypeDefLookupResult::Struct(type_def))) => {
            if let Some(module_id) = module_id {
                modules_used.insert(module_id);
            }
            Ok(type_def)
        }
        Some((_, TypeDefLookupResult::Enum(_, tag, _))) => {
            Err(internal_compilation_error!(Unsupported {
                span: path_span,
                reason: format!(
                    "destructuring enum variants like `{tag}` in let bindings is not supported yet"
                ),
            }))
        }
        None => Err(internal_compilation_error!(TypeNotFound(path_span))),
    }
}

fn tuple_pattern_type_constraint(
    path: Option<&ast::Path>,
    pattern_span: Location,
    element_count: usize,
    has_rest: bool,
    ctx: &DesugarCtx,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<Option<(Type, Location)>, InternalCompilationError> {
    if let Some(path) = path {
        let path_span = path.span().unwrap_or(pattern_span);
        let type_def = resolve_struct_pattern_type(path, ctx, modules_used)?;
        let arity = {
            let payload_ty = type_def.shape;
            let payload_data = payload_ty.data();
            let tuple_tys = payload_data.as_tuple().ok_or_else(|| {
                internal_compilation_error!(IsNotCorrectProductType {
                    which: WhichProductTypeIsNot::Tuple,
                    type_def: type_def.clone(),
                    what: WhatIsNotAProductType::Struct,
                    instantiation_span: path_span,
                })
            })?;
            tuple_tys.len()
        };
        if (!has_rest && element_count != arity) || (has_rest && element_count > arity) {
            return Err(internal_compilation_error!(WrongNumberOfArguments {
                expected: arity,
                expected_span: path_span,
                got: element_count,
                got_span: pattern_span,
            }));
        }
        Ok(Some((type_def.as_type(), path_span)))
    } else {
        Ok(None)
    }
}

fn validate_record_struct_pattern(
    type_def: &TypeDefRef,
    sorted_fields: &[&LetRecordPatternField],
    pattern_span: Location,
    has_rest: bool,
) -> Result<(), InternalCompilationError> {
    let shape_data = type_def.shape.data();
    let layout = shape_data.as_record().ok_or_else(|| {
        internal_compilation_error!(IsNotCorrectProductType {
            which: WhichProductTypeIsNot::Record,
            type_def: type_def.clone(),
            what: WhatIsNotAProductType::Struct,
            instantiation_span: pattern_span,
        })
    })?;

    if has_rest {
        for field in sorted_fields {
            if layout
                .binary_search_by_key(&field.name.0, |(name, _)| *name)
                .is_err()
            {
                return Err(internal_compilation_error!(InvalidStructField {
                    type_def: type_def.clone(),
                    field_name: field.name.0,
                    field_span: field.name.1,
                    instantiation_span: pattern_span,
                }));
            }
        }
        return Ok(());
    }

    let layout_size = layout.len();
    let fields_size = sorted_fields.len();
    for (layout_field, field) in layout.iter().zip(sorted_fields.iter()) {
        let layout_field_name = layout_field.0;
        let field_name = field.name.0;
        if layout_field_name < field_name {
            return Err(internal_compilation_error!(MissingStructField {
                type_def: type_def.clone(),
                field_name: layout_field_name,
                instantiation_span: pattern_span,
            }));
        } else if layout_field_name > field_name {
            return Err(internal_compilation_error!(InvalidStructField {
                type_def: type_def.clone(),
                field_name,
                field_span: field.name.1,
                instantiation_span: pattern_span,
            }));
        }
    }

    if layout_size > fields_size {
        return Err(internal_compilation_error!(MissingStructField {
            type_def: type_def.clone(),
            field_name: layout[fields_size].0,
            instantiation_span: pattern_span,
        }));
    }
    if layout_size < fields_size {
        let field = sorted_fields[layout_size];
        return Err(internal_compilation_error!(InvalidStructField {
            type_def: type_def.clone(),
            field_name: field.name.0,
            field_span: field.name.1,
            instantiation_span: pattern_span,
        }));
    }

    Ok(())
}

fn record_pattern_type_constraint(
    path: Option<&ast::Path>,
    pattern_span: Location,
    fields: &[LetRecordPatternField],
    has_rest: bool,
    ctx: &DesugarCtx,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<Option<(Type, Location)>, InternalCompilationError> {
    let record_ctx = if path.is_some() {
        DuplicatedFieldContext::Struct
    } else {
        DuplicatedFieldContext::Record
    };
    let sorted_fields = sort_record_pattern_fields(fields, pattern_span, record_ctx)?;
    if let Some(path) = path {
        let path_span = path.span().unwrap_or(pattern_span);
        let type_def = resolve_struct_pattern_type(path, ctx, modules_used)?;
        validate_record_struct_pattern(&type_def, &sorted_fields, pattern_span, has_rest)?;
        Ok(Some((type_def.as_type(), path_span)))
    } else {
        Ok(None)
    }
}

fn expand_let_pattern(
    pattern: &LetPattern,
    source_expr: DExprId,
    source_ty_ascription_span: Option<Location>,
    stmt_span: Location,
    ctx: &mut DesugarCtx,
    desugared_arena: &mut DExprArena,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<Vec<DExprId>, InternalCompilationError> {
    use LetPatternKind::*;
    match &pattern.kind {
        Binding { name, mut_val } => Ok(vec![bind_local_stmt(
            *name,
            *mut_val,
            source_expr,
            source_ty_ascription_span,
            stmt_span,
            ctx,
            desugared_arena,
        )]),
        Ignore => Ok(Vec::new()),
        Tuple {
            path,
            elements,
            has_rest,
        } => {
            let ty_constraint = tuple_pattern_type_constraint(
                path.as_ref(),
                pattern.span,
                elements.len(),
                *has_rest,
                ctx,
                modules_used,
            )?;
            let (source_expr, ty_ascription_span) =
                if let Some((tuple_ty, tuple_ty_span)) = ty_constraint {
                    let source_expr_span = desugared_arena[source_expr].span;
                    let ascribed_expr = desugared_arena.alloc(DExpr::new(
                        ExprKind::type_ascription(source_expr, tuple_ty, tuple_ty_span),
                        source_expr_span,
                    ));
                    (ascribed_expr, Some(tuple_ty_span))
                } else {
                    let source_expr_span = desugared_arena[source_expr].span;
                    let constrained_expr = desugared_arena.alloc(DExpr::new(
                        ExprKind::PatternConstraint(b(ast::PatternConstraintData::new(
                            source_expr,
                            PatternConstraintKind::ExactTuple(elements.len()),
                            pattern.span,
                        ))),
                        source_expr_span,
                    ));
                    (constrained_expr, source_ty_ascription_span)
                };
            let source_uses = tuple_pattern_source_uses(elements);
            if source_uses == 0 {
                return Ok(vec![source_expr]);
            }
            let (tuple_source, mut statements) = maybe_materialize_destructuring_source(
                source_expr,
                ty_ascription_span,
                stmt_span,
                source_uses,
                ctx,
                desugared_arena,
            );
            for (index, element_pattern) in elements.iter().enumerate() {
                if !pattern_consumes_source(element_pattern) {
                    continue;
                }
                let project_expr = desugared_arena.alloc(DExpr::new(
                    ExprKind::project(tuple_source, (index, element_pattern.span)),
                    element_pattern.span,
                ));
                statements.extend(expand_let_pattern(
                    element_pattern,
                    project_expr,
                    None,
                    stmt_span,
                    ctx,
                    desugared_arena,
                    modules_used,
                )?);
            }
            Ok(statements)
        }
        Record {
            path,
            fields,
            has_rest,
        } => {
            let ty_constraint = record_pattern_type_constraint(
                path.as_ref(),
                pattern.span,
                fields,
                *has_rest,
                ctx,
                modules_used,
            )?;
            let (source_expr, ty_ascription_span) =
                if let Some((record_ty, record_ty_span)) = ty_constraint {
                    let source_expr_span = desugared_arena[source_expr].span;
                    let ascribed_expr = desugared_arena.alloc(DExpr::new(
                        ExprKind::type_ascription(source_expr, record_ty, record_ty_span),
                        source_expr_span,
                    ));
                    (ascribed_expr, Some(record_ty_span))
                } else {
                    (source_expr, source_ty_ascription_span)
                };
            let source_uses = record_pattern_source_uses(fields);
            if source_uses == 0 {
                return Ok(vec![source_expr]);
            }
            let (record_source, mut statements) = maybe_materialize_destructuring_source(
                source_expr,
                ty_ascription_span,
                stmt_span,
                source_uses,
                ctx,
                desugared_arena,
            );
            for field in fields {
                if !pattern_consumes_source(&field.pattern) {
                    continue;
                }
                let field_expr = desugared_arena.alloc(DExpr::new(
                    ExprKind::field_access(record_source, field.name),
                    field.pattern.span,
                ));
                statements.extend(expand_let_pattern(
                    &field.pattern,
                    field_expr,
                    None,
                    stmt_span,
                    ctx,
                    desugared_arena,
                    modules_used,
                )?);
            }
            Ok(statements)
        }
    }
}

fn desugar_let_exprs(
    data: LetData<Parsed>,
    stmt_span: Location,
    ctx: &mut DesugarCtx,
    parsed_arena: &PExprArena,
    desugared_arena: &mut DExprArena,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<Vec<DExprId>, InternalCompilationError> {
    ensure_unique_let_pattern_bindings(&data.pattern)?;
    let expr = desugar(data.expr, ctx, parsed_arena, desugared_arena, modules_used)?;
    let ty_ascription_span = data.ty_ascription.map(|(span, _)| span);
    expand_let_pattern(
        &data.pattern,
        expr,
        ty_ascription_span,
        stmt_span,
        ctx,
        desugared_arena,
        modules_used,
    )
}

fn desugar_block_exprs(
    ids: Vec<ExprId<Parsed>>,
    ctx: &mut DesugarCtx,
    parsed_arena: &PExprArena,
    desugared_arena: &mut DExprArena,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<Vec<DExprId>, InternalCompilationError> {
    let mut out = Vec::new();
    for id in ids {
        let expr_span = parsed_arena[id].span;
        if let Some(data) = parsed_arena[id].kind.as_let() {
            out.extend(desugar_let_exprs(
                *data.clone(),
                expr_span,
                ctx,
                parsed_arena,
                desugared_arena,
                modules_used,
            )?);
        } else {
            out.push(desugar(
                id,
                ctx,
                parsed_arena,
                desugared_arena,
                modules_used,
            )?);
        }
    }
    Ok(out)
}

fn new_desugared_arena_sized_from_parsed_arena(parsed_arena: &PExprArena) -> DExprArena {
    // We estimate we need 20% more nodes due to desugaring.
    let estimated_node_cound = parsed_arena.len() * 12 / 10;
    DExprArena::with_capacity(estimated_node_cound)
}
