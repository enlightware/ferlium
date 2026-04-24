use super::format_string::emit_format_string_ast;
use super::patterns::{desugar_block_exprs, desugar_let_exprs, desugar_pattern_bindings};
use super::*;
use crate::ast::Desugared;
use crate::parser_helpers::ext_b;

/// Desugar a single parsed expression ID into a desugared expression ID.
/// Reads from `parsed_arena` and writes into `desugared_arena`.
pub fn desugar_expr_with_empty_ctx(
    id: ExprId<Parsed>,
    parsed_arena: &PExprArena,
    module_env: &ModuleEnv<'_>,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<(DExprId, DExprArena), InternalCompilationError> {
    let empty_fn_map = FxHashMap::default();
    let generic_ty_params = GenericTyParams::default();
    let mut ctx = DesugarCtx::new(&empty_fn_map, module_env, &generic_ty_params);
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
pub(crate) fn desugar(
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
        SetLiteral(elements) => build_set_literal(
            desugar_exprs(elements, ctx, parsed_arena, desugared_arena, modules_used)?,
            expr_span,
            ctx,
            desugared_arena,
            modules_used,
        )?,
        MapLiteral(entries) => {
            let entries = entries
                .into_iter()
                .map(|entry| {
                    Ok((
                        desugar(entry.key, ctx, parsed_arena, desugared_arena, modules_used)?,
                        desugar(
                            entry.value,
                            ctx,
                            parsed_arena,
                            desugared_arena,
                            modules_used,
                        )?,
                    ))
                })
                .collect::<Result<Vec<_>, InternalCompilationError>>()?;
            build_map_literal(entries, expr_span, ctx, desugared_arena, modules_used)?
        }
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
        EffectsUnsafe(expr) => ExprKind::effects_unsafe(desugar(
            expr,
            ctx,
            parsed_arena,
            desugared_arena,
            modules_used,
        )?),
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
                pattern,
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
            let loop_item_name = ctx.fresh_generated_local("for_item", pattern.span);
            let loop_item_expr =
                desugared_arena.alloc(DExpr::single_identifier(loop_item_name.0, pattern.span));
            let desugared_body = {
                let env_size = ctx.locals.len();
                let pattern_stmts = desugar_pattern_bindings(
                    &pattern,
                    loop_item_expr,
                    None,
                    pattern.span,
                    ctx,
                    desugared_arena,
                    modules_used,
                )?;
                let desugared_body =
                    desugar(body, ctx, parsed_arena, desugared_arena, modules_used)?;
                ctx.locals.truncate(env_size);
                if pattern_stmts.is_empty() {
                    desugared_body
                } else {
                    desugared_arena.alloc(DExpr::new(
                        ExprKind::block(ext_b(pattern_stmts, desugared_body)),
                        body_span,
                    ))
                }
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
                                    vec![PatternVar::Named(loop_item_name)],
                                ),
                                pattern.span,
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
            let ty = ty.desugar_with_ty_params(
                span,
                false,
                ctx.module_env,
                ctx.generic_ty_params,
                modules_used,
            )?;
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

fn inferred_collection_type(
    name: &str,
    arg_count: usize,
    span: Location,
    ctx: &DesugarCtx<'_>,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<Type, InternalCompilationError> {
    let ty = ast::PType::AppliedPath {
        path: std_path(name, span),
        args: (0..arg_count).map(|_| (ast::PType::Infer, span)).collect(),
    };
    ty.desugar_with_ty_params(
        span,
        false,
        ctx.module_env,
        ctx.generic_ty_params,
        modules_used,
    )
}

fn std_path(name: &str, span: Location) -> Path {
    Path::new(vec![(ustr("std"), span), (ustr(name), span)])
}

fn std_identifier(name: &str, span: Location, arena: &mut DExprArena) -> DExprId {
    arena.alloc(DExpr::new(ExprKind::identifier(std_path(name, span)), span))
}

fn collect_as(
    collection: DExprId,
    ty: Type,
    span: Location,
    arena: &mut DExprArena,
) -> ExprKind<Desugared> {
    let iter = std_identifier("iter", span, arena);
    let iterator = arena.alloc(DExpr::new(
        ExprKind::apply(iter, vec![collection], UnnamedArg::First),
        span,
    ));
    let collect = std_identifier("collect", span, arena);
    let collected = arena.alloc(DExpr::new(
        ExprKind::apply(collect, vec![iterator], UnnamedArg::First),
        span,
    ));
    ExprKind::type_ascription(collected, ty, span)
}

fn empty_as(ty: Type, span: Location, arena: &mut DExprArena) -> ExprKind<Desugared> {
    let empty = std_identifier("empty", span, arena);
    let value = arena.alloc(DExpr::new(
        ExprKind::apply(empty, vec![], UnnamedArg::None),
        span,
    ));
    ExprKind::type_ascription(value, ty, span)
}

fn build_set_literal(
    elements: Vec<DExprId>,
    span: Location,
    ctx: &DesugarCtx<'_>,
    arena: &mut DExprArena,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<ExprKind<Desugared>, InternalCompilationError> {
    let ty = inferred_collection_type("set", 1, span, ctx, modules_used)?;
    if elements.is_empty() {
        Ok(empty_as(ty, span, arena))
    } else {
        let array = arena.alloc(DExpr::new(ExprKind::array(elements), span));
        Ok(collect_as(array, ty, span, arena))
    }
}

fn build_map_literal(
    entries: Vec<(DExprId, DExprId)>,
    span: Location,
    ctx: &DesugarCtx<'_>,
    arena: &mut DExprArena,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<ExprKind<Desugared>, InternalCompilationError> {
    let ty = inferred_collection_type("map", 2, span, ctx, modules_used)?;
    if entries.is_empty() {
        return Ok(empty_as(ty, span, arena));
    }
    let entries = entries
        .into_iter()
        .map(|(key, value)| arena.alloc(DExpr::new(ExprKind::tuple(vec![key, value]), span)))
        .collect();
    let array = arena.alloc(DExpr::new(ExprKind::array(entries), span));
    Ok(collect_as(array, ty, span, arena))
}
