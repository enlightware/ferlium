use super::expr::desugar;
use super::*;

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
        Some((_, TypeDefLookupResult::Enum(_, tag))) => {
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
) -> Result<Option<PatternConstraintKind>, InternalCompilationError> {
    if let Some(path) = path {
        let path_span = path.span().unwrap_or(pattern_span);
        let type_def = resolve_struct_pattern_type(path, ctx, modules_used)?;
        let arity = {
            let payload_ty = type_def.shape_ty();
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
        Ok(Some(PatternConstraintKind::NamedType(type_def)))
    } else {
        Ok(Some(PatternConstraintKind::ExactTuple(element_count)))
    }
}

fn validate_record_struct_pattern(
    type_def: &TypeDefRef,
    sorted_fields: &[&LetRecordPatternField],
    pattern_span: Location,
    has_rest: bool,
) -> Result<(), InternalCompilationError> {
    let shape_data = type_def.shape_ty().data();
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
) -> Result<Option<PatternConstraintKind>, InternalCompilationError> {
    let record_ctx = if path.is_some() {
        DuplicatedFieldContext::Struct
    } else {
        DuplicatedFieldContext::Record
    };
    let sorted_fields = sort_record_pattern_fields(fields, pattern_span, record_ctx)?;
    if let Some(path) = path {
        let type_def = resolve_struct_pattern_type(path, ctx, modules_used)?;
        validate_record_struct_pattern(&type_def, &sorted_fields, pattern_span, has_rest)?;
        Ok(Some(PatternConstraintKind::NamedType(type_def)))
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
            let (source_expr, ty_ascription_span) = if let Some(constraint) = ty_constraint {
                let source_expr_span = desugared_arena[source_expr].span;
                let constrained_expr = desugared_arena.alloc(DExpr::new(
                    ExprKind::PatternConstraint(b(ast::PatternConstraintData::new(
                        source_expr,
                        constraint,
                        pattern.span,
                    ))),
                    source_expr_span,
                ));
                (constrained_expr, source_ty_ascription_span)
            } else {
                (source_expr, source_ty_ascription_span)
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
            let (source_expr, ty_ascription_span) = if let Some(constraint) = ty_constraint {
                let source_expr_span = desugared_arena[source_expr].span;
                let constrained_expr = desugared_arena.alloc(DExpr::new(
                    ExprKind::PatternConstraint(b(ast::PatternConstraintData::new(
                        source_expr,
                        constraint,
                        pattern.span,
                    ))),
                    source_expr_span,
                ));
                (constrained_expr, source_ty_ascription_span)
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

pub(super) fn desugar_pattern_bindings(
    pattern: &LetPattern,
    source_expr: DExprId,
    source_ty_ascription_span: Option<Location>,
    stmt_span: Location,
    ctx: &mut DesugarCtx,
    desugared_arena: &mut DExprArena,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<Vec<DExprId>, InternalCompilationError> {
    ensure_unique_let_pattern_bindings(pattern)?;
    expand_let_pattern(
        pattern,
        source_expr,
        source_ty_ascription_span,
        stmt_span,
        ctx,
        desugared_arena,
        modules_used,
    )
}

pub(super) fn desugar_let_exprs(
    data: LetData<Parsed>,
    stmt_span: Location,
    ctx: &mut DesugarCtx,
    parsed_arena: &PExprArena,
    desugared_arena: &mut DExprArena,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<Vec<DExprId>, InternalCompilationError> {
    let expr = desugar(data.expr, ctx, parsed_arena, desugared_arena, modules_used)?;
    let ty_ascription_span = data.ty_ascription.map(|(span, _)| span);
    desugar_pattern_bindings(
        &data.pattern,
        expr,
        ty_ascription_span,
        stmt_span,
        ctx,
        desugared_arena,
        modules_used,
    )
}

pub(super) fn desugar_block_exprs(
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
