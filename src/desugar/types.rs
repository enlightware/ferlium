use super::*;

fn desugar_type_constraint(
    constraint: &ast::PTypeConstraint,
    generic_ty_params: &GenericTyParams,
    env: &ModuleEnv<'_>,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<PubTypeConstraint, InternalCompilationError> {
    let trait_span = constraint.trait_name.span().unwrap_or(constraint.span);
    let Some((module_id, trait_ref)) = env.trait_ref_with_module(&constraint.trait_name)? else {
        return Err(internal_compilation_error!(TraitNotFound(trait_span)));
    };
    record_module_use(module_id, modules_used);

    let input_tys = if constraint.input_types.len() == 1 && constraint.input_types[0].name.is_none()
    {
        if trait_ref.input_type_count() != 1 {
            let expected_count = trait_ref.input_type_count() as usize;
            return Err(internal_compilation_error!(InvalidTraitConstraint {
                trait_name: constraint.trait_name.to_string(),
                kind: InvalidTraitConstraintKind::ExpectedNamedInputs { expected_count },
                span: constraint.span,
            }));
        }
        vec![constraint.input_types[0].ty.0.desugar_with_ty_params(
            constraint.input_types[0].ty.1,
            false,
            env,
            generic_ty_params,
            modules_used,
        )?]
    } else {
        let named_inputs = constraint
            .input_types
            .iter()
            .map(|input| {
                let Some(name) = input.name else {
                    let expected_count = trait_ref.input_type_count() as usize;
                    return Err(internal_compilation_error!(InvalidTraitConstraint {
                        trait_name: constraint.trait_name.to_string(),
                        kind: InvalidTraitConstraintKind::ExpectedNamedInputs { expected_count },
                        span: constraint.span,
                    }));
                };
                Ok((
                    name,
                    input.ty.0.desugar_with_ty_params(
                        input.ty.1,
                        false,
                        env,
                        generic_ty_params,
                        modules_used,
                    )?,
                ))
            })
            .collect::<Result<Vec<_>, _>>()?;
        desugar_named_type_bindings(
            &trait_ref.input_type_names,
            named_inputs,
            TraitConstraintBindingKind::Input,
            &constraint.trait_name,
            constraint.span,
        )?
    };

    let output_tys = desugar_named_type_bindings(
        &trait_ref.output_type_names,
        constraint
            .output_types
            .iter()
            .map(|output| {
                Ok((
                    output.name,
                    output.ty.0.desugar_with_ty_params(
                        output.ty.1,
                        false,
                        env,
                        generic_ty_params,
                        modules_used,
                    )?,
                ))
            })
            .collect::<Result<Vec<_>, _>>()?,
        TraitConstraintBindingKind::Output,
        &constraint.trait_name,
        constraint.span,
    )?;

    Ok(PubTypeConstraint::new_have_trait(
        trait_ref,
        input_tys,
        output_tys,
        constraint.span,
    ))
}

impl ast::PFnArgType {
    pub fn desugar(
        &self,
        env: &ModuleEnv<'_>,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<FnArgType, InternalCompilationError> {
        let generic_ty_params = GenericTyParams::default();
        self.desugar_with_ty_params(env, &generic_ty_params, modules_used)
    }

    fn desugar_with_ty_params(
        &self,
        env: &ModuleEnv<'_>,
        generic_ty_params: &GenericTyParams,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<FnArgType, InternalCompilationError> {
        let ty = self.ty.0.desugar_with_ty_params(
            self.ty.1,
            false,
            env,
            generic_ty_params,
            modules_used,
        )?;
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
        let generic_ty_params = GenericTyParams::default();
        self.desugar_with_ty_params(env, &generic_ty_params, modules_used)
    }

    fn desugar_with_ty_params(
        &self,
        env: &ModuleEnv<'_>,
        generic_ty_params: &GenericTyParams,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<FnType, InternalCompilationError> {
        let args = self
            .args
            .iter()
            .map(|arg| arg.desugar_with_ty_params(env, generic_ty_params, modules_used))
            .collect::<Result<Vec<_>, _>>()?;
        let ret = self.ret.0.desugar_with_ty_params(
            self.ret.1,
            false,
            env,
            generic_ty_params,
            modules_used,
        )?;
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
        let generic_ty_params = GenericTyParams::default();
        self.desugar_with_ty_params(span, in_ty_def, env, &generic_ty_params, modules_used)
    }

    pub(super) fn desugar_with_ty_params(
        &self,
        span: Location,
        in_ty_def: bool,
        env: &ModuleEnv<'_>,
        generic_ty_params: &GenericTyParams,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<Type, InternalCompilationError> {
        use ast::PType::*;
        Ok(match self {
            Never => Type::never(),
            Unit => Type::unit(),
            Resolved(ty) => *ty,
            Infer => Type::variable_id(0), // always emit variable id 0 that will be replaced by fresh variables in type inference
            Path(path) => {
                if let [(name, _)] = &path.segments[..]
                    && let Some(ty_var) = generic_ty_params.get(name)
                {
                    Type::variable(*ty_var)
                } else if let Some((module_id, ty)) = env.type_alias_type_with_module(path)? {
                    record_module_use(module_id, modules_used);
                    ty
                } else if let Some((module_id, type_def)) = env.type_def_with_module(path)? {
                    record_module_use(module_id, modules_used);
                    if !type_def.param_names.is_empty() {
                        return Err(internal_compilation_error!(WrongNumberOfArguments {
                            expected: type_def.param_names.len(),
                            expected_span: type_def.span,
                            got: 0,
                            got_span: span,
                        }));
                    }
                    Type::named(type_def, Vec::new())
                } else if let [(name, _)] = &path.segments[..] {
                    Type::variant([(*name, Type::unit())])
                } else {
                    return Err(internal_compilation_error!(TypeNotFound(span)));
                }
            }
            AppliedPath { path, args } => {
                if let Some((module_id, ty)) = env.type_alias_type_with_module(path)? {
                    record_module_use(module_id, modules_used);
                    let expected_span = path.span().unwrap_or(span);
                    let _ = ty;
                    return Err(internal_compilation_error!(WrongNumberOfArguments {
                        expected: 0,
                        expected_span,
                        got: args.len(),
                        got_span: span,
                    }));
                } else if let Some((module_id, type_def)) = env.type_def_with_module(path)? {
                    record_module_use(module_id, modules_used);
                    let desugared_args = args
                        .iter()
                        .map(|(ty, ty_span)| {
                            ty.desugar_with_ty_params(
                                *ty_span,
                                false,
                                env,
                                generic_ty_params,
                                modules_used,
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    if type_def.param_names.len() != desugared_args.len() {
                        return Err(internal_compilation_error!(WrongNumberOfArguments {
                            expected: type_def.param_names.len(),
                            expected_span: type_def.span,
                            got: desugared_args.len(),
                            got_span: span,
                        }));
                    }
                    Type::named(type_def, desugared_args)
                } else if let [(name, name_span)] = &path.segments[..] {
                    if generic_ty_params.contains_key(name) {
                        return Err(internal_compilation_error!(WrongNumberOfArguments {
                            expected: 0,
                            expected_span: *name_span,
                            got: args.len(),
                            got_span: span,
                        }));
                    }
                    return Err(internal_compilation_error!(TypeNotFound(span)));
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
                                Ok((
                                    *name,
                                    ty.desugar_with_ty_params(
                                        *ty_span,
                                        false,
                                        env,
                                        generic_ty_params,
                                        modules_used,
                                    )?,
                                ))
                            }
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                )
            }
            Tuple(elements) => Type::tuple(
                elements
                    .iter()
                    .map(|(ty, span)| {
                        ty.desugar_with_ty_params(
                            *span,
                            false,
                            env,
                            generic_ty_params,
                            modules_used,
                        )
                    })
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
                                Ok((
                                    *name,
                                    ty.desugar_with_ty_params(
                                        *ty_span,
                                        false,
                                        env,
                                        generic_ty_params,
                                        modules_used,
                                    )?,
                                ))
                            }
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                )
            }
            Array(array) => array_type(array.0.desugar_with_ty_params(
                array.1,
                false,
                env,
                generic_ty_params,
                modules_used,
            )?),
            Function(fn_type) => Type::function_type(fn_type.desugar_with_ty_params(
                env,
                generic_ty_params,
                modules_used,
            )?),
        })
    }
}

impl PTypeDef {
    pub(super) fn desugar(
        &self,
        env: &ModuleEnv<'_>,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<TypeDefRef, InternalCompilationError> {
        let mut ty_quantifiers = Vec::with_capacity(self.generic_params.len());
        let mut generic_ty_params = GenericTyParams::default();
        for (index, param) in self.generic_params.iter().enumerate() {
            let ty_var = TypeVar::new(index as u32);
            if generic_ty_params.insert(param.0, ty_var).is_some() {
                return Err(internal_compilation_error!(Unsupported {
                    reason: format!(
                        "Duplicate generic type parameter `{}` in type definition `{}`",
                        param.0, self.name.0
                    ),
                    span: param.1,
                }));
            }
            ty_quantifiers.push(ty_var);
        }
        let shape = self.shape.desugar_with_ty_params(
            self.span,
            true,
            env,
            &generic_ty_params,
            modules_used,
        )?;
        let constraints = self
            .where_clause
            .iter()
            .map(|constraint| {
                desugar_type_constraint(constraint, &generic_ty_params, env, modules_used)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(TypeDefRef::new(crate::r#type::TypeDef {
            name: self.name.0,
            doc: (!self.doc_comments.is_empty()).then(|| self.doc_comments.join("\n")),
            param_names: self.generic_params.iter().map(|(name, _)| *name).collect(),
            shape: TypeScheme {
                ty_quantifiers,
                eff_quantifiers: FxHashSet::default(),
                ty: shape,
                constraints,
            },
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
        let generic_ty_params = GenericTyParams::default();
        self.desugar_with_ty_params(env, &generic_ty_params, modules_used)
    }

    pub(super) fn desugar_with_ty_params(
        self,
        env: &ModuleEnv<'_>,
        generic_ty_params: &GenericTyParams,
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
                    ty.desugar_with_ty_params(span, false, env, generic_ty_params, modules_used)?,
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

fn collect_trait_impl_generic_ty_params_from_ty(
    ty: &ast::PType,
    env: &ModuleEnv<'_>,
    generic_ty_params: &mut GenericTyParams,
    next_index: &mut u32,
) -> Result<(), InternalCompilationError> {
    use ast::PType::*;

    match ty {
        Never | Unit | Infer | Resolved(_) => {}
        Path(path) => {
            if let [(name, _)] = &path.segments[..]
                && env.type_alias_type_with_module(path)?.is_none()
                && env.type_def_with_module(path)?.is_none()
            {
                generic_ty_params.entry(*name).or_insert_with(|| {
                    let ty_var = TypeVar::new(*next_index);
                    *next_index += 1;
                    ty_var
                });
            }
        }
        AppliedPath { args, .. } => {
            for (arg, _) in args {
                collect_trait_impl_generic_ty_params_from_ty(
                    arg,
                    env,
                    generic_ty_params,
                    next_index,
                )?;
            }
        }
        Variant(types) => {
            for (_, (payload_ty, _)) in types {
                collect_trait_impl_generic_ty_params_from_ty(
                    payload_ty,
                    env,
                    generic_ty_params,
                    next_index,
                )?;
            }
        }
        Tuple(elements) => {
            for (element_ty, _) in elements {
                collect_trait_impl_generic_ty_params_from_ty(
                    element_ty,
                    env,
                    generic_ty_params,
                    next_index,
                )?;
            }
        }
        Record(fields) => {
            for (_, (field_ty, _)) in fields {
                collect_trait_impl_generic_ty_params_from_ty(
                    field_ty,
                    env,
                    generic_ty_params,
                    next_index,
                )?;
            }
        }
        Array(element_ty) => {
            collect_trait_impl_generic_ty_params_from_ty(
                &element_ty.0,
                env,
                generic_ty_params,
                next_index,
            )?;
        }
        Function(fn_ty) => {
            for arg in &fn_ty.args {
                collect_trait_impl_generic_ty_params_from_ty(
                    &arg.ty.0,
                    env,
                    generic_ty_params,
                    next_index,
                )?;
            }
            collect_trait_impl_generic_ty_params_from_ty(
                &fn_ty.ret.0,
                env,
                generic_ty_params,
                next_index,
            )?;
        }
    }
    Ok(())
}

fn build_generic_ty_params(
    generic_params: &[UstrSpan],
) -> Result<GenericTyParams, InternalCompilationError> {
    let mut generic_ty_params = GenericTyParams::default();
    for (index, param) in generic_params.iter().enumerate() {
        let ty_var = TypeVar::new(index as u32);
        if generic_ty_params.insert(param.0, ty_var).is_some() {
            return Err(internal_compilation_error!(Unsupported {
                reason: format!("Duplicate generic type parameter `{}` in impl", param.0),
                span: param.1,
            }));
        }
    }
    Ok(generic_ty_params)
}

fn collect_trait_impl_generic_ty_params(
    for_trait: &ast::PTraitImplFor,
    env: &ModuleEnv<'_>,
) -> Result<GenericTyParams, InternalCompilationError> {
    let mut generic_ty_params = GenericTyParams::default();
    let mut next_index = 0;
    for input in &for_trait.input_types {
        collect_trait_impl_generic_ty_params_from_ty(
            &input.ty.0,
            env,
            &mut generic_ty_params,
            &mut next_index,
        )?;
    }
    for output in &for_trait.output_types {
        collect_trait_impl_generic_ty_params_from_ty(
            &output.ty.0,
            env,
            &mut generic_ty_params,
            &mut next_index,
        )?;
    }
    Ok(generic_ty_params)
}

fn desugar_trait_impl_for(
    for_trait: ast::PTraitImplFor,
    trait_name: UstrSpan,
    generic_ty_params: &GenericTyParams,
    env: &ModuleEnv<'_>,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<ast::DTraitImplFor, InternalCompilationError> {
    let trait_path = ast::Path::single_tuple(trait_name);
    let Some((module_id, trait_ref)) = env.trait_ref_with_module(&trait_path)? else {
        return Err(internal_compilation_error!(TraitNotFound(trait_name.1)));
    };
    record_module_use(module_id, modules_used);

    if for_trait.output_types.is_empty()
        && for_trait
            .input_types
            .iter()
            .all(|input| input.name.is_none())
    {
        let input_types = for_trait
            .input_types
            .into_iter()
            .map(|input| {
                input
                    .ty
                    .0
                    .desugar_with_ty_params(input.ty.1, false, env, generic_ty_params, modules_used)
                    .map(|ty| ast::TypeConstraintInput {
                        name: None,
                        ty: (ty, input.ty.1),
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        if input_types.len() != trait_ref.input_type_count() as usize {
            return Err(internal_compilation_error!(WrongNumberOfArguments {
                expected: trait_ref.input_type_count() as usize,
                expected_span: trait_name.1,
                got: input_types.len(),
                got_span: for_trait.span,
            }));
        }
        return Ok(ast::DTraitImplFor {
            input_types,
            output_types: vec![],
            span: for_trait.span,
        });
    }

    let input_types = desugar_named_type_bindings(
        &trait_ref.input_type_names,
        for_trait
            .input_types
            .into_iter()
            .map(|input| {
                let Some(name) = input.name else {
                    let expected_count = trait_ref.input_type_count() as usize;
                    return Err(internal_compilation_error!(InvalidTraitConstraint {
                        trait_name: trait_path.to_string(),
                        kind: InvalidTraitConstraintKind::ExpectedNamedInputs { expected_count },
                        span: for_trait.span,
                    }));
                };
                Ok((
                    name,
                    (
                        input.ty.0.desugar_with_ty_params(
                            input.ty.1,
                            false,
                            env,
                            generic_ty_params,
                            modules_used,
                        )?,
                        input.ty.1,
                    ),
                ))
            })
            .collect::<Result<Vec<_>, _>>()?,
        TraitConstraintBindingKind::Input,
        &trait_path,
        for_trait.span,
    )?;
    let output_types = desugar_named_type_bindings(
        &trait_ref.output_type_names,
        for_trait
            .output_types
            .into_iter()
            .map(|output| {
                Ok((
                    output.name,
                    (
                        output.ty.0.desugar_with_ty_params(
                            output.ty.1,
                            false,
                            env,
                            generic_ty_params,
                            modules_used,
                        )?,
                        output.ty.1,
                    ),
                ))
            })
            .collect::<Result<Vec<_>, _>>()?,
        TraitConstraintBindingKind::Output,
        &trait_path,
        for_trait.span,
    )?;

    Ok(ast::DTraitImplFor {
        input_types: trait_ref
            .input_type_names
            .iter()
            .copied()
            .zip(input_types)
            .map(|(name, ty)| ast::TypeConstraintInput {
                name: Some((name, for_trait.span)),
                ty,
            })
            .collect(),
        output_types: trait_ref
            .output_type_names
            .iter()
            .copied()
            .zip(output_types)
            .map(|(name, ty)| ast::TypeConstraintOutput {
                name: (name, for_trait.span),
                ty,
            })
            .collect(),
        span: for_trait.span,
    })
}

impl PTraitImpl {
    pub fn desugar(
        self,
        env: &ModuleEnv<'_>,
        parsed_arena: &PExprArena,
        desugared_arena: &mut DExprArena,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<DTraitImpl, InternalCompilationError> {
        let generic_ty_params = if self.generic_params.is_empty() {
            self.for_trait
                .as_ref()
                .map(|for_trait| collect_trait_impl_generic_ty_params(for_trait, env))
                .transpose()?
                .unwrap_or_default()
        } else {
            build_generic_ty_params(&self.generic_params)?
        };
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
                f.desugar_with_ty_params(
                    &fn_map,
                    env,
                    &generic_ty_params,
                    parsed_arena,
                    desugared_arena,
                    modules_used,
                )
                .map(|(f, _dep_graph)| f)
            })
            .collect::<Result<_, _>>()?;
        let for_trait = self
            .for_trait
            .map(|for_trait| {
                desugar_trait_impl_for(
                    for_trait,
                    self.trait_name,
                    &generic_ty_params,
                    env,
                    modules_used,
                )
            })
            .transpose()?;
        Ok(DTraitImpl {
            span: self.span,
            generic_params: self.generic_params,
            trait_name: self.trait_name,
            for_trait,
            functions,
        })
    }
}

fn record_module_use(module_id: Option<ModuleId>, modules_used: &mut FxHashSet<ModuleId>) {
    if let Some(module_id) = module_id {
        modules_used.insert(module_id);
    }
}

#[derive(Clone, Copy)]
enum TraitConstraintBindingKind {
    Input,
    Output,
}

fn desugar_named_type_bindings<T>(
    expected_names: &[Ustr],
    bindings: Vec<(UstrSpan, T)>,
    binding_kind: TraitConstraintBindingKind,
    trait_name: &ast::Path,
    span: Location,
) -> Result<Vec<T>, InternalCompilationError> {
    let mut positions = FxHashMap::default();
    for (index, name) in expected_names.iter().copied().enumerate() {
        positions.insert(name, index);
    }

    let mut ordered = (0..expected_names.len()).map(|_| None).collect::<Vec<_>>();
    for (binding_name, ty) in bindings {
        let Some(&index) = positions.get(&binding_name.0) else {
            let name = binding_name.0;
            return Err(internal_compilation_error!(InvalidTraitConstraint {
                trait_name: trait_name.to_string(),
                kind: match binding_kind {
                    TraitConstraintBindingKind::Input => {
                        InvalidTraitConstraintKind::UnknownInputBinding { name }
                    }
                    TraitConstraintBindingKind::Output => {
                        InvalidTraitConstraintKind::UnknownOutputBinding { name }
                    }
                },
                span: binding_name.1,
            }));
        };
        if ordered[index].is_some() {
            let name = binding_name.0;
            return Err(internal_compilation_error!(InvalidTraitConstraint {
                trait_name: trait_name.to_string(),
                kind: match binding_kind {
                    TraitConstraintBindingKind::Input => {
                        InvalidTraitConstraintKind::DuplicateInputBinding { name }
                    }
                    TraitConstraintBindingKind::Output => {
                        InvalidTraitConstraintKind::DuplicateOutputBinding { name }
                    }
                },
                span: binding_name.1,
            }));
        }
        ordered[index] = Some(ty);
    }

    let missing = expected_names
        .iter()
        .enumerate()
        .filter_map(|(index, name)| ordered[index].is_none().then_some(name.to_string()))
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        let names = missing.iter().map(|name| ustr(name)).collect();
        return Err(internal_compilation_error!(InvalidTraitConstraint {
            trait_name: trait_name.to_string(),
            kind: match binding_kind {
                TraitConstraintBindingKind::Input => {
                    InvalidTraitConstraintKind::MissingInputBindings { names }
                }
                TraitConstraintBindingKind::Output => {
                    InvalidTraitConstraintKind::MissingOutputBindings { names }
                }
            },
            span,
        }));
    }

    Ok(ordered
        .into_iter()
        .map(|ty| ty.expect("missing bindings already checked"))
        .collect())
}
