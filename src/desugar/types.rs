use super::*;
use crate::compiler::error::{
    AttributeTarget, InvalidAttributeKind, InvalidRecursiveTypeKind, UnsafeFeature,
};
use crate::std::{array::array_type, value::NO_DERIVE_VALUE_ATTRIBUTE};
use crate::types::r#type::{
    BareNativeTypeB, TypeAliasEntry, TypeDef as HirTypeDef, TypeKind, store_types,
};
use crate::types::type_substitution::instantiate_type;

/// Placeholder metadata for an alias root while a recursive type SCC is lowered.
#[derive(Clone)]
pub(crate) struct RecursiveAliasRef {
    pub name: Ustr,
    pub index: u32,
    pub param_names: Vec<Ustr>,
    pub ty_var_count: u32,
    pub span: Location,
}

/// Builds structural recursive alias types from local placeholders and final root shapes.
pub(crate) struct RecursiveTypeBuilder<'a, 'm> {
    env: &'a ModuleEnv<'m>,
    generic_ty_params: GenericTyParams,
    modules_used: &'a mut FxHashSet<ModuleId>,
    aliases: &'a FxHashMap<Ustr, RecursiveAliasRef>,
    type_defs: &'a FxHashMap<Ustr, TypeDefId>,
    kinds: Vec<TypeKind>,
}

impl<'a, 'm> RecursiveTypeBuilder<'a, 'm> {
    pub(crate) fn new(
        root_count: usize,
        env: &'a ModuleEnv<'m>,
        modules_used: &'a mut FxHashSet<ModuleId>,
        aliases: &'a FxHashMap<Ustr, RecursiveAliasRef>,
        type_defs: &'a FxHashMap<Ustr, TypeDefId>,
    ) -> Self {
        Self {
            env,
            generic_ty_params: GenericTyParams::default(),
            modules_used,
            aliases,
            type_defs,
            kinds: vec![TypeKind::Never; root_count],
        }
    }

    pub(crate) fn set_generic_ty_params(&mut self, generic_ty_params: GenericTyParams) {
        self.generic_ty_params = generic_ty_params;
    }

    pub(crate) fn desugar_root(
        &mut self,
        root_index: u32,
        ty: &ast::PType,
        span: Location,
    ) -> Result<Type, InternalCompilationError> {
        self.desugar_type(ty, span, false, Some(root_index))
    }

    pub(crate) fn finish(self, roots: &[Type]) -> Vec<Type> {
        let stored = store_types(&self.kinds);
        roots
            .iter()
            .map(|ty| {
                ty.world()
                    .map_or_else(|| stored[ty.index() as usize], |_| *ty)
            })
            .collect()
    }

    fn store_kind(&mut self, kind: TypeKind, slot: Option<u32>) -> Type {
        let index = if let Some(index) = slot {
            self.kinds[index as usize] = kind;
            index
        } else {
            let index = self.kinds.len() as u32;
            self.kinds.push(kind);
            index
        };
        Type::new_local(index)
    }

    fn resolve_local_alias_without_args(
        &self,
        alias: &RecursiveAliasRef,
        span: Location,
    ) -> Result<Type, InternalCompilationError> {
        expect_type_argument_count(alias.param_names.len(), alias.span, 0, span)?;
        Ok(Type::new_local(alias.index))
    }

    fn resolve_local_alias_with_args(
        &mut self,
        alias: &RecursiveAliasRef,
        args: &[ast::TypeSpan<Parsed>],
        span: Location,
    ) -> Result<Type, InternalCompilationError> {
        expect_type_argument_count(alias.param_names.len(), alias.span, args.len(), span)?;
        let desugared_args = args
            .iter()
            .map(|(arg, arg_span)| self.desugar_type(arg, *arg_span, false, None))
            .collect::<Result<Vec<_>, _>>()?;
        let is_identity = desugared_args
            .iter()
            .copied()
            .eq((0..alias.ty_var_count).map(|index| Type::variable(TypeVar::new(index))));
        if is_identity {
            Ok(Type::new_local(alias.index))
        } else {
            Err(internal_compilation_error!(InvalidRecursiveType {
                kind: InvalidRecursiveTypeKind::NonRegularGenericShape { name: alias.name },
                span,
            }))
        }
    }

    fn desugar_path_without_args(
        &mut self,
        path: &ast::Path,
        span: Location,
    ) -> Result<Type, InternalCompilationError> {
        if let [(name, _)] = &path.segments[..] {
            if let Some(ty_var) = self.generic_ty_params.get(name) {
                return Ok(Type::variable(*ty_var));
            }
            if let Some(alias) = self.aliases.get(name) {
                return self.resolve_local_alias_without_args(alias, span);
            }
            if let Some(type_def) = self.type_defs.get(name) {
                expect_type_argument_count(
                    self.env.type_def_param_names(*type_def).len(),
                    self.env.type_def_span(*type_def),
                    0,
                    span,
                )?;
                return Ok(Type::named(*type_def, Vec::new()));
            }
        }
        if let Some(resolved) = resolve_type_path(path, self.env, self.modules_used)? {
            desugar_resolved_type_without_args(resolved, path, span, self.env)
        } else if let [(name, _)] = &path.segments[..] {
            Ok(self.store_kind(TypeKind::Variant(vec![(*name, Type::unit())]), None))
        } else {
            Err(internal_compilation_error!(TypeNotFound(span)))
        }
    }

    fn desugar_path_with_args(
        &mut self,
        path: &ast::Path,
        args: &[ast::TypeSpan<Parsed>],
        span: Location,
    ) -> Result<Type, InternalCompilationError> {
        if let [(name, name_span)] = &path.segments[..] {
            if self.generic_ty_params.contains_key(name) {
                return Err(internal_compilation_error!(WrongNumberOfArguments {
                    expected: 0,
                    expected_span: *name_span,
                    got: args.len(),
                    got_span: span,
                }));
            }
            if let Some(alias) = self.aliases.get(name).cloned() {
                return self.resolve_local_alias_with_args(&alias, args, span);
            }
            if let Some(type_def) = self.type_defs.get(name) {
                expect_type_argument_count(
                    self.env.type_def_param_names(*type_def).len(),
                    self.env.type_def_span(*type_def),
                    args.len(),
                    span,
                )?;
                let desugared_args = args
                    .iter()
                    .map(|(arg, arg_span)| self.desugar_type(arg, *arg_span, false, None))
                    .collect::<Result<Vec<_>, _>>()?;
                return Ok(Type::named(*type_def, desugared_args));
            }
        }
        if let Some(resolved) = resolve_type_path(path, self.env, self.modules_used)? {
            let desugared_args = args
                .iter()
                .map(|(arg, arg_span)| self.desugar_type(arg, *arg_span, false, None))
                .collect::<Result<Vec<_>, _>>()?;
            desugar_resolved_type_with_args(resolved, path, desugared_args, span, self.env)
        } else {
            Err(internal_compilation_error!(TypeNotFound(span)))
        }
    }

    fn desugar_fn_type(
        &mut self,
        fn_type: &ast::PFnType,
    ) -> Result<FnType, InternalCompilationError> {
        let args = fn_type
            .args
            .iter()
            .map(|arg| {
                let ty = self.desugar_type(&arg.ty.0, arg.ty.1, false, None)?;
                let mut_ty = match arg.mut_ty {
                    Some(ast::PMutType::Mut) => MutType::mutable(),
                    Some(ast::PMutType::Infer) => MutType::variable_id(0),
                    None => MutType::constant(),
                };
                Ok(FnArgType::new(ty, mut_ty))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let ret = self.desugar_type(&fn_type.ret.0, fn_type.ret.1, false, None)?;
        let effects = match &fn_type.effects {
            ast::PFnEffects::ImplicitPure => EffType::empty(),
            ast::PFnEffects::ImplicitGeneric => EffType::single_variable_id(0),
            ast::PFnEffects::Explicit(effects) => EffType::multiple_primitive(effects),
        };
        Ok(FnType::new(args, ret, effects))
    }

    fn desugar_type(
        &mut self,
        ty: &ast::PType,
        span: Location,
        in_ty_def: bool,
        slot: Option<u32>,
    ) -> Result<Type, InternalCompilationError> {
        use ast::PType::*;
        Ok(match ty {
            Never => Type::never(),
            Unit => Type::unit(),
            Resolved(ty) => *ty,
            Infer => Type::variable_id(0),
            Path(path) => self.desugar_path_without_args(path, span)?,
            AppliedPath { path, args } => self.desugar_path_with_args(path, args, span)?,
            Variant(types) => {
                let mut seen = FxHashMap::default();
                let variants = types
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
                            Ok((*name, self.desugar_type(ty, *ty_span, false, None)?))
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                self.store_kind(TypeKind::Variant(variants), slot)
            }
            Tuple(elements) => {
                let elements = elements
                    .iter()
                    .map(|(ty, ty_span)| self.desugar_type(ty, *ty_span, false, None))
                    .collect::<Result<Vec<_>, _>>()?;
                self.store_kind(TypeKind::Tuple(elements), slot)
            }
            Record(fields) => {
                let mut seen = FxHashMap::default();
                let fields = fields
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
                            Ok((*name, self.desugar_type(ty, *ty_span, false, None)?))
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                self.store_kind(TypeKind::Record(fields), slot)
            }
            Array(array) => {
                let element = self.desugar_type(&array.0, array.1, false, None)?;
                desugar_array_syntax_type(element, self.env.current.module_id(), self.modules_used)
            }
            Function(fn_type) => {
                let fn_type = self.desugar_fn_type(fn_type)?;
                self.store_kind(TypeKind::Function(b(fn_type)), slot)
            }
        })
    }
}

fn desugar_type_constraint(
    constraint: &ast::PTypeConstraint,
    generic_ty_params: &GenericTyParams,
    env: &ModuleEnv<'_>,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<PubTypeConstraint, InternalCompilationError> {
    let trait_span = constraint.trait_name.span().unwrap_or(constraint.span);
    let Some((module_id, trait_id)) = env.trait_id_with_module(&constraint.trait_name)? else {
        return Err(internal_compilation_error!(TraitNotFound(trait_span)));
    };
    record_module_use(module_id, modules_used);
    let trait_def = env.trait_def(trait_id);

    let has_named_inputs = constraint
        .input_types
        .iter()
        .any(|input| input.name.is_some());
    let has_positional_inputs = constraint
        .input_types
        .iter()
        .any(|input| input.name.is_none());
    let input_tys = if has_positional_inputs && !has_named_inputs {
        if trait_def.input_type_count() as usize != constraint.input_types.len() {
            let expected_count = trait_def.input_type_count() as usize;
            let kind = if constraint.input_types.len() == 1 {
                InvalidTraitConstraintKind::ExpectedNamedInputs { expected_count }
            } else {
                InvalidTraitConstraintKind::WrongNumberOfInputBindings {
                    expected_count,
                    got_count: constraint.input_types.len(),
                }
            };
            return Err(internal_compilation_error!(InvalidTraitConstraint {
                trait_name: constraint.trait_name.to_string(),
                kind,
                span: constraint.span,
            }));
        }
        constraint
            .input_types
            .iter()
            .map(|input| {
                input.ty.0.desugar_with_ty_params(
                    input.ty.1,
                    false,
                    env,
                    generic_ty_params,
                    modules_used,
                )
            })
            .collect::<Result<Vec<_>, _>>()?
    } else {
        let named_inputs = constraint
            .input_types
            .iter()
            .map(|input| {
                let Some(name) = input.name else {
                    let expected_count = trait_def.input_type_count() as usize;
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
            &trait_def.input_type_names,
            named_inputs,
            TraitConstraintBindingKind::Input,
            &constraint.trait_name,
            constraint.span,
        )?
    };

    let output_tys = desugar_named_type_bindings(
        &trait_def.output_type_names,
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
        trait_id,
        input_tys,
        output_tys,
        constraint.span,
    ))
}

pub(crate) fn desugar_type_constraints(
    constraints: &[ast::PTypeConstraint],
    generic_ty_params: &GenericTyParams,
    env: &ModuleEnv<'_>,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<Vec<PubTypeConstraint>, InternalCompilationError> {
    constraints
        .iter()
        .map(|constraint| desugar_type_constraint(constraint, generic_ty_params, env, modules_used))
        .collect()
}

fn desugar_default_variant(
    type_def: &ast::PTypeDef,
) -> Result<Option<Ustr>, InternalCompilationError> {
    use ast::PType;

    let PType::Variant(variants) = &type_def.shape else {
        return Ok(None);
    };
    assert_eq!(type_def.variant_attributes.len(), variants.len());

    let mut default_variant = None;
    for (((variant_name, _), _), attributes) in variants.iter().zip(&type_def.variant_attributes) {
        let mut variant_has_default = false;
        for attribute in attributes {
            if attribute.path.0 != ustr("default") {
                continue;
            }
            if !attribute.items.is_empty() {
                return Err(internal_compilation_error!(InvalidAttribute {
                    attribute_name: attribute.path.0,
                    target: AttributeTarget::EnumVariant {
                        type_name: type_def.name.0,
                        variant_name: *variant_name,
                    },
                    kind: InvalidAttributeKind::HasArguments,
                    span: attribute.span,
                }));
            }
            if variant_has_default {
                return Err(internal_compilation_error!(InvalidAttribute {
                    attribute_name: attribute.path.0,
                    target: AttributeTarget::EnumVariant {
                        type_name: type_def.name.0,
                        variant_name: *variant_name,
                    },
                    kind: InvalidAttributeKind::Duplicate,
                    span: attribute.span,
                }));
            }
            variant_has_default = true;
        }

        if variant_has_default {
            if let Some(previous) = default_variant {
                return Err(internal_compilation_error!(InvalidEnumDefaultAttribute {
                    type_name: type_def.name.0,
                    kind: InvalidEnumDefaultAttributeKind::MultipleDefaultVariants {
                        first_variant: previous,
                        second_variant: *variant_name,
                    },
                    span: type_def.span,
                }));
            }
            default_variant = Some(*variant_name);
        }
    }
    Ok(default_variant)
}

fn validate_type_def_attributes(
    type_def: &ast::PTypeDef,
    is_std_module: bool,
) -> Result<(), InternalCompilationError> {
    let mut has_no_derive_value = false;
    for attribute in &type_def.attributes {
        if attribute.path.0 != ustr(NO_DERIVE_VALUE_ATTRIBUTE) {
            continue;
        }
        if !is_std_module {
            return Err(
                InternalCompilationError::new_unsafe_feature_use_not_allowed(
                    UnsafeFeature::TypeAttribute(attribute.path.0),
                    attribute.span,
                ),
            );
        }
        if !attribute.items.is_empty() {
            return Err(internal_compilation_error!(InvalidAttribute {
                attribute_name: attribute.path.0,
                target: AttributeTarget::TypeDef {
                    name: type_def.name.0,
                },
                kind: InvalidAttributeKind::HasArguments,
                span: attribute.span,
            }));
        }
        if has_no_derive_value {
            return Err(internal_compilation_error!(InvalidAttribute {
                attribute_name: attribute.path.0,
                target: AttributeTarget::TypeDef {
                    name: type_def.name.0,
                },
                kind: InvalidAttributeKind::Duplicate,
                span: attribute.span,
            }));
        }
        has_no_derive_value = true;
    }
    Ok(())
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

    pub(crate) fn desugar_with_ty_params(
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
        let effects = match &self.effects {
            ast::PFnEffects::ImplicitPure => EffType::empty(),
            // Always emit variable id 0 here; type inference will freshen it later.
            ast::PFnEffects::ImplicitGeneric => EffType::single_variable_id(0),
            ast::PFnEffects::Explicit(effects) => EffType::multiple_primitive(effects),
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

    pub(crate) fn desugar_with_ty_params(
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
                } else if let Some(resolved) = resolve_type_path(path, env, modules_used)? {
                    desugar_resolved_type_without_args(resolved, path, span, env)?
                } else if let [(name, _)] = &path.segments[..] {
                    Type::variant([(*name, Type::unit())])
                } else {
                    return Err(internal_compilation_error!(TypeNotFound(span)));
                }
            }
            AppliedPath { path, args } => {
                if let Some(resolved) = resolve_type_path(path, env, modules_used)? {
                    let desugared_args =
                        desugar_type_arguments(args, env, generic_ty_params, modules_used)?;
                    desugar_resolved_type_with_args(resolved, path, desugared_args, span, env)?
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
            Array(array) => desugar_array_syntax_type(
                array.0.desugar_with_ty_params(
                    array.1,
                    false,
                    env,
                    generic_ty_params,
                    modules_used,
                )?,
                env.current.module_id(),
                modules_used,
            ),
            Function(fn_type) => Type::function_type(fn_type.desugar_with_ty_params(
                env,
                generic_ty_params,
                modules_used,
            )?),
        })
    }
}

impl PTypeDef {
    pub(crate) fn desugar_data(
        &self,
        env: &ModuleEnv<'_>,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<HirTypeDef, InternalCompilationError> {
        validate_type_def_attributes(self, env.current.module_id() == STD_MODULE_ID)?;
        let generic_ty_params = extend_generic_ty_params(
            &GenericTyParams::default(),
            &self.generic_params,
            GenericParamsOwner::TypeDef { name: self.name.0 },
        )?;
        let ty_quantifiers = self
            .generic_params
            .iter()
            .map(|param| generic_ty_params.get(&param.0).copied().unwrap())
            .collect();
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
        let default_variant = desugar_default_variant(self)?;
        Ok(HirTypeDef {
            name: self.name.0,
            doc: (!self.doc_comments.is_empty()).then(|| self.doc_comments.join("\n")),
            generic_params: self.generic_params.clone(),
            shape: TypeScheme {
                ty_quantifiers,
                eff_quantifiers: FxHashSet::default(),
                ty: shape,
                constraints,
            },
            shape_docs: self.shape_docs.clone(),
            span: self.span,
            attributes: self.attributes.clone(),
            default_variant,
        })
    }

    pub(crate) fn desugar(
        &self,
        env: &ModuleEnv<'_>,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<HirTypeDef, InternalCompilationError> {
        self.desugar_data(env, modules_used)
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

    pub(crate) fn desugar_with_ty_params(
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
            mut_binding: self.mut_binding,
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
                && env.type_alias_with_module(path)?.is_none()
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

fn invalid_generic_params_error(
    owner: GenericParamsOwner,
    name: Ustr,
    span: Location,
) -> InternalCompilationError {
    internal_compilation_error!(InvalidGenericParams {
        owner,
        kind: InvalidGenericParamsKind::DuplicateParam { name },
        span,
    })
}

pub(crate) fn extend_generic_ty_params(
    existing: &GenericTyParams,
    generic_params: &[UstrSpan],
    owner: GenericParamsOwner,
) -> Result<GenericTyParams, InternalCompilationError> {
    let next_index = existing
        .values()
        .map(TypeVar::name)
        .max()
        .map_or(0, |index| index + 1);
    let mut generic_ty_params = existing.clone();
    for (generic_index, param) in generic_params.iter().enumerate() {
        let ty_var = TypeVar::new(next_index + generic_index as u32);
        if generic_ty_params.insert(param.0, ty_var).is_some() {
            return Err(invalid_generic_params_error(owner, param.0, param.1));
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
    let Some((module_id, trait_id)) = env.trait_id_with_module(&trait_path)? else {
        return Err(internal_compilation_error!(TraitNotFound(trait_name.1)));
    };
    record_module_use(module_id, modules_used);
    let trait_def = env.trait_def(trait_id);

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
        if input_types.len() != trait_def.input_type_count() as usize {
            return Err(internal_compilation_error!(WrongNumberOfArguments {
                expected: trait_def.input_type_count() as usize,
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
        &trait_def.input_type_names,
        for_trait
            .input_types
            .into_iter()
            .map(|input| {
                let Some(name) = input.name else {
                    let expected_count = trait_def.input_type_count() as usize;
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
        &trait_def.output_type_names,
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
        input_types: trait_def
            .input_type_names
            .iter()
            .copied()
            .zip(input_types)
            .map(|(name, ty)| ast::TypeConstraintInput {
                name: Some((name, for_trait.span)),
                ty,
            })
            .collect(),
        output_types: trait_def
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

#[derive(Clone)]
enum ResolvedTypePath {
    Alias(TypeAliasEntry),
    TypeDef(TypeDefId),
    BareNative(BareNativeTypeB),
}

fn resolve_type_path(
    path: &ast::Path,
    env: &ModuleEnv<'_>,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<Option<ResolvedTypePath>, InternalCompilationError> {
    if let [(name, _)] = &path.segments[..] {
        if let Some(entry) = env.current.get_type_alias(ustr(name)).cloned() {
            return Ok(Some(ResolvedTypePath::Alias(entry)));
        }
        if let Some(type_def) = env.current.get_type_def_id(ustr(name)) {
            return Ok(Some(ResolvedTypePath::TypeDef(type_def)));
        }
        if let Some(bare) = env.current.get_bare_native_type_alias(ustr(name)) {
            return Ok(Some(ResolvedTypePath::BareNative(bare)));
        }
    }

    if let Some((module_id, entry)) = env.type_alias_with_module(path)? {
        record_module_use(module_id, modules_used);
        return Ok(Some(ResolvedTypePath::Alias(entry.clone())));
    }
    if let Some((module_id, type_def)) = env.type_def_with_module(path)? {
        record_module_use(module_id, modules_used);
        return Ok(Some(ResolvedTypePath::TypeDef(type_def)));
    }
    if let Some((module_id, bare)) = env.bare_native_type_alias_with_module(path)? {
        let type_name = path.segments.last().unwrap().0;
        if env.is_unsafe_item_unavailable_in_current_context(module_id, type_name) {
            return Err(
                InternalCompilationError::new_unsafe_feature_use_not_allowed(
                    UnsafeFeature::TypeAlias(type_name),
                    path.span().unwrap_or(Location::new_synthesized()),
                ),
            );
        }
        record_module_use(module_id, modules_used);
        return Ok(Some(ResolvedTypePath::BareNative(bare)));
    }

    Ok(None)
}

fn desugar_array_syntax_type(
    element: Type,
    current_module_id: ModuleId,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Type {
    if current_module_id != STD_MODULE_ID {
        modules_used.insert(STD_MODULE_ID);
    }
    array_type(element)
}

fn desugar_type_arguments(
    args: &[ast::TypeSpan<Parsed>],
    env: &ModuleEnv<'_>,
    generic_ty_params: &GenericTyParams,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<Vec<Type>, InternalCompilationError> {
    args.iter()
        .map(|(ty, ty_span)| {
            ty.desugar_with_ty_params(*ty_span, false, env, generic_ty_params, modules_used)
        })
        .collect()
}

fn expect_type_argument_count(
    expected: usize,
    expected_span: Location,
    got: usize,
    got_span: Location,
) -> Result<(), InternalCompilationError> {
    if expected == got {
        Ok(())
    } else {
        Err(internal_compilation_error!(WrongNumberOfArguments {
            expected,
            expected_span,
            got,
            got_span,
        }))
    }
}

fn desugar_resolved_type_without_args(
    resolved: ResolvedTypePath,
    path: &ast::Path,
    span: Location,
    env: &ModuleEnv<'_>,
) -> Result<Type, InternalCompilationError> {
    match resolved {
        ResolvedTypePath::Alias(entry) => {
            expect_type_argument_count(entry.param_count(), path.span().unwrap_or(span), 0, span)?;
            Ok(entry.ty)
        }
        ResolvedTypePath::TypeDef(type_def) => {
            expect_type_argument_count(
                env.type_def_param_names(type_def).len(),
                env.type_def_span(type_def),
                0,
                span,
            )?;
            Ok(Type::named(type_def, Vec::new()))
        }
        ResolvedTypePath::BareNative(bare) => Ok(Type::native_type(NativeType::new(bare, vec![]))),
    }
}

fn desugar_resolved_type_with_args(
    resolved: ResolvedTypePath,
    path: &ast::Path,
    args: Vec<Type>,
    span: Location,
    env: &ModuleEnv<'_>,
) -> Result<Type, InternalCompilationError> {
    match resolved {
        ResolvedTypePath::Alias(entry) => {
            expect_type_argument_count(
                entry.param_count(),
                path.span().unwrap_or(span),
                args.len(),
                span,
            )?;
            let ty_subst = (0..entry.ty_var_count)
                .map(TypeVar::new)
                .zip(args)
                .collect();
            Ok(instantiate_type(
                entry.ty,
                &(ty_subst, EffectsInstSubst::default()),
            ))
        }
        ResolvedTypePath::TypeDef(type_def) => {
            expect_type_argument_count(
                env.type_def_param_names(type_def).len(),
                env.type_def_span(type_def),
                args.len(),
                span,
            )?;
            Ok(Type::named(type_def, args))
        }
        ResolvedTypePath::BareNative(bare) => Ok(Type::native_type(NativeType::new(bare, args))),
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
        let generic_ty_params = if self.generic_params.is_empty() {
            self.for_trait
                .as_ref()
                .map(|for_trait| collect_trait_impl_generic_ty_params(for_trait, env))
                .transpose()?
                .unwrap_or_default()
        } else {
            extend_generic_ty_params(
                &GenericTyParams::default(),
                &self.generic_params,
                GenericParamsOwner::TraitImpl {
                    trait_name: self.trait_name.0,
                },
            )?
        };
        let fn_map = self
            .functions
            .iter()
            .enumerate()
            .map(|(index, func)| (func.name.0, index))
            .collect::<FxHashMap<_, _>>();
        let (functions, fn_dep_graph): (_, Vec<_>) = process_results(
            self.functions.into_iter().map(|f| {
                f.desugar_with_ty_params(
                    &fn_map,
                    env,
                    &generic_ty_params,
                    parsed_arena,
                    desugared_arena,
                    modules_used,
                )
            }),
            |iter| iter.unzip(),
        )?;
        let sccs = find_strongly_connected_components(&fn_dep_graph);
        let function_sccs =
            local_function_sccs(&fn_dep_graph, topological_sort_sccs(&fn_dep_graph, &sccs));
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
        let where_clause =
            desugar_type_constraints(&self.where_clause, &generic_ty_params, env, modules_used)?;
        Ok(DTraitImpl {
            span: self.span,
            generic_params: self.generic_params,
            trait_name: self.trait_name,
            for_trait,
            where_clause,
            associated_consts: self.associated_consts,
            functions,
            function_sccs,
        })
    }
}

fn local_function_sccs(fn_dep_graph: &[DepGraphNode], sccs: Vec<Vec<usize>>) -> FnSccs {
    sccs.into_iter()
        .map(|functions| {
            let recursive = functions.len() > 1
                || functions
                    .first()
                    .is_some_and(|index| fn_dep_graph[*index].0.contains(index));
            ast::FunctionScc {
                functions: functions
                    .into_iter()
                    .map(ast::FunctionAstIndex::new)
                    .collect(),
                recursive,
            }
        })
        .collect()
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
