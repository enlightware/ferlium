use crate::desugar::types::{desugar_type_constraints, extend_generic_ty_params};
use crate::function::FunctionDefinition;
use crate::r#trait::{Trait, TraitFunctionSpans, TraitRef, TraitSpans, TraitValidationError};

use super::expr::desugar;
use super::*;

/// A reference to name of a type, either an alias or a definition, in parsed AST.
enum NamedTypeData {
    Alias(UstrSpan, Vec<UstrSpan>, PTypeSpan),
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
            Alias(name, _, alias) => alias.0.collect_refs(name.0, ty_names, collected),
            Def(def) => {
                def.shape.collect_refs(def.name.0, ty_names, collected)?;
                def.where_clause.iter().try_for_each(|constraint| {
                    constraint.collect_refs(def.name.0, ty_names, collected)
                })
            }
        }
    }
    fn name(&self) -> Ustr {
        use NamedTypeData::*;
        match self {
            Alias(name, _, _) => name.0,
            Def(def) => def.name.0,
        }
    }
    fn name_span(&self) -> Location {
        use NamedTypeData::*;
        match self {
            Alias(name, _, _) => name.1,
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
        let PModule {
            traits,
            functions,
            impls,
            type_aliases,
            type_defs,
            uses,
        } = self;

        let resolver = ModulesResolver::new(others);
        resolve_imports(&uses, &local_names, &resolver, &mut output.uses)?;

        // Build a map of type names to their location and definitions or aliases.
        // The ty_names map holds indices to the ty_refs vector, which contains the data.
        let (ty_names, ty_refs): (FxHashMap<_, _>, Vec<_>) = type_aliases
            .into_iter()
            .map(|alias| {
                (
                    alias.name.0,
                    NamedTypeData::Alias(alias.name, alias.generic_params, alias.ty),
                )
            })
            .chain(
                type_defs
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
                NamedTypeData::Alias(name, generic_params, alias) => {
                    let generic_ty_params = extend_generic_ty_params(
                        &GenericTyParams::default(),
                        generic_params,
                        GenericParamsOwner::TypeAlias { name: name.0 },
                    )?;
                    let ty_var_count = generic_params.len() as u32;
                    let param_names: Vec<_> =
                        generic_params.iter().map(|(name, _)| *name).collect();
                    let ty = alias.0.desugar_with_ty_params(
                        alias.1,
                        false,
                        &env,
                        &generic_ty_params,
                        &mut modules_used,
                    )?;
                    output.add_type_alias(name.0, param_names, ty_var_count, ty);
                }
                NamedTypeData::Def(def) => {
                    output.add_type_def(def.name.0, def.desugar(&env, &mut modules_used)?);
                }
            }
            env = ModuleEnv::new(output, others);
        }

        for trait_def in traits {
            output.add_trait(trait_def.desugar(&env, &mut modules_used)?);
            env = ModuleEnv::new(output, others);
        }

        // Desugar functions
        let fn_map = functions
            .iter()
            .enumerate()
            .map(|(index, func)| (func.name.0, index))
            .collect::<FxHashMap<_, _>>();
        let mut desugared_arena = new_desugared_arena_sized_from_parsed_arena(parsed_arena);
        let (functions, fn_dep_graph): (_, Vec<_>) = process_results(
            functions.into_iter().map(|f| {
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
        let impls = impls
            .into_iter()
            .map(|i| i.desugar(&env, parsed_arena, &mut desugared_arena, &mut modules_used))
            .collect::<Result<_, _>>()?;

        // Build result
        output.type_deps.extend(modules_used);
        let module = DModule {
            traits: vec![],
            functions,
            impls,
            type_aliases: vec![],
            type_defs: vec![],
            uses,
        };
        Ok((module, desugared_arena, sorted_sccs))
    }
}

impl ast::TraitDefinition {
    pub fn desugar(
        self,
        env: &ModuleEnv<'_>,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<TraitRef, InternalCompilationError> {
        let generic_params = self
            .input_type_names
            .iter()
            .chain(self.output_type_names.iter())
            .copied()
            .collect::<Vec<_>>();
        let generic_ty_params = extend_generic_ty_params(
            &GenericTyParams::default(),
            &generic_params,
            GenericParamsOwner::Trait { name: self.name.0 },
        )?;
        let constraints =
            desugar_type_constraints(&self.where_clause, &generic_ty_params, env, modules_used)?;
        let function_spans = self
            .functions
            .iter()
            .map(|function| function.spans())
            .collect();
        let spans = self.spans(function_spans);
        let input_type_names = self.iter_input_type_names().collect();
        let output_type_names = self.iter_output_type_names().collect();
        let functions = self
            .functions
            .into_iter()
            .map(|function| function.desugar(env, &generic_ty_params, modules_used))
            .collect::<Result<Vec<_>, _>>()?;
        let trait_span = self.span;
        TraitRef::from_trait_data(Trait {
            name: self.name.0,
            doc: self.doc,
            input_type_names,
            output_type_names,
            constraints,
            functions,
            derives: vec![],
            spans: Some(spans),
        })
        .map_err(|error| match error {
            TraitValidationError::Invalid { trait_name, kind } => {
                internal_compilation_error!(InvalidTraitDefinition {
                    trait_name,
                    kind,
                    span: trait_span,
                })
            }
            TraitValidationError::Unsupported { trait_name, kind } => {
                internal_compilation_error!(UnsupportedTraitDefinition {
                    trait_name,
                    kind,
                    span: trait_span,
                })
            }
        })
    }
}

impl ast::TraitFunction {
    fn spans(&self) -> TraitFunctionSpans {
        TraitFunctionSpans {
            name: self.name.1,
            args: self
                .args
                .iter()
                .map(|arg| (arg.name.1, arg.ty.span))
                .collect(),
            ret_ty: self.ret_ty.as_ref().map(|(_, span)| *span),
            span: self.span,
        }
    }

    fn desugar(
        self,
        env: &ModuleEnv<'_>,
        generic_ty_params: &GenericTyParams,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<(Ustr, FunctionDefinition), InternalCompilationError> {
        let args = self
            .args
            .iter()
            .map(|arg| {
                arg.ty
                    .desugar_with_ty_params(env, generic_ty_params, modules_used)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let ret = self.ret_ty.map_or_else(
            || Ok(Type::unit()),
            |(ret_ty, span)| {
                ret_ty.desugar_with_ty_params(span, false, env, generic_ty_params, modules_used)
            },
        )?;
        use ast::PFnEffects::*;
        let effects = match self.effects {
            ImplicitPure => EffType::empty(),
            ImplicitGeneric => EffType::single_variable_id(0),
            Explicit(effects) => EffType::multiple_primitive(&effects),
        };
        let fn_ty = FnType::new(args, ret, effects);
        Ok((
            self.name.0,
            FunctionDefinition::new(
                TypeScheme::new_infer_quantifiers(fn_ty),
                self.args.into_iter().map(|arg| arg.name.0).collect(),
                self.doc,
            ),
        ))
    }
}

impl ast::TraitDefinition {
    fn spans(&self, functions: Vec<TraitFunctionSpans>) -> TraitSpans {
        TraitSpans {
            name: self.name.1,
            input_type_names: self
                .input_type_names
                .iter()
                .map(|(_, span)| *span)
                .collect(),
            output_type_names: self
                .output_type_names
                .iter()
                .map(|(_, span)| *span)
                .collect(),
            constraints: self
                .where_clause
                .iter()
                .map(|constraint| constraint.span)
                .collect(),
            functions,
            span: self.span,
        }
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
        let generic_ty_params = GenericTyParams::default();
        self.desugar_with_ty_params(
            fn_map,
            env,
            &generic_ty_params,
            parsed_arena,
            desugared_arena,
            modules_used,
        )
    }

    pub(crate) fn desugar_with_ty_params(
        self,
        fn_map: &FnMap,
        env: &ModuleEnv<'_>,
        generic_ty_params: &GenericTyParams,
        parsed_arena: &PExprArena,
        desugared_arena: &mut DExprArena,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<(DModuleFunction, DepGraphNode), InternalCompilationError> {
        let generic_ty_params = extend_generic_ty_params(
            generic_ty_params,
            &self.generic_params,
            GenericParamsOwner::Function { name: self.name.0 },
        )?;
        // Collect mut-binding arg info before args are consumed.
        let mut_binding_args: Vec<UstrSpan> = self
            .args
            .iter()
            .filter(|arg| arg.mut_binding)
            .map(|arg| arg.name)
            .collect();
        let locals = self.args.iter().map(|arg| arg.name.0).collect();
        let mut ctx = DesugarCtx::new_with_locals(fn_map, locals, env, &generic_ty_params);
        let body = desugar(
            self.body,
            &mut ctx,
            parsed_arena,
            desugared_arena,
            modules_used,
        )?;
        // Desugar `mut x` parameters by prepending `let mut x = x;` to the body.
        // This rebinds each such parameter as a mutable local, shadowing the immutable arg,
        // without changing the function's external signature.
        let body = if mut_binding_args.is_empty() {
            body
        } else {
            let body_span = desugared_arena[body].span;
            let mut stmts: Vec<DExprId> = Vec::with_capacity(mut_binding_args.len() + 1);
            for name in &mut_binding_args {
                let span = name.1;
                let arg_ref = desugared_arena.alloc(DExpr::new(
                    ExprKind::identifier(Path::single(name.0, span)),
                    span,
                ));
                let let_mut = desugared_arena.alloc(DExpr::new(
                    ExprKind::let_(
                        DLetPattern::binding(*name, MutVal::mutable()),
                        arg_ref,
                        None,
                    ),
                    span,
                ));
                stmts.push(let_mut);
            }
            stmts.push(body);
            desugared_arena.alloc(DExpr::new(ExprKind::block(stmts), body_span))
        };
        let args = self
            .args
            .into_iter()
            .map(|arg| arg.desugar_with_ty_params(env, &generic_ty_params, modules_used))
            .collect::<Result<Vec<_>, _>>()?;
        // Collect function dependencies
        let ret_ty = self
            .ret_ty
            .map(|(ty, span)| {
                Ok((
                    ty.desugar_with_ty_params(span, false, env, &generic_ty_params, modules_used)?,
                    span,
                ))
            })
            .transpose()?;
        let where_clause =
            desugar_type_constraints(&self.where_clause, &generic_ty_params, env, modules_used)?;
        let function = ModuleFunction {
            name: self.name,
            generic_params: self.generic_params,
            args,
            args_span: self.args_span,
            ret_ty,
            where_clause,
            body,
            span: self.span,
            doc: self.doc,
        };
        let deps = DepGraphNode(ctx.fn_deps.into_iter().collect());
        Ok((function, deps))
    }
}
