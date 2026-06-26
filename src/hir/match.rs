// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    FxHashMap, Location,
    ast::{DExprId, PatternVar},
    compiler::error::DuplicatedVariantContext,
    hir::hir_syn::store_new_local,
    internal_compilation_error,
    module::{
        LocalDecl, LocalDeclId, LocalFrameSlot, ProjectionIndex, TypeDefId, TypeDefLookupResult,
        id::Id,
    },
    std::core_traits_names::REPR_TRAIT_NAME,
    types::mutability::MutVal,
    types::r#type::TypeKind,
};
use itertools::{Itertools, multiunzip};
use ustr::ustr;

use crate::{
    ast::{Pattern, PatternKind, PatternType},
    compiler::error::InternalCompilationError,
    containers::{SVec2, b},
    hir::value::LiteralValue,
    hir::{self, FieldAccess, LoadLocal, NodeId, NodeKind, Project, StoreLocal},
    std::math::int_type,
    types::effects::{EffType, no_effects},
    types::mutability::MutType,
    types::r#type::Type,
    types::type_inference::expr::TypeInference,
    types::type_scheme::PubTypeConstraint,
    types::typing_env::TypingEnv,
};

fn is_definitely_uninhabited(ty: Type, env: &TypingEnv) -> bool {
    fn go(ty: Type, env: &TypingEnv, seen: &mut Vec<Type>) -> bool {
        if seen.contains(&ty) {
            return false;
        }
        let kind = {
            let data = ty.data();
            match &*data {
                TypeKind::Never => return true,
                TypeKind::Variable(_)
                | TypeKind::Native(_)
                | TypeKind::Function(_)
                | TypeKind::Subscript(_) => return false,
                _ => data.clone(),
            }
        };

        seen.push(ty);
        let result = match kind {
            TypeKind::Tuple(fields) => fields.into_iter().any(|ty| go(ty, env, seen)),
            TypeKind::Record(fields) => fields.into_iter().any(|(_, ty)| go(ty, env, seen)),
            TypeKind::Variant(variants) => variants
                .into_iter()
                .all(|(_, payload)| go(payload, env, seen)),
            TypeKind::Named(named) => go(named.instantiated_shape(&env.module_env), env, seen),
            TypeKind::Never
            | TypeKind::Variable(_)
            | TypeKind::Native(_)
            | TypeKind::Function(_)
            | TypeKind::Subscript(_) => unreachable!(),
        };
        seen.pop();
        result
    }

    go(ty, env, &mut Vec::new())
}

impl TypeInference {
    fn fresh_named_type_instance(&mut self, type_def: TypeDefId, env: &TypingEnv) -> Type {
        let type_def_data = env.module_env.type_def(type_def);
        let param_count = type_def_data.param_count();
        let effect_param_count = type_def_data.effect_param_count();
        Type::named_with_effects(
            type_def,
            self.fresh_type_var_tys(param_count),
            (0..effect_param_count)
                .map(|_| self.fresh_effect_var_ty())
                .collect::<Vec<_>>(),
        )
    }

    fn named_enum_variant_tys_with_uninhabited_omissions(
        &self,
        condition_ty: Type,
        covered_payloads: &FxHashMap<ustr::Ustr, Type>,
        env: &TypingEnv,
    ) -> Option<Vec<(ustr::Ustr, Type)>> {
        let condition_data = condition_ty.data();
        let named = match &*condition_data {
            TypeKind::Named(named) => named.clone(),
            _ => return None,
        };
        drop(condition_data);
        let shape = named.instantiated_shape(&env.module_env);

        let shape_data = shape.data();
        let variants = match &*shape_data {
            TypeKind::Variant(variants) => variants.clone(),
            _ => return None,
        };
        drop(shape_data);

        let mut result = Vec::with_capacity(variants.len());
        for (tag, payload) in variants {
            if let Some(covered_payload) = covered_payloads.get(&tag) {
                result.push((tag, *covered_payload));
            } else if is_definitely_uninhabited(payload, env) {
                result.push((tag, payload));
            } else {
                return None;
            }
        }
        Some(result)
    }

    pub(crate) fn infer_match(
        &mut self,
        env: &mut TypingEnv,
        match_span: Location,
        cond_expr: DExprId,
        alternatives: &[(Pattern, DExprId)],
        default: &Option<DExprId>,
    ) -> Result<(NodeKind, Type, MutType, EffType), InternalCompilationError> {
        use hir::Node as N;
        use hir::NodeKind as K;

        let sp = |id: DExprId| env.ast_arena[id].span;

        // Do we have a degenerate match with no alternative?
        if alternatives.is_empty() {
            if let Some(default) = default {
                let (node_id, mut_ty) = self.infer_expr(env, *default)?;
                let node = &env.ir_arena[node_id];
                let kind = node.kind.clone();
                let ty = node.ty;
                let effects = node.effects.clone();
                return Ok((kind, ty, mut_ty, effects));
            } else {
                let (condition_node_id, _) = self.infer_expr(env, cond_expr)?;
                let condition_node = &env.ir_arena[condition_node_id];
                let cond_eff = condition_node.effects.clone();
                if is_definitely_uninhabited(condition_node.ty, env) {
                    return Ok(self.diverging_prefix_result(env, [condition_node_id], cond_eff));
                }
                return Err(internal_compilation_error!(EmptyMatchBody {
                    span: match_span
                }));
            }
        }

        // Infer the condition expression and get the pattern type.
        // Currently the type must be the same for all alternatives.
        let (condition_node_id, _) = self.infer_expr(env, cond_expr)?;
        let condition_node = &env.ir_arena[condition_node_id];
        let condition_ty = condition_node.ty;
        let condition_span = condition_node.span;
        let cond_eff = condition_node.effects.clone();
        if is_definitely_uninhabited(condition_node.ty, env) {
            return Ok(self.diverging_prefix_result(env, [condition_node_id], cond_eff));
        }

        // Generate a repr projection to get a condition_node.ty: Repr<Is = U> type
        let pattern_ty = self.fresh_type_var_ty(); // U
        self.add_pub_constraint(PubTypeConstraint::new_have_trait(
            env.module_env.expect_std_trait_id(REPR_TRAIT_NAME),
            vec![condition_node.ty],
            vec![pattern_ty],
            vec![],
            condition_node.span,
        ));

        let first_alternative = alternatives.first().unwrap();
        let first_alternative_span = first_alternative.0.span;
        let is_variant = first_alternative.0.kind.is_variant();
        let alternatives_span = Location::fuse([
            alternatives.first().unwrap().0.span,
            sp(alternatives.last().unwrap().1),
        ])
        .unwrap();

        Ok(if is_variant {
            // Variant patterns
            let initial_env_size = env.cur_locals.len();
            let match_condition_slot = env.all_locals.len();

            // Create a fresh type variable for the inner types, when there is a variable binding.
            let mut seen_tags = FxHashMap::default();
            let mut qualified_pattern_tys = FxHashMap::default();
            let (types, exprs): (Vec<_>, Vec<_>) = alternatives
                .iter()
                .map(|(pattern, expr)| {
                    if let Some(variant) = pattern.kind.as_variant() {
                        let (path, kind, vars) = variant;
                        let (tag, tag_span) = path.tag();
                        if path.is_qualified() {
                            let path_span = path.path.span().unwrap_or(pattern.span);
                            match env.get_type_def(&path.path)? {
                                Some(TypeDefLookupResult::Enum(type_def, resolved_tag)) => {
                                    debug_assert_eq!(tag, resolved_tag);
                                    let named_ty =
                                        if let Some(ty) = qualified_pattern_tys.get(&type_def) {
                                            *ty
                                        } else {
                                            let ty = self.fresh_named_type_instance(type_def, env);
                                            qualified_pattern_tys.insert(type_def, ty);
                                            ty
                                        };
                                    self.add_sub_type_constraint(
                                        condition_ty,
                                        condition_span,
                                        named_ty,
                                        path_span,
                                    );
                                }
                                Some(TypeDefLookupResult::Struct(_)) | None => {
                                    return Err(internal_compilation_error!(
                                        InvalidVariantConstructor { span: path_span }
                                    ));
                                }
                            }
                        }
                        // Detect duplicate variant tags.
                        if let Some(old_tag_span) = seen_tags.insert(tag, tag_span) {
                            return Err(internal_compilation_error!(DuplicatedVariant {
                                first_occurrence: old_tag_span,
                                second_occurrence: tag_span,
                                ctx_span: match_span,
                                ctx: DuplicatedVariantContext::Match,
                            }));
                        }
                        // Detect invalid wildcard and duplicate variable names in the pattern.
                        let mut seen_identifier = FxHashMap::default();
                        let mut has_wildcard = false;
                        let named_vars = vars
                            .iter()
                            .enumerate()
                            .filter_map(|(i, var)| {
                                use PatternVar::*;
                                let (var, span) = match var {
                                    Named(named) => named,
                                    Wildcard(span) => {
                                        if kind.is_tuple() {
                                            return Some(Err(
                                                internal_compilation_error!(Unsupported {
                                            reason: "Wildcard .. not supported in tuple patterns"
                                                .into(),
                                            span: *span,
                                        }),
                                            ));
                                        }
                                        if i != vars.len() - 1 {
                                            return Some(Err(internal_compilation_error!(
                                                RecordWildcardPatternNotAtEnd {
                                                    pattern_span: pattern.span,
                                                    wildcard_span: *span
                                                }
                                            )));
                                        }
                                        has_wildcard = true;
                                        return None;
                                    }
                                };
                                if let Some(old_span) = seen_identifier.insert(*var, *span) {
                                    return Some(Err(internal_compilation_error!(
                                        IdentifierBoundMoreThanOnceInAPattern {
                                            first_occurrence: old_span,
                                            second_occurrence: *span,
                                            pattern_span: pattern.span,
                                        }
                                    )));
                                }
                                Some(Ok((*var, *span)))
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        // Process the inner types
                        let (inner_tys, variant_inner_ty) = match named_vars.len() {
                            0 => (vec![], Type::unit()),
                            n => {
                                let inner_tys = self.fresh_type_var_tys(n);
                                let variant_inner_ty = if kind.is_tuple() {
                                    // tuple variant
                                    Type::tuple(inner_tys.clone())
                                } else {
                                    // record variant
                                    if has_wildcard {
                                        // Note: having a type variable as inner type will mark that we have an incomplete record.
                                        let variant_inner_ty = self.fresh_type_var_ty();
                                        for ((name, span), ty) in
                                            named_vars.iter().zip(inner_tys.iter())
                                        {
                                            self.add_pub_constraint(
                                                PubTypeConstraint::new_record_field_is(
                                                    variant_inner_ty,
                                                    pattern.span,
                                                    *name,
                                                    *span,
                                                    *ty,
                                                ),
                                            );
                                        }
                                        variant_inner_ty
                                    } else {
                                        let fields = named_vars
                                            .iter()
                                            .zip(inner_tys.iter())
                                            .map(|((name, _), ty)| (*name, *ty))
                                            .collect::<Vec<_>>();
                                        Type::record(fields)
                                    }
                                };
                                (inner_tys, variant_inner_ty)
                            }
                        };
                        Ok(((tag, inner_tys, variant_inner_ty), (expr, named_vars)))
                    } else {
                        Err(internal_compilation_error!(InconsistentPattern {
                            a_type: PatternType::Variant,
                            a_span: first_alternative_span,
                            b_type: pattern.kind.r#type(),
                            b_span: pattern.span,
                        }))
                    }
                })
                .process_results(|iter| iter.unzip())?;

            // Code to store the variant value in the environment.
            let (store_variant, l_match_condition) = store_new_local(
                condition_node_id,
                match_condition_slot,
                "@match_condition",
                MutVal::constant(),
                pattern_ty,
                env.all_locals,
            );
            self.set_local_owned_storage_from_value(
                env,
                l_match_condition,
                condition_node_id,
                pattern_ty,
                match_span,
            );
            let store_variant_node_id = env.ir_arena.alloc(N::new(
                store_variant,
                Type::unit(),
                cond_eff.clone(),
                sp(cond_expr),
            ));
            env.cur_locals.push(l_match_condition);

            // Code to load the variant local and extract the tag.

            let load_variant_node = N::new(
                K::LoadLocal(LoadLocal {
                    id: l_match_condition,
                }),
                pattern_ty,
                no_effects(),
                sp(cond_expr),
            );
            let load_variant_id = env.ir_arena.alloc(load_variant_node.clone());
            let extract_tag_id = env.ir_arena.alloc(N::new(
                K::ExtractTag(load_variant_id),
                int_type(),
                no_effects(),
                sp(cond_expr),
            ));

            // Variant branches should share a fresh result type, like literal matches do.
            // Otherwise a leading `never` branch can lock the whole match to `never`
            // before later branches get a chance to constrain the result.
            let return_ty = self.fresh_type_var_ty();
            let mut alternatives = types
                .iter()
                .zip(exprs)
                .map(
                    |((tag, inner_tys, variant_inner_ty), (expr, bind_var_names))| {
                        let tag_value = LiteralValue::new_native(tag.as_char_ptr() as isize);

                        // Prepare the environment for the alternative by adapting the type of the variant value
                        let alt_start_env_size = env.cur_locals.len();
                        assert_eq!(inner_tys.len(), bind_var_names.len());
                        let l_bindings: Vec<_> = bind_var_names
                            .iter()
                            .zip(inner_tys.iter())
                            .map(|(name, inner_ty)| {
                                let id = LocalDeclId::from_index(env.all_locals.len());
                                let mut local = LocalDecl::new(
                                    *name,
                                    MutType::constant(),
                                    *inner_ty,
                                    None,
                                    sp(*expr),
                                );
                                local.slot = LocalFrameSlot::from_index(id.as_index());
                                env.all_locals.push(local);
                                env.cur_locals.push(id);
                                id
                            })
                            .collect();

                        // Type check the alternative and generate its code
                        let mut node_id = self.check_expr(
                            env,
                            *expr,
                            return_ty,
                            MutType::constant(),
                            match_span,
                        )?;
                        node_id = self.materialize_owned_value(env, node_id, match_span);
                        self.add_same_type_constraint(
                            env.ir_arena[node_id].ty,
                            sp(*expr),
                            return_ty,
                            match_span,
                        );

                        // Generate the variable binding code
                        if !bind_var_names.is_empty() {
                            let mut project_node_ids = Vec::new();
                            for i in 0..inner_tys.len() {
                                let load_variant_id_inner =
                                    env.ir_arena.alloc(load_variant_node.clone());
                                let project_variant_inner_id = env.ir_arena.alloc(N::new(
                                    K::Project(Project::new(
                                        load_variant_id_inner,
                                        ProjectionIndex::from_index(0),
                                    )),
                                    *variant_inner_ty,
                                    no_effects(),
                                    sp(*expr),
                                ));
                                let inner_ty = inner_tys[i];
                                let project_index = if variant_inner_ty.data().is_tuple() {
                                    Some(i)
                                } else if let TypeKind::Record(record) = &*variant_inner_ty.data() {
                                    let index = record
                                        .iter()
                                        .position(|(name, _)| *name == bind_var_names[i].0)
                                        .expect("Expected record field to be present");
                                    Some(index)
                                } else {
                                    // If it is a variable type, we have no index and will emit FieldAccess instead
                                    None
                                };
                                let project_inner_kind = if let Some(index) = project_index {
                                    K::Project(Project::new(
                                        project_variant_inner_id,
                                        ProjectionIndex::from_index(index),
                                    ))
                                } else {
                                    K::FieldAccess(FieldAccess::new(
                                        project_variant_inner_id,
                                        bind_var_names[i].0,
                                    ))
                                };
                                let project_inner_id = env.ir_arena.alloc(N::new(
                                    project_inner_kind,
                                    inner_ty,
                                    no_effects(),
                                    sp(*expr),
                                ));
                                self.set_local_owned_storage_from_value(
                                    env,
                                    l_bindings[i],
                                    project_inner_id,
                                    inner_ty,
                                    sp(*expr),
                                );
                                let store_projected_inner_id = env.ir_arena.alloc(N::new(
                                    K::StoreLocal(StoreLocal {
                                        value: project_inner_id,
                                        id: l_bindings[i],
                                    }),
                                    Type::unit(),
                                    no_effects(),
                                    sp(*expr),
                                ));
                                project_node_ids.push(store_projected_inner_id);
                            }
                            project_node_ids.push(node_id);
                            let proj_effects = self.make_dependent_effect(
                                project_node_ids
                                    .iter()
                                    .map(|id| &env.ir_arena[*id].effects)
                                    .collect::<Vec<_>>(),
                            );
                            node_id = env.ir_arena.alloc(N::new(
                                K::Block(b(hir::Block {
                                    body: b(SVec2::from_vec(project_node_ids)),
                                    cleanup: Vec::new(),
                                })),
                                return_ty,
                                proj_effects,
                                sp(*expr),
                            ));
                        }
                        assert!(env.cur_locals.len() == alt_start_env_size + bind_var_names.len());
                        env.cur_locals.truncate(alt_start_env_size);
                        Result::<_, InternalCompilationError>::Ok((tag_value, node_id))
                    },
                )
                .collect::<Result<Vec<_>, _>>()?;
            let alt_eff = self.make_dependent_effect(
                alternatives
                    .iter()
                    .map(|(_, id)| &env.ir_arena[*id].effects)
                    .collect::<Vec<_>>(),
            );

            // Do we have a default?
            let default = if let Some(default) = default {
                // Yes, so the pattern_ty is our type and we add constraints towards it.
                for (tag, _, variant_inner_ty) in types {
                    self.add_pub_constraint(PubTypeConstraint::new_type_has_variant(
                        pattern_ty,
                        sp(cond_expr),
                        tag,
                        variant_inner_ty,
                        alternatives_span,
                    ));
                }

                // Generate the default code node
                let default_id =
                    self.check_expr(env, *default, return_ty, MutType::constant(), match_span)?;
                let default_id = self.materialize_owned_value(env, default_id, match_span);
                self.add_same_type_constraint(
                    env.ir_arena[default_id].ty,
                    sp(*default),
                    return_ty,
                    match_span,
                );
                default_id
            } else {
                // No default, compute a full variant type.
                let variant_inner_tys: Vec<_> =
                    types.into_iter().map(|(tag, _, ty)| (tag, ty)).collect();
                let covered_payloads = FxHashMap::from_iter(variant_inner_tys.iter().copied());
                let variant_inner_tys = self
                    .named_enum_variant_tys_with_uninhabited_omissions(
                        condition_ty,
                        &covered_payloads,
                        env,
                    )
                    .unwrap_or(variant_inner_tys);
                let variant_ty = Type::variant(variant_inner_tys);
                self.add_sub_type_constraint(
                    pattern_ty,
                    sp(cond_expr),
                    variant_ty,
                    alternatives_span,
                );

                // Generate the default code node
                alternatives
                    .drain(alternatives.len() - 1..)
                    .next()
                    .unwrap()
                    .1
            };
            env.cur_locals.truncate(initial_env_size);

            // Generate the final code node
            let default_eff = env.ir_arena[default].effects.clone();
            let case_eff = self.make_dependent_effect([&alt_eff, &default_eff]);
            let case_ret_ty = if Self::case_arms_all_never(env, &alternatives, default) {
                Type::never()
            } else {
                return_ty
            };
            let case = K::Case(b(hir::Case {
                value: extract_tag_id,
                alternatives,
                default,
            }));
            let case_node_id = env
                .ir_arena
                .alloc(N::new(case, case_ret_ty, case_eff, match_span));
            let store_eff = &env.ir_arena[store_variant_node_id].effects;
            let case_node_eff = &env.ir_arena[case_node_id].effects;
            let effects = self.make_dependent_effect([store_eff, case_node_eff]);
            let node = K::Block(b(hir::Block {
                body: b(SVec2::from_vec(vec![store_variant_node_id, case_node_id])),
                // The materialized scrutinee is an owned local; drop it when the block exits or a
                // resource-owning scrutinee leaks (a `Skip`-drop one resolves to no drop).
                cleanup: vec![l_match_condition],
            }));
            (node, case_ret_ty, MutType::constant(), effects)
        } else {
            // Literal patterns, convert optional default to mandatory one
            let return_ty = self.fresh_type_var_ty();
            let (alternatives, default_id, effects) = if let Some(default) = default {
                let default_id =
                    self.check_expr(env, *default, return_ty, MutType::constant(), match_span)?;
                let default_id = self.materialize_owned_value(env, default_id, match_span);
                self.add_same_type_constraint(
                    env.ir_arena[default_id].ty,
                    sp(*default),
                    return_ty,
                    match_span,
                );
                let (alternatives, alt_eff) = self.check_literal_patterns(
                    env,
                    alternatives,
                    first_alternative_span,
                    pattern_ty,
                    sp(cond_expr),
                    return_ty,
                    match_span,
                )?;
                let default_eff = &env.ir_arena[default_id].effects;
                let effects = self.make_dependent_effect([&cond_eff, &alt_eff, default_eff]);
                (alternatives, default_id, effects)
            } else {
                let (mut alternatives, alt_eff) = self.check_literal_patterns(
                    env,
                    alternatives,
                    first_alternative_span,
                    pattern_ty,
                    sp(cond_expr),
                    return_ty,
                    match_span,
                )?;
                self.add_ty_coverage_constraint(
                    match_span,
                    pattern_ty,
                    alternatives.iter().map(|(v, _)| v.clone()).collect(),
                );
                let effects = self.make_dependent_effect([cond_eff, alt_eff]);
                let default_id = alternatives.pop().unwrap().1;
                (alternatives, default_id, effects)
            };

            // Materialize the scrutinee if needed.
            let (kind, case_ty, case_effects) = self.consume_value_by_shared_ref(
                env,
                condition_node_id,
                condition_ty,
                match_span,
                ustr("$match_scrutinee"),
                move |_this, env, scrutinee| {
                    let case_ret_ty = if Self::case_arms_all_never(env, &alternatives, default_id) {
                        Type::never()
                    } else {
                        return_ty
                    };
                    (
                        K::Case(b(hir::Case {
                            value: scrutinee,
                            alternatives,
                            default: default_id,
                        })),
                        case_ret_ty,
                        effects,
                    )
                },
            );
            (kind, case_ty, MutType::constant(), case_effects)
        })
    }

    fn case_arms_all_never<V>(
        env: &TypingEnv,
        alternatives: &[(V, NodeId)],
        default: NodeId,
    ) -> bool {
        alternatives
            .iter()
            .all(|(_, node_id)| env.ir_arena[*node_id].ty == Type::never())
            && env.ir_arena[default].ty == Type::never()
    }

    #[allow(clippy::too_many_arguments)]
    fn check_literal_patterns(
        &mut self,
        env: &mut TypingEnv,
        pairs: &[(Pattern, DExprId)],
        first_pattern_span: Location,
        expected_pattern_type: Type,
        expected_pattern_span: Location,
        expected_return_type: Type,
        expected_return_span: Location,
    ) -> Result<(Vec<(LiteralValue, NodeId)>, EffType), InternalCompilationError> {
        let mut seen_values = FxHashMap::default();
        let (pairs, effects): (Vec<_>, Vec<_>) = pairs
            .iter()
            .map(|(pattern, expr)| {
                if let PatternKind::Literal(literal, ty) = &pattern.kind {
                    if let Some(previous_span) = seen_values.get(literal) {
                        return Err(internal_compilation_error!(DuplicatedLiteralPattern {
                            first_occurrence: *previous_span,
                            second_occurrence: pattern.span,
                            match_span: expected_return_span,
                        }));
                    }
                    seen_values.insert(literal.clone(), pattern.span);
                    self.add_sub_type_constraint(
                        *ty,
                        pattern.span,
                        expected_pattern_type,
                        expected_pattern_span,
                    );
                    let node_id = self.check_expr(
                        env,
                        *expr,
                        expected_return_type,
                        MutType::constant(),
                        expected_return_span,
                    )?;
                    let node_id = self.materialize_owned_value(env, node_id, expected_return_span);
                    self.add_same_type_constraint(
                        env.ir_arena[node_id].ty,
                        env.ast_arena[*expr].span,
                        expected_return_type,
                        expected_return_span,
                    );
                    let effects = env.ir_arena[node_id].effects.clone();
                    Ok(((literal.clone(), node_id), effects))
                } else {
                    Err(internal_compilation_error!(InconsistentPattern {
                        a_type: PatternType::Literal,
                        a_span: first_pattern_span,
                        b_type: pattern.kind.r#type(),
                        b_span: env.ast_arena[*expr].span,
                    }))
                }
            })
            .process_results(|iter| multiunzip(iter))?;
        let effects = self.make_dependent_effect(&effects);
        Ok((pairs, effects))
    }
}
