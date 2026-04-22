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
    error::DuplicatedVariantContext,
    internal_compilation_error,
    ir_syn::store_new,
    module::{LocalDecl, LocalDeclId, id::Id},
    mutability::MutVal,
    std::core::REPR_TRAIT,
    r#type::TypeKind,
};
use itertools::{Itertools, multiunzip};

use crate::{
    ast::{Pattern, PatternKind, PatternType},
    containers::{SVec2, b},
    effects::{EffType, no_effects},
    error::InternalCompilationError,
    ir::{self, EnvLoad, EnvStore, NodeId, NodeKind},
    mutability::MutType,
    std::math::int_type,
    r#type::Type,
    type_inference::TypeInference,
    type_scheme::PubTypeConstraint,
    typing_env::TypingEnv,
    value::LiteralValue,
};

impl TypeInference {
    pub(crate) fn infer_match(
        &mut self,
        env: &mut TypingEnv,
        match_span: Location,
        cond_expr: DExprId,
        alternatives: &[(Pattern, DExprId)],
        default: &Option<DExprId>,
    ) -> Result<(NodeKind, Type, MutType, EffType), InternalCompilationError> {
        use ir::Node as N;
        use ir::NodeKind as K;

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
                return Err(internal_compilation_error!(EmptyMatchBody {
                    span: match_span
                }));
            }
        }

        // Infer the condition expression and get the pattern type.
        // Currently the type must be the same for all alternatives.
        let (condition_node_id, _) = self.infer_expr(env, cond_expr)?;
        let condition_node = &env.ir_arena[condition_node_id];
        let cond_eff = condition_node.effects.clone();
        if condition_node.ty == Type::never() {
            return Ok(Self::diverging_prefix_result([condition_node_id], cond_eff));
        }

        // Generate a repr projection to get a condition_node.ty: Repr<Is = U> type
        let pattern_ty = self.fresh_type_var_ty(); // U
        self.add_pub_constraint(PubTypeConstraint::new_have_trait(
            REPR_TRAIT.clone(),
            vec![condition_node.ty],
            vec![pattern_ty],
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

            // Create a fresh type variable for the inner types, when there is a variable binding.
            let mut seen_tags = FxHashMap::default();
            let (types, exprs): (Vec<_>, Vec<_>) = alternatives
                .iter()
                .map(|(pattern, expr)| {
                    if let Some(variant) = pattern.kind.as_variant() {
                        let ((tag, tag_span), kind, vars) = variant;
                        // Detect duplicate variant tags.
                        if let Some(old_tag_span) = seen_tags.insert(tag, tag_span) {
                            return Err(internal_compilation_error!(DuplicatedVariant {
                                first_occurrence: *old_tag_span,
                                second_occurrence: *tag_span,
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
                        Ok(((*tag, inner_tys, variant_inner_ty), (expr, named_vars)))
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
            let (store_variant, l_match_condition) = store_new(
                condition_node_id,
                initial_env_size,
                "@match_condition",
                MutVal::constant(),
                pattern_ty,
                env.all_locals,
            );
            let store_variant_node_id = env.ir_arena.alloc(N::new(
                store_variant,
                Type::unit(),
                cond_eff.clone(),
                sp(cond_expr),
            ));
            env.cur_locals.push(l_match_condition);

            // Code to load the variant and extract the tag

            let load_variant_node = N::new(
                K::EnvLoad(EnvLoad {
                    index: initial_env_size as u32,
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
                                env.all_locals.push(LocalDecl::new(
                                    *name,
                                    MutType::constant(),
                                    *inner_ty,
                                    None,
                                    sp(*expr),
                                ));
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

                        // Generate the variable binding code
                        if !bind_var_names.is_empty() {
                            let mut project_node_ids = Vec::new();
                            for i in 0..inner_tys.len() {
                                let load_variant_id_inner =
                                    env.ir_arena.alloc(load_variant_node.clone());
                                let project_variant_inner_id = env.ir_arena.alloc(N::new(
                                    K::Project(load_variant_id_inner, 0),
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
                                    K::Project(project_variant_inner_id, index)
                                } else {
                                    K::FieldAccess(project_variant_inner_id, bind_var_names[i].0)
                                };
                                let project_inner_id = env.ir_arena.alloc(N::new(
                                    project_inner_kind,
                                    inner_ty,
                                    no_effects(),
                                    sp(*expr),
                                ));
                                let store_projected_inner_id = env.ir_arena.alloc(N::new(
                                    K::EnvStore(EnvStore {
                                        value: project_inner_id,
                                        index: (alt_start_env_size + i) as u32,
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
                                K::Block(b(SVec2::from_vec(project_node_ids))),
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
                self.check_expr(env, *default, return_ty, MutType::constant(), match_span)?
            } else {
                // No default, compute a full variant type.
                let variant_inner_tys: Vec<_> =
                    types.into_iter().map(|(tag, _, ty)| (tag, ty)).collect();
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
            let case = K::Case(b(ir::Case {
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
            let node = K::Block(b(SVec2::from_vec(vec![
                store_variant_node_id,
                case_node_id,
            ])));
            (node, case_ret_ty, MutType::constant(), effects)
        } else {
            // Literal patterns, convert optional default to mandatory one
            let return_ty = self.fresh_type_var_ty();
            let (alternatives, default_id, effects) = if let Some(default) = default {
                let default_id =
                    self.check_expr(env, *default, return_ty, MutType::constant(), match_span)?;
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
            let case_ret_ty = if Self::case_arms_all_never(env, &alternatives, default_id) {
                Type::never()
            } else {
                return_ty
            };
            let node = K::Case(b(ir::Case {
                value: condition_node_id,
                alternatives,
                default: default_id,
            }));
            (node, case_ret_ty, MutType::constant(), effects)
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
