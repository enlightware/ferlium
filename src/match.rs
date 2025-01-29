// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::collections::HashMap;

use crate::{internal_compilation_error, Location};
use itertools::{multiunzip, Itertools};
use ustr::ustr;

use crate::{
    ast::{DExpr, Pattern, PatternKind, PatternType},
    containers::{b, SVec2},
    effects::{no_effects, EffType},
    error::InternalCompilationError,
    ir::{self, EnvLoad, EnvStore, NodeKind},
    mutability::MutType,
    r#type::Type,
    std::math::int_type,
    type_inference::TypeInference,
    type_scheme::PubTypeConstraint,
    typing_env::{Local, TypingEnv},
    value::Value,
};

impl TypeInference {
    pub(crate) fn infer_match(
        &mut self,
        env: &mut TypingEnv,
        match_span: Location,
        cond_expr: &DExpr,
        alternatives: &[(Pattern, DExpr)],
        default: &Option<Box<DExpr>>,
    ) -> Result<(NodeKind, Type, MutType, EffType), InternalCompilationError> {
        use ir::Node as N;
        use ir::NodeKind as K;

        // Do we have a degenerate match with no alternative?
        if alternatives.is_empty() {
            if let Some(default) = default {
                let (node, mut_ty) = self.infer_expr(env, default)?;
                return Ok((node.kind, node.ty, mut_ty, node.effects));
            } else {
                return Err(internal_compilation_error!(EmptyMatchBody {
                    span: match_span
                }));
            }
        }

        // Infer the condition expression and get the pattern type.
        // Currently the type must be the same for all alternatives.
        let (condition_node, _) = self.infer_expr(env, cond_expr)?;
        let pattern_ty = condition_node.ty;
        let cond_eff = condition_node.effects.clone();
        let first_alternative = alternatives.first().unwrap();
        let first_alternative_span = first_alternative.0.span;
        let is_variant = first_alternative.0.kind.is_variant();
        let variants_span = Location::new_local(
            alternatives.first().unwrap().0.span.start(),
            alternatives.last().unwrap().0.span.end(),
        );

        Ok(if is_variant {
            // Variant patterns
            let initial_env_size = env.locals.len();

            // Create a fresh type variable for the inner types, when there is a variable binding.
            let mut seen_tags = HashMap::new();
            let (types, exprs): (Vec<_>, Vec<_>) = alternatives
                .iter()
                .map(|(pattern, expr)| {
                    if let Some(((tag, tag_span), vars)) = pattern.kind.as_variant() {
                        if let Some(old_tag_span) = seen_tags.insert(tag, tag_span) {
                            return Err(internal_compilation_error!(DuplicatedVariant {
                                first_occurrence: *old_tag_span,
                                second_occurrence: *tag_span,
                            }));
                        }
                        let mut seen_identifier = HashMap::new();
                        for (var, span) in vars {
                            if let Some(old_span) = seen_identifier.insert(*var, *span) {
                                return Err(internal_compilation_error!(
                                    IdentifierBoundMoreThanOnceInAPattern {
                                        first_occurrence: old_span,
                                        second_occurrence: *span,
                                    }
                                ));
                            }
                        }
                        let (inner_tys, variant_inner_ty) = match vars.len() {
                            0 => (vec![], Type::unit()),
                            1 => {
                                let ty = self.fresh_type_var_ty();
                                (vec![ty], ty)
                            }
                            n => {
                                let inner_tys = self.fresh_type_var_tys(n);
                                let variant_inner_ty = Type::tuple(inner_tys.clone());
                                (inner_tys, variant_inner_ty)
                            }
                        };
                        Ok(((*tag, inner_tys, variant_inner_ty), (expr, vars)))
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
            let store_variant = K::EnvStore(b(EnvStore {
                node: condition_node,
                name_span: cond_expr.span,
            }));
            let store_variant_node = N::new(
                store_variant,
                Type::unit(),
                cond_eff.clone(),
                cond_expr.span,
            );
            let match_condition_name = ustr("@match_condition");
            env.locals.push(Local::new(
                match_condition_name,
                MutType::constant(),
                pattern_ty,
                cond_expr.span,
            ));

            // Code to load the variant and extract the tag
            let load_variant = N::new(
                K::EnvLoad(b(EnvLoad {
                    index: initial_env_size,
                    name: Some(match_condition_name),
                })),
                pattern_ty,
                no_effects(),
                cond_expr.span,
            );
            let extract_tag = N::new(
                K::ExtractTag(b(load_variant.clone())),
                int_type(),
                no_effects(),
                cond_expr.span,
            );

            // Generate code for each alternative
            let mut return_ty = None;
            let mut return_ty_span = Location::new_local(0, 0); // placeholder
            let mut alternatives = types
                .iter()
                .zip(exprs)
                .map(
                    |((tag, inner_tys, variant_inner_ty), (expr, bind_var_names))| {
                        let tag_value = Value::native(tag.as_char_ptr() as isize);

                        // Prepare the environment for the alternative by adapting the type of the variant value
                        let alt_start_env_size = env.locals.len();
                        assert_eq!(inner_tys.len(), bind_var_names.len());
                        for ((name, span), inner_ty) in bind_var_names.iter().zip(inner_tys.iter())
                        {
                            env.locals.push(Local::new(
                                *name,
                                MutType::constant(),
                                *inner_ty,
                                *span,
                            ));
                        }

                        // Type check the alternative and generate its code
                        let mut node = if let Some(return_ty) = return_ty {
                            self.check_expr(
                                env,
                                expr,
                                return_ty,
                                MutType::constant(),
                                return_ty_span,
                            )?
                        } else {
                            let (node, _) = self.infer_expr(env, expr)?;
                            return_ty = Some(node.ty);
                            return_ty_span = expr.span;
                            node
                        };

                        // Generate the variable binding code
                        if !bind_var_names.is_empty() {
                            let mut project_nodes = Vec::new();
                            let mut add_projection = |i, is_tuple| {
                                let project_variant_inner = N::new(
                                    K::Project(b((load_variant.clone(), 0))),
                                    *variant_inner_ty,
                                    no_effects(),
                                    expr.span,
                                );
                                let inner_ty = inner_tys[i];
                                let project_tuple_inner = if is_tuple {
                                    N::new(
                                        K::Project(b((project_variant_inner, i))),
                                        inner_ty,
                                        no_effects(),
                                        expr.span,
                                    )
                                } else {
                                    project_variant_inner
                                };
                                let store_projected_inner = N::new(
                                    K::EnvStore(b(EnvStore {
                                        node: project_tuple_inner,
                                        name_span: bind_var_names[i].1,
                                    })),
                                    Type::unit(),
                                    no_effects(),
                                    expr.span,
                                );
                                project_nodes.push(store_projected_inner);
                            };
                            if bind_var_names.len() == 1 {
                                // single value payload, payload is the stored directly
                                add_projection(0, false);
                            } else {
                                // multiple value payload, payload is a tuple
                                for i in 0..inner_tys.len() {
                                    add_projection(i, true);
                                }
                            }
                            project_nodes.push(node);
                            let proj_effects = self.make_dependent_effect(
                                project_nodes.iter().map(|n| &n.effects).collect::<Vec<_>>(),
                            );
                            node = N::new(
                                K::Block(b(SVec2::from_vec(project_nodes))),
                                return_ty.unwrap(),
                                proj_effects,
                                expr.span,
                            );
                        }
                        env.locals.truncate(alt_start_env_size);
                        Result::<_, InternalCompilationError>::Ok((tag_value, node))
                    },
                )
                .collect::<Result<Vec<_>, _>>()?;
            let return_ty = return_ty.unwrap();
            let alt_eff = self.make_dependent_effect(
                alternatives
                    .iter()
                    .map(|(_, n)| &n.effects)
                    .collect::<Vec<_>>(),
            );

            // Do we have a default?
            let default = if let Some(default) = default {
                // Yes, so the pattern_ty is our type and we add constraints towards it.
                for (tag, _, variant_inner_ty) in types {
                    self.add_pub_constraint(PubTypeConstraint::new_type_has_variant(
                        pattern_ty,
                        tag,
                        variant_inner_ty,
                        variants_span,
                    ));
                }

                // Generate the default code node
                self.check_expr(env, default, return_ty, MutType::constant(), return_ty_span)?
            } else {
                // No default, compute a full variant type.
                let variant_inner_tys = types.into_iter().map(|(tag, _, ty)| (tag, ty)).collect();
                let variant_ty = Type::variant(variant_inner_tys);
                self.add_sub_type_constraint(pattern_ty, cond_expr.span, variant_ty, variants_span);

                // Generate the default code node
                alternatives
                    .drain(alternatives.len() - 1..)
                    .next()
                    .unwrap()
                    .1
            };
            env.locals.truncate(initial_env_size);

            // Generate the final code node
            let case_eff = self.make_dependent_effect([&alt_eff, &default.effects]);
            let case = K::Case(b(ir::Case {
                value: extract_tag,
                alternatives,
                default,
            }));
            let case_node = N::new(case, return_ty, case_eff, match_span);
            let effects =
                self.make_dependent_effect([&store_variant_node.effects, &case_node.effects]);
            let node = K::Block(b(SVec2::from_vec(vec![store_variant_node, case_node])));
            (node, return_ty, MutType::constant(), effects)
        } else {
            // Literal patterns, convert optional default to mandatory one
            let return_ty = self.fresh_type_var_ty();
            let (node, return_ty, effects) = if let Some(default) = default {
                let default =
                    self.check_expr(env, default, return_ty, MutType::constant(), match_span)?;
                let (alternatives, alt_eff) = self.check_literal_patterns(
                    env,
                    alternatives,
                    first_alternative_span,
                    pattern_ty,
                    cond_expr.span,
                    return_ty,
                    match_span,
                )?;
                let effects = self.make_dependent_effect([&cond_eff, &alt_eff, &default.effects]);
                (
                    K::Case(b(ir::Case {
                        value: condition_node,
                        alternatives,
                        default,
                    })),
                    return_ty,
                    effects,
                )
            } else {
                let (mut alternatives, alt_eff) = self.check_literal_patterns(
                    env,
                    alternatives,
                    first_alternative_span,
                    pattern_ty,
                    cond_expr.span,
                    return_ty,
                    match_span,
                )?;
                self.add_ty_coverage_constraint(
                    match_span,
                    pattern_ty,
                    alternatives.iter().map(|(v, _)| v.clone()).collect(),
                );
                let effects = self.make_dependent_effect([cond_eff, alt_eff]);
                let default = alternatives.pop().unwrap().1;
                (
                    K::Case(b(ir::Case {
                        value: condition_node,
                        alternatives,
                        default,
                    })),
                    return_ty,
                    effects,
                )
            };
            (node, return_ty, MutType::constant(), effects)
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn check_literal_patterns(
        &mut self,
        env: &mut TypingEnv,
        pairs: &[(Pattern, DExpr)],
        first_pattern_span: Location,
        expected_pattern_type: Type,
        expected_pattern_span: Location,
        expected_return_type: Type,
        expected_return_span: Location,
    ) -> Result<(Vec<(Value, ir::Node)>, EffType), InternalCompilationError> {
        let mut seen_values = HashMap::new();
        let (pairs, effects): (Vec<_>, Vec<_>) = pairs
            .iter()
            .map(|(pattern, expr)| {
                if let PatternKind::Literal(literal, ty) = &pattern.kind {
                    if let Some(previous_span) = seen_values.get(literal) {
                        return Err(internal_compilation_error!(DuplicatedLiteralPattern {
                            first_occurrence: *previous_span,
                            second_occurrence: pattern.span,
                        }));
                    }
                    seen_values.insert(literal.clone(), pattern.span);
                    self.add_sub_type_constraint(
                        *ty,
                        pattern.span,
                        expected_pattern_type,
                        expected_pattern_span,
                    );
                    let node = self.check_expr(
                        env,
                        expr,
                        expected_return_type,
                        MutType::constant(),
                        expected_return_span,
                    )?;
                    let effects = node.effects.clone();
                    Ok(((literal.clone().into_value(), node), effects))
                } else {
                    Err(internal_compilation_error!(InconsistentPattern {
                        a_type: PatternType::Literal,
                        a_span: first_pattern_span,
                        b_type: pattern.kind.r#type(),
                        b_span: expr.span,
                    }))
                }
            })
            .process_results(|iter| multiunzip(iter))?;
        let effects = self.make_dependent_effect(&effects);
        Ok((pairs, effects))
    }
}
