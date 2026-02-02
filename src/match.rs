// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::collections::HashMap;

use crate::{
    Location, ast::PatternVar, error::DuplicatedVariantContext, internal_compilation_error,
    std::core::REPR_TRAIT, r#type::TypeKind,
};
use itertools::{Itertools, multiunzip};
use ustr::ustr;

use crate::{
    ast::{DExpr, Pattern, PatternKind, PatternType},
    containers::{SVec2, b},
    effects::{EffType, no_effects},
    error::InternalCompilationError,
    ir::{self, EnvLoad, EnvStore, NodeKind},
    mutability::MutType,
    std::math::int_type,
    r#type::Type,
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
        let cond_eff = condition_node.effects.clone();

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
            alternatives.last().unwrap().1.span,
        ])
        .unwrap();

        Ok(if is_variant {
            // Variant patterns
            let initial_env_size = env.locals.len();

            // Create a fresh type variable for the inner types, when there is a variable binding.
            let mut seen_tags = HashMap::new();
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
                        let mut seen_identifier = HashMap::new();
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
            let match_condition_name = ustr("@match_condition");
            let store_variant = K::EnvStore(b(EnvStore {
                value: condition_node,
                index: initial_env_size,
                name: match_condition_name,
                name_span: Location::new_synthesized(),
                ty_span: None,
            }));
            let store_variant_node = N::new(
                store_variant,
                Type::unit(),
                cond_eff.clone(),
                cond_expr.span,
            );
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
            let mut return_ty_span = match_span;
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
                            for i in 0..inner_tys.len() {
                                let project_variant_inner = N::new(
                                    K::Project(b((load_variant.clone(), 0))),
                                    *variant_inner_ty,
                                    no_effects(),
                                    expr.span,
                                );
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
                                    K::Project(b((project_variant_inner, index)))
                                } else {
                                    K::FieldAccess(b((project_variant_inner, bind_var_names[i].0)))
                                };
                                let project_inner =
                                    N::new(project_inner_kind, inner_ty, no_effects(), expr.span);
                                let store_projected_inner = N::new(
                                    K::EnvStore(b(EnvStore {
                                        value: project_inner,
                                        index: alt_start_env_size + i,
                                        name: bind_var_names[i].0,
                                        name_span: bind_var_names[i].1,
                                        ty_span: None,
                                    })),
                                    Type::unit(),
                                    no_effects(),
                                    expr.span,
                                );
                                project_nodes.push(store_projected_inner);
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
                        assert!(env.locals.len() == alt_start_env_size + bind_var_names.len());
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
                        cond_expr.span,
                        tag,
                        variant_inner_ty,
                        alternatives_span,
                    ));
                }

                // Generate the default code node
                self.check_expr(env, default, return_ty, MutType::constant(), return_ty_span)?
            } else {
                // No default, compute a full variant type.
                let variant_inner_tys: Vec<_> =
                    types.into_iter().map(|(tag, _, ty)| (tag, ty)).collect();
                let variant_ty = Type::variant(variant_inner_tys);
                self.add_sub_type_constraint(
                    pattern_ty,
                    cond_expr.span,
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
