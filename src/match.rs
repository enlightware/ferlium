use std::collections::HashMap;

use itertools::Itertools;
use lrpar::Span;
use ustr::ustr;

use crate::{
    ast::{Expr, Pattern, PatternKind, PatternType},
    containers::{SVec1, SVec2, B},
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
        expr: &Expr,
        cond_expr: &Expr,
        alternatives: &[(Pattern, Expr)],
        default: &Option<Box<Expr>>,
    ) -> Result<(NodeKind, Type, MutType), InternalCompilationError> {
        use ir::Node as N;
        use ir::NodeKind as K;

        // Do we have a degenerate match with no alternative?
        if alternatives.is_empty() {
            if let Some(default) = default {
                let (node, ty, mut_ty) = self.infer_expr(env, default)?;
                return Ok((node.kind, ty, mut_ty));
            } else {
                panic!("empty match without default");
            }
        }

        // Infer the condition expression and get the pattern type.
        // Currently the type must be the same for all alternatives.
        let (condition_node, pattern_ty, _) = self.infer_expr(env, cond_expr)?;
        let first_alternative = alternatives.first().unwrap();
        let first_alternative_span = first_alternative.0.span;
        let is_variant = first_alternative.0.kind.is_variant();
        let variants_span = Span::new(
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
                    if let Some((tag, tag_span, var)) = pattern.kind.as_variant() {
                        if let Some(old_tag_span) = seen_tags.insert(tag, tag_span) {
                            return Err(InternalCompilationError::DuplicatedVariant {
                                first_occurrence: *old_tag_span,
                                second_occurrence: *tag_span,
                            });
                        }
                        let inner_ty = if var.is_some() {
                            self.fresh_type_var_ty()
                        } else {
                            Type::unit()
                        };
                        Ok(((*tag, inner_ty), (expr, var)))
                    } else {
                        Err(InternalCompilationError::InconsistentPattern {
                            a_type: PatternType::Variant,
                            a_span: first_alternative_span,
                            b_type: pattern.kind.r#type(),
                            b_span: pattern.span,
                        })
                    }
                })
                .process_results(|iter| iter.unzip())?;

            // Code to store the variant value in the environment.
            let store_variant = K::EnvStore(B::new(EnvStore {
                node: condition_node,
                ty: pattern_ty,
                name_span: cond_expr.span,
            }));
            let store_variant_node = N::new(store_variant, Type::unit(), cond_expr.span);
            env.locals.push(Local::new(
                ustr("@match_condition"),
                MutType::constant(),
                pattern_ty,
                cond_expr.span,
            ));

            // Code to load the variant and extract the tag
            let load_variant = N::new(
                K::EnvLoad(B::new(EnvLoad {
                    index: initial_env_size,
                })),
                pattern_ty,
                cond_expr.span,
            );
            let extract_tag = N::new(
                K::ExtractTag(B::new(load_variant.clone())),
                int_type(),
                cond_expr.span,
            );

            // Generate code for each alternative
            let mut return_ty = None;
            let mut return_ty_span = Span::new(0, 0); // placeholder
            let mut alternatives = types
                .iter()
                .zip(exprs)
                .map(|((tag, inner_ty), (expr, bind_var_name))| {
                    let tag_value = Value::native(tag.as_char_ptr() as isize);

                    // Prepare the environment for the alternative by adapting the type of the variant value
                    let alt_start_env_size = env.locals.len();
                    if let Some((bind_var_name, _)) = bind_var_name {
                        env.locals.push(Local::new(
                            *bind_var_name,
                            MutType::constant(),
                            *inner_ty,
                            first_alternative_span,
                        ));
                    }

                    // Type check the alternative and generate its code
                    let mut node = if let Some(return_ty) = return_ty {
                        self.check_expr(env, expr, return_ty, MutType::constant(), return_ty_span)?
                    } else {
                        let (node, expr_return_ty, _) = self.infer_expr(env, expr)?;
                        return_ty = Some(expr_return_ty);
                        return_ty_span = expr.span;
                        node
                    };

                    // Generate the variable binding code
                    if let Some((_, bind_var_span)) = bind_var_name {
                        let project_inner = N::new(
                            K::Project(B::new((load_variant.clone(), 0))),
                            *inner_ty,
                            expr.span,
                        );
                        let store_projected_inner = N::new(
                            K::EnvStore(B::new(EnvStore {
                                node: project_inner,
                                ty: *inner_ty,
                                name_span: *bind_var_span,
                            })),
                            Type::unit(),
                            expr.span,
                        );
                        node = N::new(
                            K::Block(B::new(SVec2::from_vec(vec![store_projected_inner, node]))),
                            return_ty.unwrap(),
                            expr.span,
                        );
                    }
                    env.locals.truncate(alt_start_env_size);
                    Result::<_, InternalCompilationError>::Ok((tag_value, node))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let return_ty = return_ty.unwrap();

            // Do we have a default?
            let default = if let Some(default) = default {
                // Yes, so the pattern_ty is our type and we add constraints towards it.
                for (tag, inner_ty) in types {
                    self.add_pub_constraint(PubTypeConstraint::new_type_has_variant(
                        pattern_ty,
                        tag,
                        inner_ty,
                        variants_span,
                    ));
                }

                // Generate the default code node
                self.check_expr(env, default, return_ty, MutType::constant(), return_ty_span)?
            } else {
                // No default, compute a full variant type.
                let variant_ty = Type::variant(types);
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
            let case = K::Case(B::new(ir::Case {
                value: extract_tag,
                alternatives,
                default,
            }));
            let case_node = N::new(case, return_ty, expr.span);
            let node = K::Block(B::new(SVec2::from_vec(vec![store_variant_node, case_node])));
            (node, return_ty, MutType::constant())
        } else {
            // Literal patterns, convert optional default to mandatory one
            let return_ty = self.fresh_type_var_ty();
            let (node, return_ty) = if let Some(default) = default {
                let default =
                    self.check_expr(env, default, return_ty, MutType::constant(), expr.span)?;
                let alternatives = self.check_literal_patterns(
                    env,
                    alternatives,
                    first_alternative_span,
                    pattern_ty,
                    cond_expr.span,
                    return_ty,
                    expr.span,
                )?;
                (
                    K::Case(B::new(ir::Case {
                        value: condition_node,
                        alternatives,
                        default,
                    })),
                    return_ty,
                )
            } else {
                let mut alternatives: Vec<_> = self.check_literal_patterns(
                    env,
                    alternatives,
                    first_alternative_span,
                    pattern_ty,
                    cond_expr.span,
                    return_ty,
                    expr.span,
                )?;
                let default = alternatives.pop().unwrap().1;
                (
                    K::Case(B::new(ir::Case {
                        value: condition_node,
                        alternatives,
                        default,
                    })),
                    return_ty,
                )
            };
            (node, return_ty, MutType::constant())
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn check_literal_patterns<U: std::iter::FromIterator<(Value, ir::Node)>>(
        &mut self,
        env: &mut TypingEnv,
        pairs: &[(Pattern, Expr)],
        first_pattern_span: Span,
        expected_pattern_type: Type,
        expected_pattern_span: Span,
        expected_return_type: Type,
        expected_return_span: Span,
    ) -> Result<U, InternalCompilationError> {
        pairs
            .iter()
            .map(|(pattern, expr)| {
                if let PatternKind::Literal(literal, ty) = &pattern.kind {
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
                    Ok((literal.clone(), node))
                } else {
                    Err(InternalCompilationError::InconsistentPattern {
                        a_type: PatternType::Literal,
                        a_span: first_pattern_span,
                        b_type: pattern.kind.r#type(),
                        b_span: expr.span,
                    })
                }
            })
            .collect::<Result<U, InternalCompilationError>>()
    }
}
