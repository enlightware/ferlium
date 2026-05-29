// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::sync::LazyLock;

use crate::FxHashSet;

use heck::ToSnakeCase;

use crate::{
    CompilerSession, ModuleAndExpr, SourceId, ast,
    format::FormatWith,
    hir::{Node, NodeArena, NodeId, NodeKind, UnresolvedKind},
    module::{LocalDecl, ModuleEnv, id::Id},
    types::{
        effects::{EffType, Effect, PrimitiveEffect},
        r#type::Type,
        type_scheme_display::TypeSchemeConstraintRenderMode,
    },
};
#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

/// An annotation data struct to be used in IDEs
#[cfg_attr(target_arch = "wasm32", wasm_bindgen(getter_with_clone))]
pub struct AnnotationData {
    pub pos: usize,
    pub hint: String,
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
impl AnnotationData {
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen(constructor))]
    pub fn new(pos: usize, hint: String) -> Self {
        Self { pos, hint }
    }
}

/// Type and other annotations for display in a IDE, for a given source file.
/// Returns a vector of positions in byte offsets and annotations.
pub(super) fn display_annotations(
    module_and_expr: &ModuleAndExpr,
    source_id: SourceId,
    src: &str,
    session: &CompilerSession,
    constraint_mode: TypeSchemeConstraintRenderMode,
) -> Vec<(usize, String)> {
    let entry = session.expect_module_entry(module_and_expr.module_id);
    let module = match entry.module() {
        None => return vec![],
        Some(module) => module,
    };
    let env = ModuleEnv::new(module, session.modules());
    let mut annotations = vec![];

    // Function and expression bodies.
    for function in module.iter_functions() {
        let spans = match &function.spans {
            Some(spans) => spans,
            None => continue,
        };
        if spans.span.source_id != source_id {
            continue;
        }
        if let Some(script_fn) = function.code.as_script() {
            let ty_var_names = function
                .definition
                .ty_scheme
                .display_ty_var_names_with_source_params(&function.definition.generic_params);
            let type_env = function
                .definition
                .ty_scheme
                .type_display_env(&env, &ty_var_names);
            variable_type_annotations(
                &module.ir_arena,
                script_fn.entry_node_id,
                &mut annotations,
                &function.locals,
                &type_env,
            );
        }
    }
    if let Some(expr) = &module_and_expr.expr {
        let root_span = module.ir_arena[expr.expr].span;
        if root_span.source_id == source_id {
            variable_type_annotations(
                &module.ir_arena,
                expr.expr,
                &mut annotations,
                &expr.locals,
                &env,
            );
        }
    }

    // Function signatures.
    for function in module.iter_functions() {
        let spans = match &function.spans {
            Some(spans) => spans,
            None => continue,
        };
        if spans.span.source_id != source_id {
            continue;
        }
        let ty_scheme = &function.definition.ty_scheme;
        let ty_var_names =
            ty_scheme.display_ty_var_names_with_source_params(&function.definition.generic_params);
        let type_env = ty_scheme.type_display_env(&env, &ty_var_names);
        if !function.definition.ty_scheme.is_just_type() {
            let source_param_count = function.definition.generic_params.len();
            let mut inserted_quantifiers = ty_scheme
                .display_ty_quantifiers_with_source_params(&function.definition.generic_params)
                .into_iter()
                .filter(|ty_var| ty_var.name() as usize >= source_param_count)
                .map(|ty_var| {
                    ty_var_names
                        .get(&ty_var)
                        .map_or_else(|| format!("{ty_var}"), ToString::to_string)
                })
                .chain(ty_scheme.eff_quantifiers.iter().map(|q| format!("{q}")))
                .peekable();
            if inserted_quantifiers.peek().is_some() {
                let inserted_quantifiers = inserted_quantifiers.collect::<Vec<_>>().join(", ");
                if let Some((_, last_source_param_span)) = function
                    .definition
                    .generic_params
                    .iter()
                    .max_by_key(|(_, span)| span.end_usize())
                {
                    annotations.push((
                        last_source_param_span.end_usize(),
                        format!(", {inserted_quantifiers}"),
                    ));
                } else if !spans.name.is_synthesized() {
                    annotations.push((spans.name.end_usize(), format!("<{inserted_quantifiers}>")));
                }
            }
        }
        for ((name_span, ty_span), arg_ty) in spans
            .args
            .iter()
            .zip(&function.definition.ty_scheme.ty.args)
        {
            if let Some((ty_span, ty_constant)) = ty_span {
                if !ty_constant {
                    let rendered = arg_ty.format_with(&type_env).to_string();
                    if src[ty_span.as_range()].trim() != rendered {
                        annotations.push((ty_span.end_usize(), format!(" ⇨ {rendered}")));
                    }
                }
            } else {
                annotations.push((
                    name_span.end_usize(),
                    format!(": {}", arg_ty.format_with(&type_env)),
                ));
            }
        }
        let displayed_effects = display_effects_with_constraint_mode(
            &function.definition.ty_scheme.ty.effects,
            constraint_mode,
        );
        let byte_src = src.as_bytes();
        let past_args_index = spans.args_span.end_usize();
        let start_space = if past_args_index > 0 && byte_src[past_args_index - 1] == b' ' {
            ""
        } else {
            " "
        };
        let mut annotation = if displayed_effects.is_empty() {
            if let Some((ret_span, ty_constant)) = spans.ret_ty {
                if !ty_constant {
                    let rendered = function
                        .definition
                        .ty_scheme
                        .ty
                        .ret
                        .format_with(&type_env)
                        .to_string();
                    (src[ret_span.as_range()].trim() != rendered)
                        .then(|| format!("{start_space}⇨ {rendered}"))
                } else {
                    None
                }
            } else {
                Some(format!(
                    "{start_space}-> {}",
                    function.definition.ty_scheme.ty.ret.format_with(&type_env)
                ))
            }
        } else if let Some((ret_span, ty_constant)) = spans.ret_ty {
            if !ty_constant {
                let rendered = function
                    .definition
                    .ty_scheme
                    .ty
                    .ret
                    .format_with(&type_env)
                    .to_string();
                (src[ret_span.as_range()].trim() != rendered)
                    .then(|| format!("{start_space}⇨ {rendered} ! {displayed_effects}"))
            } else {
                Some(format!("{start_space}! {displayed_effects}"))
            }
        } else {
            Some(format!(
                "{start_space}-> {} ! {}",
                function.definition.ty_scheme.ty.ret.format_with(&type_env),
                displayed_effects
            ))
        };
        if !function.definition.ty_scheme.is_just_type_and_effects() {
            let constraints = function
                .definition
                .ty_scheme
                .display_constraints_with_mode(&type_env, constraint_mode)
                .to_string();
            if !constraints.is_empty() {
                annotation = Some(format!(
                    "{}{}{}",
                    annotation.as_ref().map_or("", |v| v),
                    annotation.as_ref().map_or(start_space, |_| " "),
                    constraints
                ));
            }
        }
        if let Some(mut annotation) = annotation {
            let end_space = if past_args_index < byte_src.len() && byte_src[past_args_index] == b' '
            {
                ""
            } else {
                " "
            };
            annotation.push_str(end_space);
            annotations.push((past_args_index, annotation));
        }
    }

    // Return type of the expression, if any.
    if let Some(expr) = &module_and_expr.expr {
        let root_span = module.ir_arena[expr.expr].span;
        annotations.push((
            root_span.end_usize(),
            format!(": {}", expr.ty.display(&env)),
        ));
    }
    // FIXME: this need better behaviour to be useful.
    // For each end of line, we also show the type of the expression.
    // let newline_indices = newline_indices_of_non_empty_lines(src);
    // let mut i = 0;
    // for function in self.module.functions.values() {
    //     function.code.borrow_mut().apply_if_script(&mut |node| {
    //         while i < newline_indices.len() && newline_indices[i] <= node.span.end() {
    //             let pos = newline_indices[i];
    //             if let Some(ty) = crate::hir::type_at(arena, node, pos - 1) {
    //                 annotations.push((pos, format!(" {}", ty.format_with(&env))));
    //             }
    //             i += 1;
    //         }
    //     });
    // }
    // if let Some(expr) = &self.expr {
    //     while i < newline_indices.len() {
    //         let pos = newline_indices[i];
    //         if let Some(ty) = crate::hir::type_at(arena, expr.expr, pos - 1) {
    //             annotations.push((pos, format!(" {}", ty.format_with(&env))));
    //         }
    //         i += 1;
    //     }
    // }

    annotations
}

fn display_effects_with_constraint_mode(
    effects: &EffType,
    constraint_mode: TypeSchemeConstraintRenderMode,
) -> EffType {
    match constraint_mode {
        TypeSchemeConstraintRenderMode::Full => effects.clone(),
        TypeSchemeConstraintRenderMode::Light => effects
            .iter()
            .filter(|effect| *effect != Effect::Primitive(PrimitiveEffect::Fallible))
            .collect(),
    }
}

fn variable_type_annotations<Env>(
    arena: &NodeArena,
    node_id: NodeId,
    result: &mut Vec<(usize, String)>,
    locals: &[LocalDecl],
    env: &Env,
) where
    Type: FormatWith<Env>,
{
    node_variable_type_annotations(&arena[node_id], arena, result, locals, env)
}

fn node_variable_type_annotations<Env>(
    node: &Node,
    arena: &NodeArena,
    result: &mut Vec<(usize, String)>,
    locals: &[LocalDecl],
    env: &Env,
) where
    Type: FormatWith<Env>,
{
    use NodeKind::*;
    match &node.kind {
        Immediate(_) | Uninit => {}
        BuildClosure(build_closure) => {
            variable_type_annotations(arena, build_closure.function, result, locals, env);
            // We do not look into captures as they are generated code.
        }
        Apply(app) => {
            variable_type_annotations(arena, app.function, result, locals, env);
            for arg in &app.arguments {
                variable_type_annotations(arena, arg.value, result, locals, env);
            }
        }
        CloneClosureEnv(node) => {
            variable_type_annotations(arena, node.source, result, locals, env);
            variable_type_annotations(arena, node.target, result, locals, env);
        }
        DropClosureEnv(node) => {
            variable_type_annotations(arena, node.target, result, locals, env);
        }
        CloneValue(node) => {
            variable_type_annotations(arena, node.source, result, locals, env);
        }
        StaticApply(app) => {
            let arity = app.argument_names.len();
            let show_arg_name_hints = !app.function_span.is_empty();
            for (index, arg) in app.arguments.iter().enumerate() {
                if show_arg_name_hints
                    && let (Some(path), Some(arg_name)) =
                        (&app.function_path, app.argument_names.get(index))
                    && !should_hide_arg_name_hint(arena, path, arity, arg_name, arg.value, locals)
                {
                    result.push((arena[arg.value].span.start_usize(), format!("{arg_name}: ")));
                }
                variable_type_annotations(arena, arg.value, result, locals, env);
            }
        }
        Unresolved(
            UnresolvedKind::TraitMethodApply(_)
            | UnresolvedKind::GetTraitMethod(_)
            | UnresolvedKind::GetTraitAssociatedConst(_)
            | UnresolvedKind::GetTraitDictionary(_),
        ) => {
            // Lowered away by dictionary passing; absent from the final HIR.
        }
        GetFunction(_) => {}
        GetDictionary(_) => {}
        LoadDictionary(_) | LoadFieldIndex(_) => {}
        GetDictionaryMethod(node) => {
            variable_type_annotations(arena, node.dictionary, result, locals, env);
        }
        GetDictionaryAssociatedConst(node) => {
            variable_type_annotations(arena, node.dictionary, result, locals, env);
        }
        CallDictionaryMethod(node) => {
            variable_type_annotations(arena, node.dictionary, result, locals, env);
            for arg in &node.arguments {
                variable_type_annotations(arena, arg.value, result, locals, env);
            }
        }
        StoreLocal(node) => {
            // Note: desugared string interpolation code have variable names starting with "@", so we ignore these.
            // Note: synthesized let nodes have empty name span, so we ignore these.
            let local = &locals[node.id.as_index()];
            let (name, name_span) = local.name;
            if !name.starts_with("@") && !name_span.is_synthesized() {
                let value_ty = arena[node.value].ty;
                if let Some((ty_span, ty_constant)) = local.ty_span {
                    if !ty_constant {
                        result.push((
                            ty_span.end_usize(),
                            format!(" ⇨ {}", value_ty.format_with(env)),
                        ));
                    }
                } else {
                    result.push((
                        name_span.end_usize(),
                        format!(": {}", value_ty.format_with(env)),
                    ));
                }
            }
            variable_type_annotations(arena, node.value, result, locals, env);
        }
        TakeLocalValue(_) => {}
        LoadLocal(_) => {}
        Return(node) => variable_type_annotations(arena, *node, result, locals, env),
        Block(block) => block
            .body
            .iter()
            .for_each(|&node| variable_type_annotations(arena, node, result, locals, env)),
        Assign(assignment) => {
            variable_type_annotations(arena, assignment.place, result, locals, env);
            variable_type_annotations(arena, assignment.value, result, locals, env);
        }
        Tuple(nodes) => nodes
            .iter()
            .for_each(|&node| variable_type_annotations(arena, node, result, locals, env)),
        Project(project) => variable_type_annotations(arena, project.value, result, locals, env),
        Record(nodes) => nodes
            .iter()
            .for_each(|&node| variable_type_annotations(arena, node, result, locals, env)),
        Unresolved(UnresolvedKind::FieldAccess(field_access)) => {
            variable_type_annotations(arena, field_access.value, result, locals, env)
        }
        ProjectAt(project) => variable_type_annotations(arena, project.value, result, locals, env),
        Variant(variant) => variable_type_annotations(arena, variant.payload, result, locals, env),
        ExtractTag(node) => variable_type_annotations(arena, *node, result, locals, env),
        Array(nodes) => nodes
            .iter()
            .for_each(|&node| variable_type_annotations(arena, node, result, locals, env)),
        Case(case) => {
            variable_type_annotations(arena, case.value, result, locals, env);
            for &(_, alt_id) in &case.alternatives {
                variable_type_annotations(arena, alt_id, result, locals, env);
            }
            variable_type_annotations(arena, case.default, result, locals, env);
        }
        Loop(body) => variable_type_annotations(arena, *body, result, locals, env),
        CheckCallDepth | CheckFuel | SoftBreak | Unimplemented => {}
    }
}

// Essentially implement a similar logic as rust-analyzer's "should_hide_param_name_hint" fn
fn should_hide_arg_name_hint(
    arena: &NodeArena,
    function_path: &ast::Path,
    arity: usize,
    arg_name: &str,
    argument: NodeId,
    locals: &[LocalDecl],
) -> bool {
    if function_path
        .segments
        .iter()
        .any(|segment| segment.0.starts_with('@'))
    {
        return true;
    }

    let arg_name = arg_name.trim_start_matches('_');
    if arg_name.is_empty() {
        return true;
    }

    static PATHS_TO_HIDE: LazyLock<FxHashSet<&'static str>> = LazyLock::new(|| {
        [
            "std::eq",
            "std::ne",
            "std::le",
            "std::lt",
            "std::ge",
            "std::gt",
            "std::not",
            "std::neg",
            "std::add",
            "std::sub",
            "std::mul",
            "std::div",
            "std::rem",
            "std::array_index",
        ]
        .into_iter()
        .collect()
    });
    let joined_path = format!("{function_path}");
    if PATHS_TO_HIDE.contains(joined_path.as_str()) {
        return true;
    }

    let function_name = function_path.segments.last().unwrap().0;
    is_arg_name_suffix_of_unary_fn_name(&function_name, arity, arg_name)
        || is_argument_similar_to_arg_name(arena, argument, arg_name, locals)
        || (arity <= 2 && is_obvious_param(arg_name))
        || is_adt_constructor_similar_to_arg_name(arena, argument, arg_name)
}

fn is_arg_name_suffix_of_unary_fn_name(function_name: &str, arity: usize, arg_name: &str) -> bool {
    if arity != 1 {
        return false;
    }
    function_name == arg_name
        || function_name
            .len()
            .checked_sub(arg_name.len())
            .and_then(|at| {
                function_name
                    .is_char_boundary(at)
                    .then(|| function_name.split_at(at))
            })
            .is_some_and(|(prefix, suffix)| {
                suffix.eq_ignore_ascii_case(arg_name) && prefix.ends_with('_')
            })
}

fn is_argument_similar_to_arg_name(
    arena: &NodeArena,
    argument: NodeId,
    arg_name: &str,
    locals: &[LocalDecl],
) -> bool {
    use NodeKind::*;
    let argument = match arena[argument].kind {
        LoadLocal(ref load) => locals[load.id.as_index()].name.0.as_str(),
        _ => return false,
    };

    let str_split_at = |str: &str, at| str.is_char_boundary(at).then(|| argument.split_at(at));

    let arg_name = arg_name.trim_start_matches('_');
    let argument = argument.trim_start_matches('_');

    match str_split_at(argument, arg_name.len()) {
        Some((prefix, rest)) if prefix.eq_ignore_ascii_case(arg_name) => {
            return rest.is_empty() || rest.starts_with('_');
        }
        _ => (),
    }
    match argument
        .len()
        .checked_sub(arg_name.len())
        .and_then(|at| str_split_at(argument, at))
    {
        Some((rest, suffix)) if arg_name.eq_ignore_ascii_case(suffix) => {
            return rest.is_empty() || rest.ends_with('_');
        }
        _ => (),
    }
    false
}

fn is_obvious_param(arg_name: &str) -> bool {
    let is_obvious_param_name = matches!(
        arg_name,
        "self" | "left" | "right" | "value" | "pat" | "predicate" | "other"
    );
    arg_name.len() == 1 || is_obvious_param_name
}

fn is_adt_constructor_similar_to_arg_name(
    arena: &NodeArena,
    argument: NodeId,
    arg_name: &str,
) -> bool {
    use NodeKind::*;
    let node = &arena[argument];
    let tag = match &node.kind {
        Variant(variant) => variant.tag,
        _ => return false,
    };
    tag.to_snake_case() == arg_name
}
