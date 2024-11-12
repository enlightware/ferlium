use heck::ToSnakeCase;

use crate::{
    ir::{Node, NodeKind, StaticApplication},
    module::{FmtWithModuleEnv, ModuleEnv, Modules},
    std::math::int_type,
    type_scheme::DisplayStyle,
    ModuleAndExpr,
};

impl ModuleAndExpr {
    /// Type and other annotations for display in a IDE
    /// Returns a vector of positions in byte offsets and annotations.
    pub fn display_annotations(
        &self,
        _src: &str,
        other_modules: &Modules,
        style: DisplayStyle,
    ) -> Vec<(usize, String)> {
        use DisplayStyle::*;
        let env = ModuleEnv::new(&self.module, other_modules);
        let mut annotations = vec![];

        // Let/var bindings just after the name.
        for function in self.module.functions.values() {
            let mut code = function.code.borrow_mut();
            if let Some(script_fn) = code.as_script_mut() {
                script_fn
                    .code
                    .variable_type_annotations(&mut annotations, &env);
            }
        }
        if let Some(expr) = &self.expr {
            expr.expr.variable_type_annotations(&mut annotations, &env);
        }

        // Function signatures.
        for function in self.module.functions.values() {
            if let Some(spans) = &function.spans {
                if !function.ty_scheme.is_just_type() {
                    match style {
                        Mathematical => {
                            annotations.push((
                                spans.span.start(),
                                format!(
                                    "{} ",
                                    function
                                        .ty_scheme
                                        .display_quantifiers_and_constraints_math_style(&env)
                                ),
                            ));
                        }
                        Rust => {
                            annotations.push((
                                spans.name.end(),
                                format!("{}", function.ty_scheme.display_quantifiers_rust_style()),
                            ));
                        }
                    }
                }
                for (span, arg_ty) in spans.args.iter().zip(&function.ty_scheme.ty.args) {
                    annotations.push((span.end(), format!(": {}", arg_ty.format_with(&env))));
                }
                let ret_ty_and_eff = if function.ty_scheme.ty.effects.is_empty() {
                    format!(" → {}", function.ty_scheme.ty.ret.format_with(&env))
                } else {
                    format!(
                        " → {} ! {}",
                        function.ty_scheme.ty.ret.format_with(&env),
                        function.ty_scheme.ty.effects
                    )
                };
                annotations.push((spans.args_span.end(), ret_ty_and_eff));
                if style == Rust && !function.ty_scheme.is_just_type_and_effects() {
                    annotations.push((
                        spans.args_span.end(),
                        format!(
                            " {}",
                            function.ty_scheme.display_constraints_rust_style(&env)
                        ),
                    ));
                }
            }
        }

        // Return type of the expression, if any.
        if let Some(expr) = &self.expr {
            annotations.push((
                expr.expr.span.end(),
                match style {
                    Mathematical => format!(": {}", expr.ty.display_math_style(&env)),
                    Rust => format!(": {}", expr.ty.display_rust_style(&env)),
                },
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
        //             if let Some(ty) = node.type_at(pos - 1) {
        //                 annotations.push((pos, format!(" {}", ty.format_with(&env))));
        //             }
        //             i += 1;
        //         }
        //     });
        // }
        // if let Some(expr) = &self.expr {
        //     while i < newline_indices.len() {
        //         let pos = newline_indices[i];
        //         if let Some(ty) = expr.expr.type_at(pos - 1) {
        //             annotations.push((pos, format!(" {}", ty.format_with(&env))));
        //         }
        //         i += 1;
        //     }
        // }

        annotations
    }
}

impl Node {
    pub fn variable_type_annotations(&self, result: &mut Vec<(usize, String)>, env: &ModuleEnv) {
        use NodeKind::*;
        match &self.kind {
            Immediate(_) => {}
            BuildClosure(build_closure) => {
                build_closure
                    .function
                    .variable_type_annotations(result, env);
                // We do not look into captures as they are generated code.
            }
            Apply(app) => {
                app.function.variable_type_annotations(result, env);
                for arg in &app.arguments {
                    arg.variable_type_annotations(result, env);
                }
            }
            StaticApply(app) => {
                for (arg, arg_name) in app.arguments.iter().zip(app.argument_names.iter()) {
                    if !should_hide_arg_name_hint(app, arg_name, arg) {
                        result.push((arg.span.start(), format!("{}: ", arg_name)));
                    }
                    arg.variable_type_annotations(result, env);
                }
            }
            EnvStore(node) => {
                // Note: synthesized let nodes have empty name span, so we ignore these.
                if node.name_span.end() != node.name_span.start() {
                    result.push((
                        node.name_span.end(),
                        format!(": {}", node.node.ty.format_with(env)),
                    ));
                }
                node.node.variable_type_annotations(result, env);
            }
            EnvLoad(_) => {}
            Block(nodes) => nodes
                .iter()
                .for_each(|node| node.variable_type_annotations(result, env)),
            Assign(assignment) => {
                assignment.place.variable_type_annotations(result, env);
                assignment.value.variable_type_annotations(result, env);
            }
            Tuple(nodes) => nodes
                .iter()
                .for_each(|node| node.variable_type_annotations(result, env)),
            Project(projection) => projection.0.variable_type_annotations(result, env),
            Record(nodes) => nodes
                .iter()
                .for_each(|node| node.variable_type_annotations(result, env)),
            FieldAccess(access) => access.0.variable_type_annotations(result, env),
            ProjectAt(access) => access.0.variable_type_annotations(result, env),
            Variant(variant) => variant.1.variable_type_annotations(result, env),
            ExtractTag(node) => node.variable_type_annotations(result, env),
            Array(nodes) => nodes
                .iter()
                .for_each(|node| node.variable_type_annotations(result, env)),
            Index(array, index) => {
                array.variable_type_annotations(result, env);
                index.variable_type_annotations(result, env);
            }
            Case(case) => {
                case.value.variable_type_annotations(result, env);
                for (_, node) in &case.alternatives {
                    node.variable_type_annotations(result, env);
                }
                case.default.variable_type_annotations(result, env);
            }
            Iterate(iteration) => {
                // TODO: once the iterator is generalized, get the type from it!
                result.push((
                    iteration.var_name_span.end(),
                    format!(": {}", int_type().format_with(env)),
                ));
                iteration.iterator.variable_type_annotations(result, env);
                iteration.body.variable_type_annotations(result, env);
            }
        }
    }
}

// Essentially implement a similar logic as rust-analyzer's "should_hide_param_name_hint" fn
fn should_hide_arg_name_hint(app: &StaticApplication, arg_name: &str, argument: &Node) -> bool {
    let function_name = &app.function_name;
    let arity = app.arguments.len();
    if function_name.starts_with('@') {
        return true;
    }

    let arg_name = arg_name.trim_start_matches('_');
    if arg_name.is_empty() {
        return true;
    }

    is_arg_name_suffix_of_unary_fn_name(function_name, arity, arg_name)
        || is_argument_similar_to_arg_name(argument, arg_name)
        || (arity <= 2 && is_obvious_param(arg_name))
        || is_adt_constructor_similar_to_arg_name(argument, arg_name)
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
            .map_or(false, |(prefix, suffix)| {
                suffix.eq_ignore_ascii_case(arg_name) && prefix.ends_with('_')
            })
}

fn is_argument_similar_to_arg_name(argument: &Node, arg_name: &str) -> bool {
    let argument = match argument.kind {
        NodeKind::EnvLoad(ref load) => match load.name {
            Some(name) => name,
            None => return false,
        },
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
        "left" | "right" | "value" | "pat" | "predicate" | "other"
    );
    arg_name.len() == 1 || is_obvious_param_name
}

fn is_adt_constructor_similar_to_arg_name(argument: &Node, arg_name: &str) -> bool {
    use NodeKind::*;
    let tag = match &argument.kind {
        Immediate(value) => {
            if !argument.ty.data().is_variant() {
                return false;
            }
            value.value.as_variant().unwrap().tag
        }
        Variant(variant) => variant.0,
        _ => return false,
    };
    tag.to_snake_case() == arg_name
}
