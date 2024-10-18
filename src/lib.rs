use std::new_module_with_prelude;

use emit_ir::{emit_expr, emit_module, CompiledExpr};
use error::{CompilationError, LocatedError};
use format::FormatWith;
use itertools::Itertools;
use lalrpop_util::lalrpop_mod;
use module::{FmtWithModuleEnv, Module, ModuleEnv, Modules, Use};
use parser_helpers::describe_parse_error;

mod assert;
mod ast;
mod borrow_checker;
mod containers;
mod dictionary_passing;
pub mod effects;
pub mod emit_ir;
pub mod error;
mod escapes;
pub mod eval;
pub mod format;
mod format_string;
pub mod function;
mod graph;
pub mod ide;
pub mod ir;
mod r#match;
pub mod module;
pub mod mutability;
mod parser_helpers;
mod span;
pub mod std;
mod sync;
pub mod r#type;
mod type_inference;
pub mod type_scheme;
pub mod typing_env;
pub mod value;

pub use ide::Compiler;
pub use span::Span;

use type_scheme::DisplayStyle;
pub use ustr::{ustr, Ustr};

lalrpop_mod!(
    #[allow(clippy::ptr_arg)]
    #[rustfmt::skip]
    parser
);

/// A compiled module and an expression (if any).
#[derive(Default, Debug)]
pub struct ModuleAndExpr {
    pub module: Module,
    pub expr: Option<CompiledExpr>,
}
impl ModuleAndExpr {
    pub fn new_just_module(module: Module) -> Self {
        Self { module, expr: None }
    }

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

/// Parse a module and an expression (if any) from a source code and return the corresponding ASTs.
pub fn parse_module_and_expr(
    src: &str,
) -> Result<(ast::Module, Option<ast::Expr>), Vec<LocatedError>> {
    let mut errors = Vec::new();
    let module_and_expr = parser::ModuleAndExprParser::new()
        .parse(&mut errors, src)
        .map_err(|error| vec![describe_parse_error(error)])?;
    // TODO: change the last line to an unwrap once the grammar is fully error-tolerant.
    if !errors.is_empty() {
        let errors = errors
            .into_iter()
            .map(|error| describe_parse_error(error.error))
            .collect();
        Err(errors)
    } else {
        Ok(module_and_expr)
    }
}

/// Compile a source code, given some other modules, and return the compiled module and an expression (if any), or an error.
/// All spans are in byte offsets.
pub fn compile(
    src: &str,
    other_modules: &Modules,
    extra_uses: &[Use],
) -> Result<ModuleAndExpr, CompilationError> {
    let mut module = new_module_with_prelude();
    module.uses.extend(extra_uses.iter().cloned());

    // Parse the source code.
    log::debug!("Using other modules: {}", other_modules.keys().join(", "));
    log::debug!("Input: {src}");
    let (module_ast, expr_ast) =
        parse_module_and_expr(src).map_err(CompilationError::ParsingFailed)?;
    {
        let env = ModuleEnv::new(&module, other_modules);
        log::debug!("Module AST\n{}", module_ast.format_with(&env));
    }
    assert_eq!(module_ast.errors(), &[]);
    if let Some(expr) = expr_ast.as_ref() {
        log::debug!("Expr AST\n{expr}");
    }

    // Emit IR for the module.
    let module = emit_module(&module_ast, other_modules, Some(&module)).map_err(|error| {
        let env = ModuleEnv::new(&module, other_modules);
        CompilationError::from_internal(error, &env, src)
    })?;
    if !module.is_empty() {
        log::debug!("Module IR\n{}", FormatWith::new(&module, other_modules));
    }

    // Emit IR for the expression, if any.
    let expr = if let Some(expr_ast) = expr_ast {
        let env = ModuleEnv::new(&module, other_modules);
        let compiled_expr = emit_expr(&expr_ast, env, vec![])
            .map_err(|error| CompilationError::from_internal(error, &env, src))?;
        log::debug!("Expr IR\n{}", compiled_expr.expr.format_with(&env));
        Some(compiled_expr)
    } else {
        None
    };

    Ok(ModuleAndExpr { module, expr })
}
