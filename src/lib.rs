use std::new_module_with_prelude;

use emit_ir::{emit_expr_top_level, emit_module, CompiledExpr};
use error::CompilationError;
use format::FormatWith;
use module::{FmtWithModuleEnv, Module, ModuleEnv, Modules};
use parser::parse;

mod assert;
mod ast;
mod containers;
pub mod emit_ir;
pub mod error;
pub mod format;
pub mod function;
mod graph;
pub mod ir;
pub mod module;
pub mod mutability;
pub mod parser;
mod parser_helpers;
pub mod std;
mod sync;
pub mod r#type;
mod type_inference;
pub mod type_scheme;
pub mod typing_env;
pub mod value;

pub use lrpar::Span;
use type_scheme::DisplayStyle;

/// A compiled module and an expression (if any).
#[derive(Default, Debug)]
pub struct ModuleAndExpr {
    pub module: Module,
    pub expr: Option<CompiledExpr>,
}
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
            function.code.borrow_mut().apply_if_script(&mut |node| {
                node.variable_type_annotations(style, &mut annotations, &env)
            });
        }
        if let Some(expr) = &self.expr {
            expr.expr
                .variable_type_annotations(style, &mut annotations, &env);
        }

        // Function signatures.
        for function in self.module.functions.values() {
            if let Some(spans) = &function.spans {
                if style == Mathematical && !function.ty_scheme.is_just_type() {
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
                for (span, arg_ty) in spans.args.iter().zip(&function.ty_scheme.ty.args) {
                    annotations.push((span.end(), format!(": {}", arg_ty.format_with(&env))));
                }
                annotations.push((
                    spans.args_span.end(),
                    format!(" → {}", function.ty_scheme.ty.ret.format_with(&env)),
                ));
                if style == Rust && !function.ty_scheme.is_just_type() {
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

/// Compile a source code, given some other modules, and return the compiled module and an expression (if any), or an error.
/// All spans are in byte offsets.
pub fn compile(src: &str, other_modules: &Modules) -> Result<ModuleAndExpr, CompilationError> {
    let module = new_module_with_prelude();

    // Parse the source code.
    log::debug!("Input: {src}");
    let (module_ast, expr_ast) = parse(src);
    {
        let env = ModuleEnv::new(&module, other_modules);
        log::debug!("Module AST\n{}", module_ast.format_with(&env));
    }
    assert_eq!(module_ast.errors(), &[]);
    if let Some(expr) = expr_ast.as_ref() {
        log::debug!("Expr AST\n{expr}");
        let errors = expr.errors();
        if !errors.is_empty() {
            return Err(CompilationError::ParsingFailed(errors));
        }
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
        let compiled_expr = emit_expr_top_level(&expr_ast, env, vec![])
            .map_err(|error| CompilationError::from_internal(error, &env, src))?;
        log::debug!("Expr IR\n{}", compiled_expr.expr.format_with(&env));
        Some(compiled_expr)
    } else {
        None
    };

    Ok(ModuleAndExpr { module, expr })
}
