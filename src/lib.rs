// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
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
mod desugar;
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
mod location;
mod r#match;
pub mod module;
pub mod mutability;
mod never;
mod parser_helpers;
pub mod std;
mod sync;
pub mod r#trait;
pub mod r#type;
mod type_inference;
pub mod type_scheme;
pub mod typing_env;
pub mod value;

pub use ide::Compiler;
pub use location::Location;
pub use type_inference::SubOrSameType;

use r#type::Type;
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
}

/// Parse a type from a source code and return the corresponding Type.
pub fn parse_type(src: &str) -> Result<Type, LocatedError> {
    let mut errors = Vec::new();
    parser::TypeParser::new()
        .parse(&mut errors, src)
        .map_err(describe_parse_error)
}

/// Parse a module and an expression (if any) from a source code and return the corresponding ASTs.
pub fn parse_module_and_expr(
    src: &str,
) -> Result<(ast::PModule, Option<ast::PExpr>), Vec<LocatedError>> {
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
        parse_module_and_expr(src).map_err(|error| compilation_error!(ParsingFailed(error)))?;
    {
        let env = ModuleEnv::new(&module, other_modules);
        log::debug!("Module AST\n{}", module_ast.format_with(&env));
    }
    assert_eq!(module_ast.errors(), &[]);
    if let Some(expr) = expr_ast.as_ref() {
        log::debug!("Expr AST\n{expr}");
    }

    // Emit IR for the module.
    let mut module = emit_module(module_ast, other_modules, Some(&module)).map_err(|error| {
        let env = ModuleEnv::new(&module, other_modules);
        CompilationError::from_internal(error, &env, src)
    })?;
    module.source = Some(src.to_string());
    if !module.is_empty() {
        log::debug!("Module IR\n{}", FormatWith::new(&module, other_modules));
    }

    // Emit IR for the expression, if any.
    let expr = if let Some(expr_ast) = expr_ast {
        let env = ModuleEnv::new(&module, other_modules);
        let compiled_expr = emit_expr(expr_ast, env, vec![])
            .map_err(|error| CompilationError::from_internal(error, &env, src))?;
        log::debug!("Expr IR\n{}", compiled_expr.expr.format_with(&env));
        Some(compiled_expr)
    } else {
        None
    };

    Ok(ModuleAndExpr { module, expr })
}
