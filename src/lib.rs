// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use ::std::rc::Rc;
use std::new_module_using_std;

use ast::{UnstableCollector, VisitExpr};
use emit_ir::{CompiledExpr, emit_expr, emit_module};
use error::{CompilationError, LocatedError};
use itertools::Itertools;
use lalrpop_util::lalrpop_mod;
use module::ModuleEnv;
use parser_helpers::describe_parse_error;

mod assert;
pub mod ast;
mod borrow_checker;
pub mod containers;
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
mod ir_syn;
mod location;
mod r#match;
pub mod module;
pub mod mutability;
mod never;
mod parser_helpers;
pub mod std;
mod sync;
pub mod r#trait;
pub mod trait_solver;
pub mod r#type;
mod type_inference;
mod type_like;
mod type_mapper;
pub mod type_scheme;
mod type_substitution;
mod type_visitor;
pub mod typing_env;
pub mod value;

pub use ide::Compiler;
pub use location::Location;
pub use type_inference::SubOrSameType;

use type_scheme::DisplayStyle;
pub use ustr::{Ustr, ustr};

use crate::{
    format::FormatWith,
    module::{Module, ModuleRc, Modules, Use},
    r#type::Type,
};

lalrpop_mod!(
    #[allow(clippy::ptr_arg)]
    #[rustfmt::skip]
    parser
);

/// A compiled module and an expression (if any).
#[derive(Default, Debug)]
pub struct ModuleAndExpr {
    pub module: ModuleRc,
    pub expr: Option<CompiledExpr>,
}
impl ModuleAndExpr {
    pub fn new_just_module(module: Module) -> Self {
        let module = Rc::new(module);
        assert!(module.functions.is_empty());
        assert!(module.impls.data.is_empty());
        Self { module, expr: None }
    }
}

/// Parse a type from a source code and return the corresponding concrete Type.
pub fn parse_concrete_type(src: &str) -> Result<ast::PType, LocatedError> {
    let mut errors = Vec::new();
    parser::ConcreteTypeParser::new()
        .parse(&mut errors, src)
        .map_err(describe_parse_error)
}

/// Resolve a concrete type from a source code and return the corresponding Type.
pub fn resolve_concrete_type(src: &str, env: &ModuleEnv<'_>) -> Result<Type, CompilationError> {
    let ast =
        parse_concrete_type(src).map_err(|error| compilation_error!(ParsingFailed(vec![error])))?;
    let span = Location::new_local(0, src.len());
    ast.desugar(span, false, env)
        .map_err(|error| CompilationError::resolve_types(error, env, src))
}

/// Parse a type from a source code and return the corresponding Type,
/// with placeholder filled with first generic variable.
pub fn parse_generic_type(src: &str) -> Result<ast::PType, LocatedError> {
    let mut errors = Vec::new();
    parser::GenericTypeParser::new()
        .parse(&mut errors, src)
        .map_err(describe_parse_error)
}

/// Resolve a generic type from a source code and return the corresponding Type,
/// with placeholder filled with first generic variable.
pub fn resolve_generic_type(src: &str, env: &ModuleEnv<'_>) -> Result<Type, CompilationError> {
    let ast =
        parse_generic_type(src).map_err(|error| compilation_error!(ParsingFailed(vec![error])))?;
    let span = Location::new_local(0, src.len());
    ast.desugar(span, false, env)
        .map_err(|error| CompilationError::resolve_types(error, env, src))
}

/// Parse a module from a source code and return the corresponding ASTs.
pub fn parse_module(src: &str, accept_unstable: bool) -> Result<ast::PModule, Vec<LocatedError>> {
    let mut errors = Vec::new();
    let module = parser::ModuleParser::new()
        .parse(&mut errors, src)
        .map_err(|error| vec![describe_parse_error(error)])?;
    // TODO: change the last line to an unwrap once the grammar is fully error-tolerant.
    if !errors.is_empty() {
        let errors = errors
            .into_iter()
            .map(|error| describe_parse_error(error.error))
            .collect();
        Err(errors)
    } else if !accept_unstable {
        let unstables = module.visit_with(UnstableCollector::default());
        if unstables.0.is_empty() {
            Ok(module)
        } else {
            Err(unstables
                .0
                .into_iter()
                .map(|span| ("Unstable feature not allowed".into(), span))
                .collect())
        }
    } else {
        Ok(module)
    }
}

/// Parse a module and an expression (if any) from a source code and return the corresponding ASTs.
pub fn parse_module_and_expr(
    src: &str,
    accept_unstable: bool,
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
    } else if !accept_unstable {
        let mut unstables = module_and_expr.0.visit_with(UnstableCollector::default());
        if let Some(expr) = module_and_expr.1.as_ref() {
            unstables = expr.visit_with(unstables);
        }
        if unstables.0.is_empty() {
            Ok(module_and_expr)
        } else {
            Err(unstables
                .0
                .into_iter()
                .map(|span| ("Unstable feature not allowed".into(), span))
                .collect())
        }
    } else {
        Ok(module_and_expr)
    }
}

/// Compile a source code, given some other Modules, and return the compiled module and an expression (if any), or an error.
/// All spans are in byte offsets.
pub fn compile(
    src: &str,
    other_modules: &Modules,
    extra_uses: &[Use],
) -> Result<ModuleAndExpr, CompilationError> {
    if log::log_enabled!(log::Level::Debug) {
        log::debug!(
            "Using other modules: {}",
            other_modules.modules.keys().join(", ")
        );
        log::debug!("Input: {src}");
    }

    // Prepare a module with the extra uses.
    let mut module = new_module_using_std();
    module.uses.extend(extra_uses.iter().cloned());

    // Compile the code.
    // If debug logging is enabled, prepare an AST inspector that logs the ASTs.
    let output = if log::log_enabled!(log::Level::Debug) {
        let dbg_module = module.clone();
        let ast_inspector = |module_ast: &ast::PModule, expr_ast: &Option<ast::PExpr>| {
            let env = ModuleEnv::new(&dbg_module, other_modules, false);
            log::debug!("Module AST\n{}", module_ast.format_with(&env));
            if let Some(expr_ast) = expr_ast {
                log::debug!("Expr AST\n{}", expr_ast.format_with(&env));
            }
        };
        compile_to(src, module, other_modules, Some(&ast_inspector))
    } else {
        compile_to(src, module, other_modules, None)
    }?;

    // If debug logging is enabled, display the final IR, after linking and finalizing pending functions.
    if log::log_enabled!(log::Level::Debug) {
        if !output.module.is_empty() {
            let module: &Module = &output.module;
            log::debug!("Module IR\n{}", module.format_with(other_modules));
        }
        if let Some(expr) = output.expr.as_ref() {
            let env = ModuleEnv::new(&output.module, other_modules, false);
            log::debug!("Expr IR\n{}", expr.expr.format_with(&env));
        }
    }

    Ok(output)
}

pub type AstInspectorCb<'a> = &'a dyn Fn(&ast::PModule, &Option<ast::PExpr>);

/// Compile a source code, given some other Modules, and return the compiled module and an expression (if any), or an error.
/// Merge with existing module.
/// All spans are in byte offsets.
pub fn compile_to(
    src: &str,
    module: Module,
    other_modules: &Modules,
    ast_inspector: Option<AstInspectorCb<'_>>,
) -> Result<ModuleAndExpr, CompilationError> {
    // Parse the source code.
    let (module_ast, expr_ast) = parse_module_and_expr(src, false)
        .map_err(|error| compilation_error!(ParsingFailed(error)))?;
    if let Some(ast_inspector) = ast_inspector {
        ast_inspector(&module_ast, &expr_ast);
    }

    // Emit IR for the module.
    let mut module =
        emit_module(module_ast, other_modules, Some(&module), false).map_err(|error| {
            let env = ModuleEnv::new(&module, other_modules, false);
            CompilationError::resolve_types(error, &env, src)
        })?;
    module.source = Some(src.to_string());

    // Emit IR for the expression, if any.
    let mut expr = if let Some(expr_ast) = expr_ast {
        let compiled_expr =
            emit_expr(expr_ast, &mut module, other_modules, vec![]).map_err(|error| {
                let env = ModuleEnv::new(&module, other_modules, false);
                CompilationError::resolve_types(error, &env, src)
            })?;
        Some(compiled_expr)
    } else {
        None
    };

    // Finalize pending function values inside the module by attaching the module weak reference.
    let module = Rc::new(module);
    module::finalize_module_pending_functions(&module);
    if let Some(expr) = expr.as_mut() {
        expr.expr.finalize_pending_values(&module);
    }

    // Link the module.
    // This must be done after emitting the expression, as that may add new imports.
    other_modules.link(&module);

    Ok(ModuleAndExpr { module, expr })
}

/// Compile a source code, given some other Modules, and it to an existing module, or an error.
/// Allow unstable features as this is typically not user code.
pub fn add_code_to_module(
    code: &str,
    to: &mut Module,
    other_modules: &Modules,
    within_std: bool,
) -> Result<(), CompilationError> {
    // Parse the source code.
    let module_ast =
        parse_module(code, true).map_err(|error| compilation_error!(ParsingFailed(error)))?;
    assert_eq!(module_ast.errors(), &[]);
    {
        let env = ModuleEnv::new(to, other_modules, within_std);
        log::debug!("Added module AST\n{}", module_ast.format_with(&env));
    }

    // Emit IR for the module.
    let module = emit_module(module_ast, other_modules, Some(to), within_std).map_err(|error| {
        let env = ModuleEnv::new(to, other_modules, within_std);
        CompilationError::resolve_types(error, &env, code)
    })?;

    // Swap the new module with the old one.
    *to = module;
    Ok(())
}
