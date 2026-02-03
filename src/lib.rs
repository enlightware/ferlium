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
use lalrpop_util::{ErrorRecovery, lalrpop_mod};
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
mod import_resolver;
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
pub use location::{Location, SourceId, SourceTable};
pub use type_inference::SubOrSameType;

use type_scheme::DisplayStyle;
pub use ustr::{Ustr, ustr};

use crate::{
    format::FormatWith,
    module::{Module, ModuleRc, Modules},
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

pub type AstInspectorCb<'a> = &'a dyn Fn(&ast::PModule, &Option<ast::PExpr>);

/// A compilation session, that contains a source table and the standard library.
#[derive(Debug)]
pub struct CompilerSession {
    /// Source table for this compilation session.
    source_table: SourceTable,
    /// Pre-created standard library module.
    std_module: ModuleRc,
    /// Pre-created set of modules including only the standard library.
    std_modules: Modules,
    /// Pre-created empty module just using the standard library, for debugging purposes.
    empty_std_user: Module,
}

impl CompilerSession {
    /// Create a new compilation session with an empty source table and the standard library loaded.
    pub fn new() -> Self {
        let mut source_table = SourceTable::default();
        let std_module = std::std_module(&mut source_table);
        let mut std_modules: Modules = Default::default();
        std_modules
            .modules
            .insert(module::Path::single_str("std"), std_module.clone());
        let empty_std_user = new_module_using_std();
        Self {
            source_table,
            std_module,
            std_modules,
            empty_std_user,
        }
    }

    /// Get the source table for this compilation session.
    pub fn source_table(&self) -> &SourceTable {
        &self.source_table
    }

    /// Get a module environment, with an empty module including the standard library
    /// for debugging purposes.
    pub fn std_module_env(&self) -> ModuleEnv<'_> {
        ModuleEnv {
            others: &self.std_modules,
            current: &self.empty_std_user,
            within_std: false,
        }
    }

    /// Get the standard library module.
    pub fn std_module(&self) -> &ModuleRc {
        &self.std_module
    }

    /// Get the standard library as a set of modules.
    pub fn std_modules(&self) -> &Modules {
        &self.std_modules
    }

    /// Create a new set of modules including the standard library.
    pub fn new_std_modules(&self) -> Modules {
        self.std_modules.clone()
    }

    /// Parse a type from a source code and return the corresponding fully-defined Type.
    pub fn parse_defined_type(
        &mut self,
        name: &str,
        src: &str,
    ) -> Result<(ast::PType, SourceId), LocatedError> {
        let mut errors = Vec::new();
        let source_id = self
            .source_table
            .add_source(name.to_string(), src.to_string());
        let ty = parser::DefinedTypeParser::new()
            .parse(source_id, &mut errors, src)
            .map_err(|e| describe_parse_error(e, source_id))?;
        Ok((ty, source_id))
    }

    /// Resolve a fully-defined type from a source code and return the corresponding Type.
    pub fn resolve_defined_type_with_std(
        &mut self,
        name: &str,
        src: &str,
    ) -> Result<Type, CompilationError> {
        let (ast, source_id) = self
            .parse_defined_type(name, src)
            .map_err(|error| compilation_error!(ParsingFailed(vec![error])))?;
        let span = Location::new_usize(0, src.len(), source_id);
        let env = self.std_module_env();
        ast.desugar(span, false, &env)
            .map_err(|error| CompilationError::resolve_types(error, &env, &self.source_table))
    }

    /// Parse a type from a source code and return the corresponding Type,
    /// with placeholder filled with first generic variable.
    pub fn parse_holed_type(
        &mut self,
        name: &str,
        src: &str,
    ) -> Result<(ast::PType, SourceId), LocatedError> {
        let mut errors = Vec::new();
        let source_id = self
            .source_table
            .add_source(name.to_string(), src.to_string());
        let ty = parser::HoledTypeParser::new()
            .parse(source_id, &mut errors, src)
            .map_err(|e| describe_parse_error(e, source_id))?;
        Ok((ty, source_id))
    }

    /// Resolve a generic type from a source code and return the corresponding Type,
    /// with placeholder filled with first generic variable.
    pub fn resolve_holed_type_with_std(
        &mut self,
        name: &str,
        src: &str,
    ) -> Result<Type, CompilationError> {
        let (ast, source_id) = self
            .parse_holed_type(name, src)
            .map_err(|error| compilation_error!(ParsingFailed(vec![error])))?;
        let span = Location::new_usize(0, src.len(), source_id);
        let env = self.std_module_env();
        ast.desugar(span, false, &env)
            .map_err(|error| CompilationError::resolve_types(error, &env, &self.source_table))
    }

    /// Compile a source code, given some other Modules, and return the compiled module and an expression (if any), or an error.
    /// All spans are in byte offsets.
    pub fn compile(
        &mut self,
        source_name: &str,
        src: &str,
        other_modules: &Modules,
    ) -> Result<ModuleAndExpr, CompilationError> {
        if log::log_enabled!(log::Level::Debug) {
            log::debug!(
                "Using other modules: {}",
                other_modules.modules.keys().join(", ")
            );
            log::debug!("Input: {src}");
        }

        // Prepare a module with the extra uses.
        let module = new_module_using_std();

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
            self.compile_to(
                source_name,
                src,
                module,
                other_modules,
                Some(&ast_inspector),
            )
        } else {
            self.compile_to(source_name, src, module, other_modules, None)
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

    /// Compile a source code, given some other Modules, and return the compiled module and an expression (if any), or an error.
    /// Merge with existing module.
    /// All spans are in byte offsets.
    pub fn compile_to(
        &mut self,
        source_name: &str,
        src: &str,
        module: Module,
        other_modules: &Modules,
        ast_inspector: Option<AstInspectorCb<'_>>,
    ) -> Result<ModuleAndExpr, CompilationError> {
        // Parse the source code.
        let source_id = self
            .source_table
            .add_source(source_name.to_string(), src.to_string());
        let (module_ast, expr_ast) = parse_module_and_expr(src, source_id, false)
            .map_err(|error| compilation_error!(ParsingFailed(error)))?;
        if let Some(ast_inspector) = ast_inspector {
            ast_inspector(&module_ast, &expr_ast);
        }

        // Emit IR for the module.
        let mut module =
            emit_module(module_ast, other_modules, Some(&module), false).map_err(|error| {
                let env = ModuleEnv::new(&module, other_modules, false);
                CompilationError::resolve_types(error, &env, &self.source_table)
            })?;
        module.source = Some(src.to_string());

        // Emit IR for the expression, if any.
        let mut expr = if let Some(expr_ast) = expr_ast {
            let compiled_expr =
                emit_expr(expr_ast, &mut module, other_modules, vec![]).map_err(|error| {
                    let env = ModuleEnv::new(&module, other_modules, false);
                    CompilationError::resolve_types(error, &env, &self.source_table)
                })?;
            Some(compiled_expr)
        } else {
            None
        };

        // Finalize the module and the expression.
        let module = Rc::new(module);
        module::finalize_module(&module);
        if let Some(expr) = expr.as_mut() {
            expr.expr.finalize_pending_values(&module);
        }

        // Link the module.
        // This must be done after emitting the expression, as that may add new imports.
        other_modules.link(&module);

        Ok(ModuleAndExpr { module, expr })
    }
}

impl Default for CompilerSession {
    fn default() -> Self {
        CompilerSession::new()
    }
}

/// Parse a module from a source code and return the corresponding ASTs.
fn parse_module(
    src: &str,
    source_id: SourceId,
    accept_unstable: bool,
) -> Result<ast::PModule, Vec<LocatedError>> {
    let mut errors = Vec::new();
    let module = parser::ModuleParser::new()
        .parse(source_id, &mut errors, src)
        .map_err(|error| vec![describe_parse_error(error, source_id)])?;
    describe_recovered_errors(errors, source_id)?;
    // TODO: change the last line to an unwrap once the grammar is fully error-tolerant.
    if !accept_unstable {
        validate_no_unstable(&module, [].iter())?;
    }
    Ok(module)
}

/// Parse a module and an expression (if any) from a source code and return the corresponding ASTs.
fn parse_module_and_expr(
    src: &str,
    source_id: SourceId,
    accept_unstable: bool,
) -> Result<(ast::PModule, Option<ast::PExpr>), Vec<LocatedError>> {
    let mut errors = Vec::new();
    let module_and_expr = parser::ModuleAndBlockContentParser::new()
        .parse(source_id, &mut errors, src)
        .map_err(|error| vec![describe_parse_error(error, source_id)])?;
    describe_recovered_errors(errors, source_id)?;
    // TODO: revisit once the grammar is fully error-tolerant.
    if !accept_unstable {
        validate_no_unstable(&module_and_expr.0, module_and_expr.1.iter())?;
    }
    Ok((module_and_expr.0, module_and_expr.1))
}

/// Compile a source code, given some other Modules, and it to an existing module, or an error.
/// Allow unstable features as this is typically not user code.
pub(crate) fn add_code_to_module(
    source_name: &str,
    code: &str,
    to: &mut Module,
    other_modules: &Modules,
    source_table: &mut SourceTable,
    within_std: bool,
) -> Result<SourceId, CompilationError> {
    // Parse the source code.
    let source_id = source_table.add_source(source_name.to_string(), code.to_string());
    let module_ast = parse_module(code, source_id, true)
        .map_err(|error| compilation_error!(ParsingFailed(error)))?;
    assert_eq!(module_ast.errors(), &[]);
    {
        let env = ModuleEnv::new(to, other_modules, within_std);
        log::debug!("Added module AST\n{}", module_ast.format_with(&env));
    }

    // Emit IR for the module.
    let module = emit_module(module_ast, other_modules, Some(to), within_std).map_err(|error| {
        let env = ModuleEnv::new(to, other_modules, within_std);
        CompilationError::resolve_types(error, &env, source_table)
    })?;

    // Swap the new module with the old one.
    *to = module;
    Ok(source_id)
}

/// Transform parse error into LocatedError.
fn describe_recovered_errors(
    errors: Vec<ErrorRecovery<usize, crate::parser::Token<'_>, LocatedError>>,
    source_id: SourceId,
) -> Result<(), Vec<LocatedError>> {
    if !errors.is_empty() {
        let errors = errors
            .into_iter()
            .map(|error| describe_parse_error(error.error, source_id))
            .collect();
        Err(errors)
    } else {
        Ok(())
    }
}

/// Validate that a module and some expressions do not use unstable features.
fn validate_no_unstable<'a>(
    module: &ast::PModule,
    exprs: impl Iterator<Item = &'a ast::PExpr>,
) -> Result<(), Vec<LocatedError>> {
    let mut unstables = module.visit_with(UnstableCollector::default());
    for expr in exprs {
        unstables = expr.visit_with(unstables);
    }
    if unstables.0.is_empty() {
        Ok(())
    } else {
        Err(unstables
            .0
            .into_iter()
            .map(|span| ("Unstable feature not allowed".into(), span))
            .collect())
    }
}
