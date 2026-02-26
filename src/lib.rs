// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

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
pub use module::{Modules, Path};
pub use type_inference::SubOrSameType;

use type_scheme::DisplayStyle;
pub use ustr::{Ustr, ustr};

use crate::{
    format::FormatWith,
    module::{Module, ModuleId},
    std::STD_MODULE_ID,
    r#type::Type,
};

lalrpop_mod!(
    #[allow(clippy::ptr_arg,clippy::type_complexity)]
    #[rustfmt::skip]
    parser
);

/// A compiled module and an expression (if any).
#[derive(Debug)]
pub struct ModuleAndExpr {
    pub module_id: ModuleId,
    pub expr: Option<CompiledExpr>,
}
impl ModuleAndExpr {
    pub fn new_just_module(module: ModuleId) -> Self {
        Self {
            module_id: module,
            expr: None,
        }
    }
}

pub type AstInspectorCb<'a> = &'a dyn Fn(&ast::PModule, &Option<ast::PExpr>, &Modules);

/// A compilation session, that contains a source table and the standard library.
#[derive(Debug)]
pub struct CompilerSession {
    /// Source table for this compilation session.
    source_table: SourceTable,
    /// All compiled modules
    modules: Modules,
    /// Pre-created empty module just using the standard library, for debugging purposes.
    empty_std_user: ModuleId,
}

impl CompilerSession {
    /// Create a new compilation session with an empty source table and the standard library loaded.
    pub fn new() -> Self {
        let mut source_table = SourceTable::default();
        let mut modules = Modules::default();
        assert_eq!(modules.next_id(), STD_MODULE_ID);
        let std_module = std::std_module(&mut source_table);
        let std_name = module::Path::single_str("std");
        modules.insert(std_name, std_module);
        let empty_std_user = new_module_using_std(modules.next_id());
        let empty_std_user =
            modules.insert(module::Path::single_str("$empty_std_user"), empty_std_user);
        Self {
            source_table,
            modules,
            empty_std_user,
        }
    }

    /// Get the source table for this compilation session.
    pub fn source_table(&self) -> &SourceTable {
        &self.source_table
    }

    /// Get all compiled modules for this compilation session.
    pub fn modules(&self) -> &Modules {
        &self.modules
    }

    /// Get a module by its ID, if it exists.
    pub fn get_module_by_id(&self, id: ModuleId) -> Option<&Module> {
        self.modules.get(id)
    }

    /// Get a module by its path, if it exists.
    pub fn get_module_by_path(&self, path: &module::Path) -> Option<&Module> {
        self.modules.get_by_name(path).map(|(_, module)| module)
    }

    /// Get a module environment, with an empty module including the standard library
    /// for debugging purposes.
    pub fn module_env(&self) -> ModuleEnv<'_> {
        ModuleEnv {
            modules: &self.modules,
            current: self.modules.get(self.empty_std_user).unwrap(),
        }
    }

    /// Get the standard library module.
    pub fn std_module(&self) -> &Module {
        self.modules.get(STD_MODULE_ID).unwrap()
    }

    /// Register a module in this compilation session and return its id.
    pub fn register_module(&mut self, path: module::Path, module: Module) -> ModuleId {
        let module_id = self.modules.insert(path, module);
        log::debug!("Registered module with id {module_id}");
        module_id
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
        let env = self.module_env();
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
        let env = self.module_env();
        ast.desugar(span, false, &env)
            .map_err(|error| CompilationError::resolve_types(error, &env, &self.source_table))
    }

    /// Compile a source code and return the compiled module and an expression (if any), or an error.
    /// All spans are in byte offsets.
    pub fn compile(
        &mut self,
        src_code: &str,
        source_name: &str,
        module_path: Path,
    ) -> Result<ModuleAndExpr, CompilationError> {
        if log::log_enabled!(log::Level::Debug) {
            log::debug!(
                "Using other modules: {}",
                self.modules.iter_names().join(", ")
            );
            log::debug!("Input: {src_code}");
        }

        // Prepare a module with the extra uses.
        let module = new_module_using_std(self.modules.next_id());

        // Compile the code.
        // If debug logging is enabled, prepare an AST inspector that logs the ASTs.
        let output = if log::log_enabled!(log::Level::Debug) {
            let dbg_module = module.clone();
            let ast_inspector =
                |module_ast: &ast::PModule, expr_ast: &Option<ast::PExpr>, modules: &Modules| {
                    let env = ModuleEnv::new(&dbg_module, modules);
                    log::debug!("Module AST\n{}", module_ast.format_with(&env));
                    if let Some(expr_ast) = expr_ast {
                        log::debug!("Expr AST\n{}", expr_ast.format_with(&env));
                    }
                };
            self.compile_to(
                src_code,
                source_name,
                module_path,
                module,
                Some(&ast_inspector),
            )
        } else {
            self.compile_to(src_code, source_name, module_path, module, None)
        }?;

        // If debug logging is enabled, display the final IR, after linking and finalizing pending functions.
        if log::log_enabled!(log::Level::Debug) {
            let module = self.modules.get(output.module_id).unwrap();
            if !module.is_empty() {
                log::debug!("Module IR\n{}", module.format_with(&self.modules));
            }
            if let Some(expr) = output.expr.as_ref() {
                let env = ModuleEnv::new(module, &self.modules);
                log::debug!("Expr IR\n{}", expr.expr.format_with(&env));
            }
        }

        Ok(output)
    }

    /// Compile a source code and return the compiled module and an expression (if any), or an error.
    /// Merge with existing module.
    /// All spans are in byte offsets.
    pub fn compile_to(
        &mut self,
        src_code: &str,
        source_name: &str,
        module_path: Path,
        module: Module,
        ast_inspector: Option<AstInspectorCb<'_>>,
    ) -> Result<ModuleAndExpr, CompilationError> {
        // Parse the source code.
        let source_id = self
            .source_table
            .add_source(source_name.to_string(), src_code.to_string());
        let (module_ast, expr_ast) = parse_module_and_expr(src_code, source_id, false)
            .map_err(|error| compilation_error!(ParsingFailed(error)))?;
        if let Some(ast_inspector) = ast_inspector {
            ast_inspector(&module_ast, &expr_ast, &self.modules);
        }

        // FIXME: this always associates a ModuleId, even if the module was not there yet and the compilation fails.
        // We might not want this behavior.

        // Get the old module of the same name, replacing it with a dummy for the duration of the compilation.
        let (module_id, old_module) = self
            .modules
            .replace(module_path.clone(), Module::new(self.modules.next_id()));

        // Emit IR for the module.
        let mut module =
            emit_module(module_ast, module_id, &self.modules, Some(&module)).map_err(|error| {
                // Restore the old module in case of error, to avoid leaving the session in a broken state.
                // Note: the clone on old_module is due to a limitation of the borrow checker not realizing this function
                // is only called when the parent function is exited with the ? below.
                old_module
                    .clone()
                    .map(|old_module| self.modules.replace(module_path.clone(), old_module));
                // Resolve types in the error, to provide better error messages.
                let env = ModuleEnv::new(&module, &self.modules);
                CompilationError::resolve_types(error, &env, &self.source_table)
            })?;

        // Emit IR for the expression, if any.
        let expr = if let Some(expr_ast) = expr_ast {
            let compiled_expr =
                emit_expr(expr_ast, &mut module, &self.modules, vec![]).map_err(|error| {
                    // Restore the old module in case of error, to avoid leaving the session in a broken state.
                    old_module
                        .map(|old_module| self.modules.replace(module_path.clone(), old_module));
                    // Resolve types in the error, to provide better error messages.
                    let env = ModuleEnv::new(&module, &self.modules);
                    CompilationError::resolve_types(error, &env, &self.source_table)
                })?;
            Some(compiled_expr)
        } else {
            None
        };

        // Store the module.
        self.modules.replace(module_path, module);

        Ok(ModuleAndExpr { module_id, expr })
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
    module_id: ModuleId,
    other_modules: &Modules,
    source_table: &mut SourceTable,
) -> Result<SourceId, CompilationError> {
    // Parse the source code.
    let source_id = source_table.add_source(source_name.to_string(), code.to_string());
    let module_ast = parse_module(code, source_id, true)
        .map_err(|error| compilation_error!(ParsingFailed(error)))?;
    assert_eq!(module_ast.errors(), &[]);
    {
        let env = ModuleEnv::new(to, other_modules);
        log::debug!("Added module AST\n{}", module_ast.format_with(&env));
    }

    // Emit IR for the module.
    let module = emit_module(module_ast, module_id, other_modules, Some(to)).map_err(|error| {
        let env = ModuleEnv::new(to, other_modules);
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
