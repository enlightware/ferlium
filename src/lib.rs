// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

pub use rustc_hash::{FxHashMap, FxHashSet};

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
    ast::PExprArena,
    containers::b,
    emit_ir::EmitModuleFrom,
    format::FormatWith,
    module::{Module, ModuleFunction, ModuleId, Uses, id::Id},
    std::STD_MODULE_ID,
    r#type::Type,
};

lalrpop_mod!(
    #[allow(clippy::ptr_arg,clippy::type_complexity)]
    #[rustfmt::skip]
    parser
);

/// Call a compiled function after validating its type signature, for any arity.
/// - Session: `session` — a `CompilerSession` containing the module to call the function from.
/// - Module: `module_id` — the id of the module to call the function from
/// - Function name: `name` — the name of the function to call, as a string literal.
/// - Fn arguments: `[val1 => ty1, val2 => ty2, ...]` — each `val` is a `Value` and each `ty` is a `Type`.
/// - Fn return: `-> ret_ty` — a `Type` expression.
///
/// Returns `Result<Value, String>`.
#[macro_export]
macro_rules! call_fn {
    (
        $session:expr, $module_id:expr, $name:expr,
        [ $( $val:expr => $ty:expr ),* $(,)? ]
        -> $ret_ty:expr
    ) => {{
        use $crate::format::FormatWith;
        let __session = $session;
        let __module_id = $module_id;
        let ret_ty = $ret_ty;
        __session.run_fn(__module_id, $name, move |func, current, others| {
            let expected_args = vec![
                $( $crate::r#type::FnArgType::new_by_val($ty) ),*
            ];
            if !func.definition.ty_scheme.is_just_type_and_effects()
                || func.definition.ty_scheme.ty.args != expected_args
                || func.definition.ty_scheme.ty.ret != ret_ty
            {
                let module_env = $crate::module::ModuleEnv::new(current, others);
                let args_fmt = expected_args
                    .iter()
                    .map(|a| a.ty.format_with(&module_env).to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                let ret_fmt = ret_ty.format_with(&module_env).to_string();
                Err(format!(
                    "Function {} does not have type \"({}) -> {}\", it has \"{}\" instead",
                    $name,
                    args_fmt,
                    ret_fmt,
                    func.definition.ty_scheme.display_rust_style(&module_env),
                ))
            } else {
                let mut ctx = $crate::eval::EvalCtx::new(__module_id, __session);
                let args_vec = vec![ $( $crate::eval::ValOrMut::Val($val) ),* ];
                let ret = func
                    .code
                    .call(args_vec, &mut ctx, &func.locals)
                    .map_err(|err| format!("Execution error: {}", err.kind()))?
                    .into_value();
                Ok(ret)
            }
        })
    }};
}

/// Run a compiled function with native Rust values, for any arity.
///
/// A thin wrapper over [`call_fn!`] that converts native Rust values via `Value::native` and
/// Rust types via `Type::primitive`, then extracts the return value back to a native type.
///
/// # Variants
///
/// **Unit return** (returns `Result<(), String>`):
/// ```ignore
/// run_fn_native!(session, module_id, "name", [val1 => I1, val2 => I2, ...])
/// ```
///
/// **Primitive return** (returns `Result<O, String>`):
/// ```ignore
/// run_fn_native!(session, module_id, "name", [val1 => I1, val2 => I2, ...] -> O)
/// ```
#[macro_export]
macro_rules! run_fn_native {
    // Unit return
    ( $session:expr, $module_id:expr, $name:expr, [ $( $val:expr => $ty:ty ),* $(,)? ] ) => {
        $crate::call_fn!(
            $session, $module_id, $name,
            [ $( $crate::value::Value::native($val.clone()) => $crate::r#type::Type::primitive::<$ty>() ),* ]
            -> $crate::r#type::Type::unit()
        ).map(|_| ())
    };
    // Primitive return
    ( $session:expr, $module_id:expr, $name:expr, [ $( $val:expr => $ty:ty ),* $(,)? ] -> $ret:ty ) => {
        $crate::call_fn!(
            $session, $module_id, $name,
            [ $( $crate::value::Value::native($val.clone()) => $crate::r#type::Type::primitive::<$ty>() ),* ]
            -> $crate::r#type::Type::primitive::<$ret>()
        ).map(|ret| ret.into_primitive_ty::<$ret>().unwrap())
    };
}

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

pub type AstInspectorCb<'a> =
    &'a dyn Fn(&ast::PModule, Option<ast::PExprId>, &ast::PExprArena, &Modules);

static FIRST_USER_MODULE_ID: ModuleId = ModuleId(2);

/// A compilation session, that contains a source table and the standard library.
#[derive(Debug)]
pub struct CompilerSession {
    /// Source table for this compilation session.
    source_table: SourceTable,
    /// All compiled modules
    modules: Modules,
    /// Pre-created empty module just using the standard library, for debugging purposes.
    empty_std_user: ModuleId,
    /// Initial size of the source table, for reset().
    initial_source_table_size: usize,
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
        assert_eq!(modules.next_id(), FIRST_USER_MODULE_ID);
        let initial_source_table_size = source_table.len();
        Self {
            source_table,
            modules,
            empty_std_user,
            initial_source_table_size,
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

    /// Reset the compiler session to its initial state, without rebuilding std.
    pub fn reset(&mut self) {
        // We only keep std and $empty_std_user and drop the rest.
        self.modules.truncate(FIRST_USER_MODULE_ID.as_index());
        self.source_table.truncate(self.initial_source_table_size);
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
        let mut arena = new_ast_arena_sized_from_source(src);
        let source_id = self
            .source_table
            .add_source(name.to_string(), src.to_string());
        let ty = parser::DefinedTypeParser::new()
            .parse(source_id, &mut errors, &mut arena, src)
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
        let mut modules_used = FxHashSet::default();
        ast.desugar(span, false, &env, &mut modules_used)
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
        let mut arena = new_ast_arena_sized_from_source(src);
        let source_id = self
            .source_table
            .add_source(name.to_string(), src.to_string());
        let ty = parser::HoledTypeParser::new()
            .parse(source_id, &mut errors, &mut arena, src)
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
        let mut modules_used = FxHashSet::default();
        ast.desugar(span, false, &env, &mut modules_used)
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

        // Compile the code.
        // If debug logging is enabled, prepare an AST inspector that logs the ASTs.
        let uses = Uses::new_with_std();
        let output = if log::log_enabled!(log::Level::Debug) {
            let dbg_module = new_module_using_std(self.modules.next_id());
            let ast_inspector = |module_ast: &ast::PModule,
                                 expr_ast: Option<ast::PExprId>,
                                 arena: &ast::PExprArena,
                                 modules: &Modules| {
                let env = ModuleEnv::new(&dbg_module, modules);
                let ast = ast::ModuleDisplay::new(module_ast, arena);
                log::debug!("Module AST\n{}", ast.format_with(&env));
                if let Some(expr_ast) = expr_ast {
                    let ast = ast::ExprDisplay::new(expr_ast, arena);
                    log::debug!("Expr AST\n{}", ast.format_with(&env));
                }
            };
            self.compile_to(
                src_code,
                source_name,
                module_path,
                uses,
                Some(&ast_inspector),
            )
        } else {
            self.compile_to(src_code, source_name, module_path, uses, None)
        }?;

        // If debug logging is enabled, display the final IR, after linking and finalizing pending functions.
        if log::log_enabled!(log::Level::Debug) {
            let module = self.modules.get(output.module_id).unwrap();
            if !module.is_empty() {
                log::debug!("Module IR\n{}", module.format_with(&self.modules));
            }
            if let Some(expr) = output.expr.as_ref() {
                let env = ModuleEnv::new(module, &self.modules);
                log::debug!(
                    "Expr IR\n{}",
                    ir::ExprDisplay::new(expr.expr, &expr.locals).format_with(&env)
                );
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
        uses: Uses,
        ast_inspector: Option<AstInspectorCb<'_>>,
    ) -> Result<ModuleAndExpr, CompilationError> {
        // Parse the source code.
        let source_id = self
            .source_table
            .add_source(source_name.to_string(), src_code.to_string());
        let (module_ast, expr_ast, arena) = parse_module_and_expr(src_code, source_id, false)
            .map_err(|error| compilation_error!(ParsingFailed(error)))?;
        if let Some(ast_inspector) = ast_inspector {
            ast_inspector(&module_ast, expr_ast, &arena, &self.modules);
        }

        // Get the old module of the same name, replacing it with a dummy for the duration of the compilation.
        let (module_id, old_module) = self
            .modules
            .replace(module_path.clone(), Module::new(self.modules.next_id()));

        // Emit IR for the module.
        let emit_from = EmitModuleFrom::Uses(uses);
        let mut module = emit_module(module_ast, &arena, module_id, &self.modules, emit_from)
            .map_err(|error| {
                // Restore the old module in case of error, to avoid leaving the session in a broken state.
                // Note: the clone on old_module is due to a limitation of the borrow checker not realizing this function
                // is only called when the parent function is exited with the ? below.
                old_module
                    .clone()
                    .map(|old_module| self.modules.replace(module_path.clone(), old_module));
                // Resolve types in the error, to provide better error messages.
                let module = new_module_using_std(module_id);
                let env = ModuleEnv::new(&module, &self.modules);
                CompilationError::resolve_types(error, &env, &self.source_table)
            })?;

        // Emit IR for the expression, if any.
        let expr = if let Some(expr_ast) = expr_ast {
            let compiled_expr = emit_expr(expr_ast, &arena, &mut module, &self.modules, vec![])
                .map_err(|error| {
                    // Restore the old module in case of error, to avoid leaving the session in a broken state.
                    old_module
                        .clone()
                        .map(|old_module| self.modules.replace(module_path.clone(), old_module));
                    // Resolve types in the error, to provide better error messages.
                    let env = ModuleEnv::new(&module, &self.modules);
                    CompilationError::resolve_types(error, &env, &self.source_table)
                })?;
            Some(compiled_expr)
        } else {
            None
        };

        // Detect circular imports and emit error in that case.
        struct ModuleNode(Vec<ModuleId>);
        impl graph::Node for ModuleNode {
            type Index = ModuleId;
            fn neighbors(&self) -> impl Iterator<Item = ModuleId> {
                self.0.iter().copied()
            }
        }
        // Note: `module_id`'s slot in `self.modules` still holds the temporary dummy module
        // inserted at the start of `compile_to`. We must use the freshly-compiled `module`
        // for that slot so its real dependencies are visible to the cycle detector.
        let module_graph: Vec<_> = self
            .modules
            .iter_ids()
            .map(|id| {
                let deps = if id == module_id {
                    module.deps().collect()
                } else {
                    self.modules.get(id).unwrap().deps().collect()
                };
                ModuleNode(deps)
            })
            .collect();
        if let Some(cycle) = graph::find_cycle_from(&module_graph, module_id.as_index()) {
            // Restore the old module in case of error, to avoid leaving the session in a broken state.
            old_module.map(|old_module| self.modules.replace(module_path.clone(), old_module));
            return Err(compilation_error!(CircularImportDependency {
                origin: self.modules.get_name(module_id).unwrap().to_string(),
                import_chain: cycle
                    .into_iter()
                    .map(|index| self
                        .modules
                        .get_name(ModuleId::from_index(index))
                        .unwrap()
                        .to_string())
                    .collect(),
                span: Location::new_synthesized(),
            }));
        }

        // Store the module.
        self.modules.replace(module_path, module);

        Ok(ModuleAndExpr { module_id, expr })
    }

    /// Run a function from a module, given its path and name, through a user-provided runner.
    pub fn run_fn<R>(
        &self,
        module_id: ModuleId,
        name: &str,
        runner: impl FnOnce(&ModuleFunction, &Module, &Modules) -> Result<R, String>,
    ) -> Result<R, String> {
        let module = self
            .modules()
            .get(module_id)
            .ok_or_else(|| format!("Module {module_id} not found"))?;
        match module.lookup_function(name, &self.modules) {
            Ok(Some(func)) => runner(func, module, &self.modules),
            Ok(None) => Err(format!("Function {name} not found in module {module_id}")),
            Err(e) => Err(format!("Lookup error for function {name}: {e:?}")),
        }
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
) -> Result<(ast::PModule, ast::PExprArena), Vec<LocatedError>> {
    let mut errors = Vec::new();
    let mut arena = new_ast_arena_sized_from_source(src);
    let module = parser::ModuleParser::new()
        .parse(source_id, &mut errors, &mut arena, src)
        .map_err(|error| vec![describe_parse_error(error, source_id)])?;
    describe_recovered_errors(errors, source_id)?;
    // TODO: change the last line to an unwrap once the grammar is fully error-tolerant.
    if !accept_unstable {
        validate_no_unstable(&module, [].iter(), &arena)?;
    }
    Ok((module, arena))
}

/// Parse a module and an expression (if any) from a source code and return the corresponding ASTs.
pub fn parse_module_and_expr(
    src: &str,
    source_id: SourceId,
    accept_unstable: bool,
) -> Result<(ast::PModule, Option<ast::PExprId>, ast::PExprArena), Vec<LocatedError>> {
    let mut errors = Vec::new();
    let mut arena = new_ast_arena_sized_from_source(src);
    let module_and_expr = parser::ModuleAndBlockContentParser::new()
        .parse(source_id, &mut errors, &mut arena, src)
        .map_err(|error| vec![describe_parse_error(error, source_id)])?;
    describe_recovered_errors(errors, source_id)?;
    // TODO: revisit once the grammar is fully error-tolerant.
    if !accept_unstable {
        validate_no_unstable(&module_and_expr.0, module_and_expr.1.iter(), &arena)?;
    }
    Ok((module_and_expr.0, module_and_expr.1, arena))
}

/// Compile a source code, given some other Modules, and it to an existing module, or an error.
/// Allow unstable features as this is typically not user code.
pub(crate) fn add_code_to_module(
    source_name: &str,
    code: &str,
    to: Module,
    module_id: ModuleId,
    other_modules: &Modules,
    source_table: &mut SourceTable,
) -> Result<Module, CompilationError> {
    // Parse the source code.
    let source_id = source_table.add_source(source_name.to_string(), code.to_string());
    let (module_ast, arena) = parse_module(code, source_id, true)
        .map_err(|error| compilation_error!(ParsingFailed(error)))?;
    assert_eq!(module_ast.errors(&arena), &[]);
    {
        let env = ModuleEnv::new(&to, other_modules);
        log::debug!(
            "Added module AST\n{}",
            ast::ModuleDisplay::new(&module_ast, &arena).format_with(&env)
        );
    }

    // Emit IR for the module.
    let prev_to = to.clone();
    let emit_from = EmitModuleFrom::Existing(b(to));
    let module =
        emit_module(module_ast, &arena, module_id, other_modules, emit_from).map_err(|error| {
            let env = ModuleEnv::new(&prev_to, other_modules);
            CompilationError::resolve_types(error, &env, source_table)
        })?;

    Ok(module)
}

/// Create a new arena for src, estimating the number of nodes needed and pre-allocating the memory.
fn new_ast_arena_sized_from_source(src: &str) -> PExprArena {
    let estimated_node_count = src.len() / 8;
    ast::ExprArena::with_capacity(estimated_node_count)
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
    exprs: impl Iterator<Item = &'a ast::ExprId<ast::Parsed>>,
    arena: &ast::PExprArena,
) -> Result<(), Vec<LocatedError>> {
    let mut unstables = module.visit_with(UnstableCollector::default(), arena);
    for expr in exprs {
        unstables = arena[*expr].visit_with(unstables, arena);
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
